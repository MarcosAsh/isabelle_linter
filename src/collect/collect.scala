/* The linter_collect tool: for every `by` step of a session, the features of its goal and which
   methods close it how fast, as JSON lines for studying which method to try. */

package isabelle.isabelle_linter

import isabelle._


object Collect {
  /* A `by` step and the methods tried on it: its own first, then faster_step's. */
  sealed case class Item(lemma: Lemma, step: Step) {
    val methods: List[String] = (step.methods :: Faster_Step.candidates(step)).distinct

    def key(what: String): String = lemma.key + ":" + step.cmd.offset + ":" + what

    def question(function: String, what: String, args: List[String], timeout: Time): Pide.Question =
      Pide.Question(key(what), lemma.theory, step.goal.command, function, args, timeout)

    def tried(answers: Pide.Answers, method: String): Pide.Answer = answers(key("try:" + method))

    def closing(answers: Pide.Answers): List[String] = methods.filter(method => tried(answers, method).closes)
  }


  /* questions */

  /* The goal, and every method with the same limit; these may run in parallel. */
  def tries(item: Item, timeout: Time): List[Pide.Question] =
    item.question("linter_goal", "goal", Nil, timeout) ::
      item.methods.map(method => item.question("linter_try", "try:" + method, List(method), timeout))

  /* The methods that closed, re-timed one after another. */
  def timing(item: Item, answers: Pide.Answers, runs: Int, timeout: Time): List[Pide.Question] =
    item.closing(answers) match {
      case Nil => Nil
      case closing => List(item.question("linter_times", "times", runs.toString :: closing, timeout))
    }

  def sledgehammer(item: Item, timeout: Time): Pide.Question =
    item.question("linter_sledgehammer", "sledgehammer", List(""), timeout)

  /* Ask in chunks of a few steps, so that the timed runs barely compete. */
  def ask_in_chunks(checked: Pide.Checked, questions: List[List[Pide.Question]], size: Int,
      progress: Progress): Pide.Answers = {
    var answers: Pide.Answers = Map.empty
    for (chunk <- questions.grouped(size); chunk_questions = chunk.flatten if chunk_questions.nonEmpty) {
      answers ++= Pide.ask(checked.session, chunk_questions, progress)
    }
    answers
  }

  def ask_batch(checked: Pide.Checked, batch: List[Item], options: Options, progress: Progress): Pide.Answers = {
    val timeout = Time.seconds(options.real("collect_timeout"))
    val runs = options.int("collect_runs")
    val parallel = options.int("collect_parallel")

    val answers = Pide.ask(checked.session, batch.flatMap(tries(_, timeout)), progress)
    val times = ask_in_chunks(checked, batch.map(timing(_, answers, runs, timeout)), parallel, progress)

    val sledgehammer_timeout = Time.seconds(options.real("collect_sledgehammer"))
    val proofs =
      if (!checked.hol || sledgehammer_timeout.is_zero) Map.empty
      else ask_in_chunks(checked, batch.map(item => List(sledgehammer(item, sledgehammer_timeout))), parallel, progress)

    answers ++ times ++ proofs
  }


  /* records */

  /* Numbers go into the JSON as numbers. */
  def value(s: String): Any = Value.Long.unapply(s).getOrElse(s)

  /* The result message also carries its position, which is no feature of the goal. */
  val not_features: Set[String] =
    Set(Markup.INSTANCE, "verdict", Markup.SERIAL, Markup.ID, Markup.LABEL, Markup.OFFSET, Markup.END_OFFSET,
      Markup.FILE)

  def goal(answer: Pide.Answer): JSON.Object.T =
    answer.props.collect({ case (name, text) if !not_features(name) => name -> value(text) }).toMap

  def tries_json(item: Item, answers: Pide.Answers): List[JSON.Object.T] = {
    val times = answers.get(item.key("times"))
    val closing = item.closing(answers)
    for (method <- item.methods) yield {
      val tried = item.tried(answers, method)
      val median = times.flatMap(_.long("ms" + closing.indexOf(method)))
      JSON.Object("method" -> method, "verdict" -> tried.verdict, "ms" -> tried.ms) ++
        median.map(ms => "median_ms" -> ms)
    }
  }

  def sledgehammer_json(answer: Pide.Answer): JSON.Object.T =
    JSON.Object("verdict" -> answer.verdict, "ms" -> answer.ms) ++
      answer.get("method").map(method => "method" -> method)

  def record(entry: String, item: Item, answers: Pide.Answers, options: Options): JSON.Object.T = {
    val lemma = item.lemma
    JSON.Object(
      "entry" -> entry,
      "theory" -> lemma.theory.theory,
      "lemma_line" -> lemma.line,
      "step_line" -> lemma.line(item.step.cmd.range.start),
      "step_offset" -> item.step.cmd.range.start,
      "method" -> item.step.methods,
      "timeout_ms" -> Time.seconds(options.real("collect_timeout")).ms,
      "runs" -> options.int("collect_runs"),
      "goal" -> goal(answers(item.key("goal"))),
      "tries" -> tries_json(item, answers)) ++
      answers.get(item.key("sledgehammer")).map(answer => "sledgehammer" -> sledgehammer_json(answer))
  }


  /* One JSON line per step, written a batch at a time. */
  def collect_session(options: Options, session_name: String, output: Path, dirs: List[Path],
      progress: Progress): Unit =
    Pide.check(options, session_name, dirs, progress) { checked =>
      val entry = checked.dir.base.implode
      val items = for (lemma <- checked.lemmas if lemma.ok; step <- lemma.steps) yield Item(lemma, step)
      progress.echo(session_name + ": " + items.length + " `by` steps")

      var done = 0
      for (batch <- items.grouped(options.int("collect_batch"))) {
        val answers = ask_batch(checked, batch, options, progress)
        File.append(output, batch.map(item => JSON.Format(record(entry, item, answers, options)) + "\n").mkString)
        done += batch.length
        progress.echo("collect: " + done + " of " + items.length + " steps")
      }
    }

  /* The sessions of one AFP entry go into one file, which only appears when all are done. */
  def collect(options: Options, sessions: List[String], output: Path, dirs: List[Path], progress: Progress): Unit =
    if (output.is_file) progress.echo("Skipping " + output.implode + ": already there")
    else {
      val part = output.ext("part")
      File.write(part, "")
      for (session_name <- sessions) collect_session(options, session_name, part, dirs, progress)
      Isabelle_System.move_file(part, output)
    }


  val collect_tool: Isabelle_Tool =
    Isabelle_Tool("linter_collect", "record which methods close each `by` step, and how fast",
      Scala_Project.here,
      { args =>
        val dirs = new scala.collection.mutable.ListBuffer[Path]
        var output = Path.explode("collect.jsonl")
        var options = Options.init()

        val getopts = Getopts("""
Usage: isabelle linter_collect [OPTIONS] SESSIONS

  Options are:
    -O FILE      output file (default: collect.jsonl)
    -d DIR       include session directory
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Check each session once, then for every `by` step write one JSON line: the
  goal's features, and which methods close it (collect_timeout) with their
  median times over collect_runs runs. Meant for the sessions of one AFP
  entry; does nothing if FILE exists, so a run over many entries can resume.
""",
          "O:" -> (arg => output = Path.explode(arg)),
          "d:" -> (arg => dirs += Path.explode(arg)),
          "o:" -> (arg => options = options + arg))

        val sessions = getopts(args)
        if (sessions.isEmpty) getopts.usage()

        collect(options, sessions, output, dirs.toList, new Console_Progress())
      })
}
