/* linter_collect: for every `by` step, its goal and which methods close it how fast */

package isabelle.isabelle_linter

import isabelle._


object Collect {
  /* a `by` step and the methods tried on it: its own first, then faster_step's */
  sealed case class Item(lemma: Lemma, step: Step) {
    val methods: List[String] = (step.methods :: Faster_Step.candidates(step)).distinct

    def key(what: String): String = lemma.key + ":" + step.cmd.offset + ":" + what

    def question(function: String, what: String, args: List[String], timeout: Time): Pide.Question =
      Pide.Question(key(what), lemma.theory, step.goal.command, function, args, timeout)

    def tried(answers: Pide.Answers, method: String): Pide.Answer = answers(key("try:" + method))

    def closing(answers: Pide.Answers): List[String] = methods.filter(m => tried(answers, m).closes)
  }


  /* questions */

  /* the goal, and every method with the same limit; these may run in parallel */
  def tries(item: Item, timeout: Time): List[Pide.Question] =
    item.question("linter_goal", "goal", Nil, timeout) ::
      item.methods.map(m => item.question("linter_try", "try:" + m, List(m), timeout))

  /* the methods that closed, re-timed one after another */
  def timing(item: Item, answers: Pide.Answers, runs: Int, timeout: Time): List[Pide.Question] =
    item.closing(answers) match {
      case Nil => Nil
      case ms => List(item.question("linter_times", "times", runs.toString :: ms, timeout))
    }

  def sledgehammer(item: Item, timeout: Time): Pide.Question =
    item.question("linter_sledgehammer", "sledgehammer", List(""), timeout)

  /* chunks of a few steps, so the timed runs barely compete */
  def ask_in_chunks(checked: Pide.Checked, questions: List[List[Pide.Question]], size: Int,
      progress: Progress): Pide.Answers = {
    var answers: Pide.Answers = Map.empty
    for (chunk <- questions.grouped(size); qs = chunk.flatten if qs.nonEmpty) {
      answers ++= Pide.ask(checked.session, qs, progress)
    }
    answers
  }

  def ask_batch(checked: Pide.Checked, batch: List[Item], options: Options, progress: Progress): Pide.Answers = {
    val timeout = Time.seconds(options.real("collect_timeout"))
    val runs = options.int("collect_runs")
    val parallel = options.int("collect_parallel")

    val answers = Pide.ask(checked.session, batch.flatMap(tries(_, timeout)), progress)
    val times = ask_in_chunks(checked, batch.map(timing(_, answers, runs, timeout)), parallel, progress)

    val sh_timeout = Time.seconds(options.real("collect_sledgehammer"))
    val sh =
      if (!checked.hol || sh_timeout.is_zero) Map.empty
      else ask_in_chunks(checked, batch.map(i => List(sledgehammer(i, sh_timeout))), parallel, progress)

    answers ++ times ++ sh
  }


  /* records */

  /* numbers as numbers */
  def value(s: String): Any = Value.Long.unapply(s).getOrElse(s)

  /* the result message also carries its position */
  val not_features: Set[String] =
    Set(Markup.INSTANCE, "verdict", Markup.SERIAL, Markup.ID, Markup.LABEL, Markup.OFFSET, Markup.END_OFFSET,
      Markup.FILE)

  def goal(answer: Pide.Answer): JSON.Object.T =
    answer.props.filterNot(p => not_features(p._1)).map({ case (a, b) => a -> value(b) }).toMap

  def tries_json(item: Item, answers: Pide.Answers): List[JSON.Object.T] = {
    val times = answers.get(item.key("times"))
    val closing = item.closing(answers)
    for (m <- item.methods) yield {
      val a = item.tried(answers, m)
      val median = times.flatMap(_.long("ms" + closing.indexOf(m)))
      JSON.Object("method" -> m, "verdict" -> a.verdict, "ms" -> a.ms) ++
        median.map(t => "median_ms" -> t)
    }
  }

  def sledgehammer_json(answer: Pide.Answer): JSON.Object.T =
    JSON.Object("verdict" -> answer.verdict, "ms" -> answer.ms) ++
      answer.get("method").map(m => "method" -> m)

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
      answers.get(item.key("sledgehammer")).map(a => "sledgehammer" -> sledgehammer_json(a))
  }


  /* one JSON line per step, a batch at a time */
  def collect_session(options: Options, session_name: String, output: Path, dirs: List[Path],
      progress: Progress): Unit =
    Pide.check(options, session_name, dirs, progress) { checked =>
      val entry = checked.dir.base.implode
      val items = for (lemma <- checked.lemmas if lemma.ok; step <- lemma.steps) yield Item(lemma, step)
      progress.echo(session_name + ": " + items.length + " `by` steps")

      var done = 0
      for (batch <- items.grouped(options.int("collect_batch"))) {
        val answers = ask_batch(checked, batch, options, progress)
        File.append(output, batch.map(i => JSON.Format(record(entry, i, answers, options)) + "\n").mkString)
        done += batch.length
        progress.echo("collect: " + done + " of " + items.length + " steps")
      }
    }

  /* the sessions of one AFP entry into one file; it only appears when all are done */
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
