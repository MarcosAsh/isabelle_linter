/* Check a session once in a headless PIDE session, then ask the prover questions about single
   lemmas: each is a print function of ml/linter_query.ML, attached to a command as an overlay. */

package isabelle.isabelle_linter

import isabelle._


object Pide {
  /* A print function run on the state after command `at`. A serial question is asked alone, so
     that other questions do not distort its times. */
  sealed case class Question(key: String, theory: Document.Node.Name, at: Command, function: String,
      args: List[String], timeout: Time, serial: Boolean = false)

  /* The verdict, with all properties of the print function's result message. */
  sealed case class Answer(verdict: String, props: Properties.T = Nil) {
    def closes: Boolean = verdict == "closes"
    def get(name: String): Option[String] = Properties.get(props, name)
    def long(name: String): Option[Long] = get(name).flatMap(Value.Long.unapply)
    def ms: Long = long("ms").getOrElse(0L)
    def ms2: Long = long("ms2").getOrElse(0L)
    def medians: Medians = Medians(ms, ms2)
  }

  type Answers = Map[String, Answer]

  val unanswered: Answer = Answer("unanswered")


  /* An edited lemma gets linter_factor times the time of the lemma as written. Below a second,
     timing noise alone could make it run out of time. */
  val min_limit_ms = 1000L

  def budget(original: Answer, options: Options): Long =
    (original.ms * options.real("linter_factor")).toLong max min_limit_ms


  /* The checked session with the queries loaded. Definitions are commands like `datatype` and
     `fun`; snapshots are of the session's own theories. */
  sealed case class Checked(session: Headless.Session, lemmas: List[Lemma], definitions: List[Lemma],
    hol: Boolean, dir: Path, snapshots: List[Document.Snapshot])

  /* Check the session once, read its lemmas and run body. With imported, the lemmas of imported
     theories that no heap holds count as the session's own. */
  def check[A](options: Options, session_name: String, dirs: List[Path], progress: Progress,
      imported: Boolean = false)(body: Checked => A): A = {
    val structure = Sessions.load_structure(options, dirs = dirs)
    val deps = Sessions.deps(structure.selection(session_name), progress = progress)
    val theories = deps(session_name).proper_session_theories.map(_.theory)
    val logic = structure(session_name).parent.getOrElse("Pure")
    if (!Build.build_logic(options, logic, build_heap = true, progress = progress, dirs = dirs, strict = true).ok)
      error("Failed to build " + quote(logic))

    /* No forked proofs: a question must see every proof it starts fail or finish, and
       Thm.consolidate_theory does not join an unnamed or non-theorem result. */
    val resources =
      Headless.Resources.make(options + "parallel_proofs=0", logic, Logger.make_progress(progress),
        session_dirs = dirs, include_sessions = deps.sessions_structure.imports_topological_order,
        progress = progress)
    val session = resources.start_session(progress = progress)
    val watch = new Watch(session, progress)
    try {
      val hol = structure.build_requirements(List(logic)).contains("HOL")
      load_queries(session, hol)

      val checked = session.use_theories(theories, progress = progress)
      val state = session.get_state()

      /* Imported theories outside every heap are checked too, but only the session's own are linted. */
      val all_snapshots = checked.nodes.map({ case (name, _) => name -> checked.snapshot(name) }).toMap
      val own = checked.nodes.map(_._1).filter(name => imported || theories.contains(name.theory))
      val snapshots = own.map(all_snapshots)
      val lemmas = snapshots.flatMap(Lemma.read(state, _))
      progress.echo(lemmas.count(_.ok).toString + " of " + lemmas.length + " lemmas check")

      val own_files = deps(session_name).proper_session_theories.map(_.path)
      val downstream = Downstream.make(structure, session_name, own_files, all_snapshots)
      val definitions = own.flatMap(name => Lemma.definitions(state, all_snapshots(name), downstream(name)))

      body(Checked(session, lemmas, definitions, hol, structure(session_name).dir, snapshots))
    }
    finally { watch.stop(); session.stop() }
  }

  /* Pass on the prover's own output and its exit as warnings: it can die, of running out of
     memory for instance, and a dead prover is otherwise silent. */
  private class Watch(session: Session, progress: Progress) {
    private val output =
      Session.Consumer[Prover.Output]("linter_output") { msg =>
        if (msg.is_stdout || msg.is_stderr || msg.is_system)
          progress.echo_warning("prover: " + XML.content(msg.message))
      }
    private val phase =
      Session.Consumer[Session.Phase]("linter_phase") {
        case Session.Terminated(result) => progress.echo_warning("prover exited: " + result.print_return_code)
        case _ =>
      }

    session.raw_output_messages += output
    session.phase_changed += phase

    def stop(): Unit = {
      session.raw_output_messages -= output
      session.phase_changed -= phase
    }
  }

  /* The prover's latest ML statistics and peak heap while a batch is out, for the warning when
     questions go unanswered. */
  private class Stats(session: Session) {
    @volatile private var last: Properties.T = Nil
    @volatile private var peak = Space.zero
    private val consumer =
      Session.Consumer[Session.Runtime_Statistics]("linter_stats") { stats =>
        val used = ML_Statistics.memory_status(stats.props).heap_used_minor
        if (used.bytes > peak.bytes) peak = used
        last = stats.props
      }

    session.runtime_statistics += consumer

    def stop(): Unit = session.runtime_statistics -= consumer

    def print: String =
      if (last.isEmpty) "no ML statistics"
      else {
        val memory = ML_Statistics.memory_status(last)
        def int(name: String): Int = Properties.get(last, name).flatMap(Value.Int.unapply).getOrElse(0)
        "heap " + memory.heap_used_minor.print + " of " + memory.heap_size.print + " (peak " + peak.print +
          "), GC " + memory.gc_percent + "%, tasks " + int("tasks_running") + " running " +
          int("tasks_ready") + " ready, workers " + int("workers_active") + " of " + int("workers_total") + " active"
      }
  }

  /* Edits to a dead prover are dropped silently, so a dead prover must stop the run. */
  private def check_ready(session: Session, out: Int): Unit =
    if (!session.is_ready)
      error("Prover died with " + out + " questions out, prover log:\n" + session.syslog.content())

  def run(
    options: Options,
    session_name: String,
    lints: List[Lint],
    dirs: List[Path] = Nil,
    progress: Progress = new Progress
  ): List[Finding] =
    check(options, session_name, dirs, progress) { checked =>
      val log = proper_string(options.string("linter_log")).map(Path.explode)
      val batch = options.int("linter_batch")
      lints.flatMap { lint =>
        val targets = lint.targets(checked)
        val answers = rounds(checked.session, lint.name, progress, log, batch)(lint.ask(targets, _, options))
        lint.read(checked, options) ::: lint.report(targets, answers, options)
      }
    }

  /* Ask in rounds until next has no new questions. A big round goes in batches, since thousands of
     questions at once fill the heap. */
  def rounds(session: Headless.Session, name: String, progress: Progress, log: Option[Path] = None,
      batch: Int = 500)(next: Answers => List[Question]): Answers = {
    var answers: Answers = Map.empty
    def new_questions(): List[Question] =
      next(answers).filterNot(question => answers.contains(question.key)).distinctBy(_.key)

    var round = new_questions()
    while (round.nonEmpty) {
      val (serial, parallel) = round.partition(_.serial)
      progress.echo(name + ": asking " + round.length + " questions" +
        (if (serial.isEmpty) "" else ", " + serial.length + " one at a time"))
      try {
        for (group <- parallel.grouped(batch max 1)) answers ++= ask(session, group, progress)
        for (question <- serial) answers ++= ask(session, List(question), progress)
        answers ++= retry(session, name, parallel, answers, progress)
      }
      finally { log.foreach(write_log(_, name, round, answers)) }
      round = new_questions()
    }
    answers
  }

  /* A question cut short among many, by a stack overflow in its thread say, or given up by the
     watchdog, gets one more try alone; what it answers then stands. */
  val lost: Set[String] = Set("interrupted", "unanswered")

  private def retry(session: Headless.Session, name: String, questions: List[Question], answers: Answers,
      progress: Progress): Answers = {
    val again = questions.filter(question => lost(answers(question.key).verdict))
    if (again.nonEmpty) progress.echo(name + ": asking " + again.length + " cut-short questions again, one at a time")
    again.foldLeft(Map.empty: Answers)((retried, question) => retried ++ ask(session, List(question), progress))
  }

  /* One TSV row per question: lint, function, key, args, verdict, then the answer's properties.
     A round cut short by an error logs its missing answers as unanswered. */
  private def write_log(path: Path, lint: String, questions: List[Question], answers: Answers): Unit = {
    def clean(s: String): String = s.replace('\t', ' ').nn.replace('\n', ' ').nn
    val rows =
      for (question <- questions) yield {
        val answer = answers.getOrElse(question.key, unanswered)
        val fields =
          List(lint, question.function, question.key, question.args.mkString(" | "), answer.verdict) :::
            answer.props.map({ case (name, value) => name + "=" + value })
        fields.map(clean).mkString("\t") + "\n"
      }
    File.append(path, rows.mkString)
  }

  /* Sledgehammer and try0 need HOL, the rule statistics an Isabelle built with etc/simpstats.patch. */
  private def load_queries(session: Headless.Session, hol: Boolean): Unit = {
    val theories =
      "Linter_Query" :: (if (hol) List("Linter_Sledgehammer", "Linter_Try0") else Nil) :::
        (if (Simp_Hygiene.available) List("Linter_Rule_Stats") else Nil)
    val query_dir = Path.explode("$ISABELLE_LINTER_HOME/ml").absolute.implode
    if (!session.use_theories(theories, master_dir = query_dir).ok)
      error("Failed to load " + theories.mkString(", ") + " from ml/")
  }

  /* Ask all questions at once, wait for their answers, then take the questions back. */
  def ask(session: Headless.Session, questions: List[Question], progress: Progress): Answers = {
    /* Each question gets a fresh instance id, which its result message carries back. */
    val placed = questions.map(question => Document_ID.make().toString -> question)
    val overlays = place(placed)
    def perspectives(f: Document.Node.Overlays => Document.Node.Overlays): List[Document.Edit_Text] =
      overlays.toList.map({ case (name, o) => name -> Document.Node.Perspective(true, Text.Perspective.empty, f(o)) })

    check_ready(session, placed.length)
    session.update(Document.Blobs.empty, perspectives(o => o))
    val answers = collect(session, placed, progress)

    /* Stop whatever is still running, so that it does not hold workers in the next batch. */
    session.update(Document.Blobs.empty, perspectives(_ => Document.Node.Overlays.empty))
    placed.map({ case (_, question) => question.key -> answers.getOrElse(question.key, unanswered) }).toMap
  }

  /* The overlays of each theory: the print function on its command, with instance and timeout first. */
  private def place(placed: List[(String, Question)]): Map[Document.Node.Name, Document.Node.Overlays] =
    placed.foldLeft(Map.empty[Document.Node.Name, Document.Node.Overlays]) {
      case (overlays, (instance, question)) =>
        val theory = overlays.getOrElse(question.theory, Document.Node.Overlays.empty)
        val args = instance :: question.timeout.ms.toString :: question.args
        overlays + (question.theory -> theory.insert(question.at, question.function, args))
    }

  /* The prover enforces the time limits; the watchdog only guards against a stuck prover. */
  private val watchdog_slack = Time.seconds(120)
  private val poll_interval = Time.seconds(0.2)
  private val report_interval = Time.seconds(600)

  private def collect(session: Headless.Session, placed: List[(String, Question)], progress: Progress): Answers = {
    val watchdog = Time.seconds(placed.map(_._2.timeout.seconds).max + watchdog_slack.seconds)
    val stats = new Stats(session)
    var answers: Answers = Map.empty
    var last = Time.now()
    var reported = Time.now()
    try {
      while (answers.size < placed.length && Time.now() - last < watchdog && session.is_ready) {
        progress.expose_interrupt()
        poll_interval.sleep()
        val state = session.get_state()
        val versions = placed.map(_._2.theory).distinct.map(name => name -> state.snapshot(name).version).toMap
        for ((instance, question) <- placed if !answers.contains(question.key)) {
          read_answer(state.command_results(versions(question.theory), question.at), instance)
            .foreach { answer => answers += (question.key -> answer); last = Time.now() }
        }
        /* A long round writes nothing else, so say it is still going. */
        if (Time.now() - reported > report_interval) {
          progress.echo("  " + answers.size + " of " + placed.length + " answered")
          reported = Time.now()
        }
      }
    }
    finally { stats.stop() }
    check_ready(session, placed.length - answers.size)
    if (answers.size < placed.length) {
      progress.echo_warning((placed.length - answers.size).toString + " questions unanswered, last answer " +
        (Time.now() - last).seconds.round + " s before; " + stats.print)
    }
    answers
  }

  /* A print reports "interrupted" when it is cancelled; a real verdict wins if it ran again. */
  private def read_answer(results: Command.Results, instance: String): Option[Answer] = {
    val found =
      results.iterator.collect {
        case (_, XML.Elem(Markup(Markup.RESULT, props @ Markup.Instance(i)), _)) if i == instance =>
          Answer(Properties.get(props, "verdict").getOrElse("fails"), props)
      }.toList
    found.find(_.verdict != "interrupted").orElse(found.headOption)
  }
}


/* The median times of a lemma or step as written and with its fix (linter_time, linter_runs). */
sealed case class Medians(before: Long, after: Long)

/* A fix is the lemma's new text, checked alone. Its edit replaces one range, so that fixes of
   disjoint ranges in one lemma can be combined. */
sealed case class Finding(lint: String, lemma: Lemma, line: Int, message: String, fix: Option[String] = None,
  edit: Option[(Text.Range, String)] = None)

/* A lint's ask is called in rounds with all answers so far, until it asks nothing new; then report
   turns the answers into findings. read finds what the check shows without any question. */
abstract class Lint {
  def name: String
  def ask(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Pide.Question]
  def report(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding]
  def read(checked: Pide.Checked, options: Options): List[Finding] = Nil
  def targets(checked: Pide.Checked): List[Lemma] = checked.lemmas.filter(_.ok)
}
