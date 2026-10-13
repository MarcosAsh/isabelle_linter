/* isabelle_linter: check a session once with PIDE, then ask questions as overlays */

package isabelle.isabelle_linter

import isabelle._


object Pide {
  /* a print function of ml/linter_query.ML, run on the result state of `at`; serial: asked alone,
    so that its times are not distorted by other questions */
  sealed case class Question(key: String, theory: Document.Node.Name, at: Command, function: String,
      args: List[String], timeout: Time, serial: Boolean = false)

  /* all properties of the result message */
  sealed case class Answer(verdict: String, props: Properties.T = Nil) {
    def closes: Boolean = verdict == "closes"
    def get(name: String): Option[String] = Properties.get(props, name)
    def long(name: String): Option[Long] = get(name).flatMap(Value.Long.unapply)
    def ms: Long = long("ms").getOrElse(0L)
    def ms2: Long = long("ms2").getOrElse(0L)
  }

  type Answers = Map[String, Answer]

  /* never counts as closed */
  val unanswered: Answer = Answer("unanswered")


  /* a checked session with the queries loaded; dir is the session's directory */
  sealed case class Checked(session: Headless.Session, lemmas: List[Lemma], hol: Boolean, dir: Path)

  /* check the session once, read its lemmas, run body, stop the session; imported: also the
    lemmas of imported theories that no heap holds */
  def check[A](options: Options, session_name: String, dirs: List[Path], progress: Progress,
      imported: Boolean = false)(body: Checked => A): A = {
    val structure = Sessions.load_structure(options, dirs = dirs)
    val deps = Sessions.deps(structure.selection(session_name), progress = progress)
    val theories = deps(session_name).proper_session_theories.map(_.theory)
    val logic = structure(session_name).parent.getOrElse("Pure")
    if (!Build.build_logic(options, logic, build_heap = true, progress = progress, dirs = dirs, strict = true).ok)
      error("Failed to build " + quote(logic))

    /* no forked proofs: a question must see every proof it starts fail or finish, and an
      unnamed or non-theorem result is not joined by Thm.consolidate_theory */
    val resources =
      Headless.Resources.make(options + "parallel_proofs=0", logic, session_dirs = dirs,
        include_sessions = deps.sessions_structure.imports_topological_order, progress = progress)
    val session = resources.start_session(progress = progress)
    try {
      val hol = structure.build_requirements(List(logic)).contains("HOL")
      load_queries(session, hol)

      val checked = session.use_theories(theories, progress = progress)
      val state = session.get_state()

      /* imported theories outside a heap are loaded too; lint only the session's own */
      val own = checked.nodes.map(_._1).filter(name => imported || theories.contains(name.theory))
      val lemmas = own.flatMap(name => Lemma.read(state, checked.snapshot(name)))
      progress.echo(lemmas.count(_.ok).toString + " of " + lemmas.length + " lemmas check")

      body(Checked(session, lemmas, hol, structure(session_name).dir))
    }
    finally { session.stop() }
  }

  /* each lint asks in rounds until it has no new questions */
  def run(
    options: Options,
    session_name: String,
    lints: List[Lint],
    dirs: List[Path] = Nil,
    progress: Progress = new Progress
  ): List[Finding] =
    check(options, session_name, dirs, progress) { checked =>
      val ok = checked.lemmas.filter(_.ok)
      lints.flatMap { lint =>
        val log = proper_string(options.string("linter_log")).map(Path.explode)
        val batch = options.int("linter_batch")
        val answers = rounds(checked.session, lint.name, progress, log, batch)(a => lint.ask(ok, a, options))
        lint.report(ok, answers, options)
      }
    }

  /* ask until next has no new questions; a big round goes in batches, since thousands of questions
    at once fill the heap */
  def rounds(session: Headless.Session, name: String, progress: Progress, log: Option[Path] = None,
      batch: Int = 500)(next: Answers => List[Question]): Answers = {
    var answers: Answers = Map.empty
    var round = next(answers).filterNot(q => answers.contains(q.key)).distinctBy(_.key)
    while (round.nonEmpty) {
      val (serial, parallel) = round.partition(_.serial)
      progress.echo(name + ": asking " + round.length + " questions" +
        (if (serial.isEmpty) "" else ", " + serial.length + " one at a time"))
      for (b <- parallel.grouped(batch max 1)) answers ++= ask(session, b, progress)
      for (q <- serial) answers ++= ask(session, List(q), progress)
      log.foreach(write_log(_, name, round, answers))
      round = next(answers).filterNot(q => answers.contains(q.key)).distinctBy(_.key)
    }
    answers
  }

  /* one row per question: lint, function, key, args, verdict, then the answer's properties */
  private def write_log(path: Path, lint: String, questions: List[Question], answers: Answers): Unit = {
    def clean(s: String): String = s.replace('\t', ' ').replace('\n', ' ')
    val rows =
      for (q <- questions) yield {
        val a = answers(q.key)
        (List(lint, q.function, q.key, q.args.mkString(" | "), a.verdict) :::
          a.props.map({ case (k, v) => k + "=" + v })).map(clean).mkString("\t") + "\n"
      }
    File.append(path, rows.mkString)
  }

  /* the print functions of ml/; Sledgehammer needs HOL */
  private def load_queries(session: Headless.Session, hol: Boolean): Unit = {
    val theories = "Linter_Query" :: (if (hol) List("Linter_Sledgehammer") else Nil)
    val query_dir = Path.explode("$ISABELLE_LINTER_HOME/ml").absolute.implode
    if (!session.use_theories(theories, master_dir = query_dir).ok)
      error("Failed to load " + theories.mkString(", ") + " from ml/")
  }

  /* one round: all questions as overlays at once */
  def ask(session: Headless.Session, questions: List[Question], progress: Progress): Answers = {
    val placed = questions.map(q => Document_ID.make().toString -> q)
    val overlays =
      placed.foldLeft(Map.empty[Document.Node.Name, Document.Node.Overlays]) {
        case (m, (instance, q)) =>
          val o = m.getOrElse(q.theory, Document.Node.Overlays.empty)
          m + (q.theory -> o.insert(q.at, q.function, instance :: q.timeout.ms.toString :: q.args))
      }
    def perspectives(f: Document.Node.Overlays => Document.Node.Overlays): List[Document.Edit_Text] =
      overlays.toList.map({ case (name, o) => name -> Document.Node.Perspective(true, Text.Perspective.empty, f(o)) })
    session.update(Document.Blobs.empty, perspectives(o => o))

    /* the prover enforces time limits; this only guards against a dead session */
    val watchdog = Time.seconds(questions.map(_.timeout.seconds).max + 120)
    var answers: Answers = Map.empty
    var last = Time.now()
    while (answers.size < placed.length && Time.now() - last < watchdog) {
      progress.expose_interrupt()
      Time.seconds(0.2).sleep()
      val state = session.get_state()
      val versions = placed.map(_._2.theory).distinct.map(n => n -> state.snapshot(n).version).toMap
      for ((instance, q) <- placed if !answers.contains(q.key)) {
        state.command_results(versions(q.theory), q.at).iterator.collectFirst {
          case (_, XML.Elem(Markup(Markup.RESULT, props @ Markup.Instance(i)), _)) if i == instance =>
            Answer(Properties.get(props, "verdict").getOrElse("fails"), props)
        }.foreach { a => answers += (q.key -> a); last = Time.now() }
      }
    }
    if (answers.size < placed.length) progress.echo_warning((placed.length - answers.size).toString + " questions unanswered")

    /* stop whatever is still running, so that it does not hold workers in the next batch */
    session.update(Document.Blobs.empty, perspectives(_ => Document.Node.Overlays.empty))
    placed.map({ case (_, q) => q.key -> answers.getOrElse(q.key, unanswered) }).toMap
  }
}


/* fix: the checked new text of the lemma */
sealed case class Finding(lint: String, lemma: Lemma, line: Int, message: String, fix: Option[String] = None)

/* ask is called in rounds and sees all answers so far; report runs when it asks nothing new */
abstract class Lint {
  def name: String
  def ask(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Pide.Question]
  def report(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding]
}
