/* isabelle_linter: check a session once with PIDE, then ask questions as overlays */

package isabelle.isabelle_linter

import isabelle._


object Pide {
  /* a print function of ml/linter_query.ML, run on the result state of `at` */
  sealed case class Question(key: String, theory: Document.Node.Name, at: Command, function: String,
      args: List[String], timeout: Time)

  sealed case class Answer(verdict: String, ms: Long, ms2: Long) {
    def closes: Boolean = verdict == "closes"
  }

  type Answers = Map[String, Answer]

  /* never counts as closed */
  val unanswered: Answer = Answer("unanswered", 0, 0)


  /* each lint asks in rounds until it has no new questions */
  def run(
    options: Options,
    session_name: String,
    lints: List[Lint],
    dirs: List[Path] = Nil,
    progress: Progress = new Progress
  ): List[Finding] = {
    val structure = Sessions.load_structure(options, dirs = dirs)
    val deps = Sessions.deps(structure.selection(session_name), progress = progress)
    val theories = deps(session_name).proper_session_theories.map(_.theory)
    val logic = structure(session_name).parent.getOrElse("Pure")
    if (!Build.build_logic(options, logic, build_heap = true, progress = progress, dirs = dirs, strict = true).ok)
      error("Failed to build " + quote(logic))

    val resources =
      Headless.Resources.make(options, logic, session_dirs = dirs,
        include_sessions = deps.sessions_structure.imports_topological_order, progress = progress)
    val session = resources.start_session(progress = progress)
    try {
      val query_dir = Path.explode("$ISABELLE_LINTER_HOME/ml").absolute.implode
      if (!session.use_theories(List("Linter_Query"), master_dir = query_dir).ok)
        error("Failed to load ml/Linter_Query.thy")

      val checked = session.use_theories(theories, progress = progress)
      val state = session.get_state()

      /* imported theories outside a heap are loaded too; lint only the session's own */
      val own = checked.nodes.map(_._1).filter(name => theories.contains(name.theory))
      val lemmas = own.flatMap(name => Lemma.read(state, checked.snapshot(name)))
      val ok = lemmas.filter(_.ok)
      progress.echo(ok.length.toString + " of " + lemmas.length + " lemmas check")

      lints.flatMap { lint =>
        var answers: Answers = Map.empty
        def next(): List[Question] = lint.ask(ok, answers, options).filterNot(q => answers.contains(q.key))
        var round = next()
        while (round.nonEmpty) {
          progress.echo(lint.name + ": asking " + round.length + " questions")
          answers ++= ask(session, round, progress)
          round = next()
        }
        lint.report(ok, answers, options)
      }
    }
    finally { session.stop() }
  }

  /* one round: all questions as overlays at once */
  private def ask(session: Headless.Session, questions: List[Question], progress: Progress): Answers = {
    val placed = questions.map(q => Document_ID.make().toString -> q)
    val overlays =
      placed.foldLeft(Map.empty[Document.Node.Name, Document.Node.Overlays]) {
        case (m, (instance, q)) =>
          val o = m.getOrElse(q.theory, Document.Node.Overlays.empty)
          m + (q.theory -> o.insert(q.at, q.function, instance :: q.timeout.ms.toString :: q.args))
      }
    session.update(Document.Blobs.empty,
      overlays.toList.map({ case (name, o) => name -> Document.Node.Perspective(true, Text.Perspective.empty, o) }))

    /* the prover enforces time limits; this only guards against a dead session */
    val watchdog = Time.seconds(questions.map(_.timeout.seconds).max + 120)
    var answers: Answers = Map.empty
    var last = Time.now()
    while (answers.size < placed.length && Time.now() - last < watchdog) {
      progress.expose_interrupt()
      Time.seconds(0.2).sleep()
      val state = session.get_state()
      for ((instance, q) <- placed if !answers.contains(q.key)) {
        state.command_results(state.snapshot(q.theory).version, q.at).iterator.collectFirst {
          case (_, XML.Elem(Markup(Markup.RESULT, props @ Markup.Instance(i)), _)) if i == instance =>
            def ms(name: String): Long = Properties.get(props, name).flatMap(Value.Long.unapply).getOrElse(0L)
            Answer(Properties.get(props, "verdict").getOrElse("fails"), ms("ms"), ms("ms2"))
        }.foreach { a => answers += (q.key -> a); last = Time.now() }
      }
    }
    if (answers.size < placed.length) progress.echo_warning((placed.length - answers.size).toString + " questions unanswered")
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
