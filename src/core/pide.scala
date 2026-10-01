/* isabelle_linter: check a session once in a headless PIDE session, then ask the prover about single
  `by` steps as document overlays (ml/linter_query.ML) */

package isabelle.isabelle_linter

import isabelle._


object Pide {
  /** steps, questions, answers **/

  /* a `by` step; goal is the command before it, whose result state is the goal the step solves */
  sealed case class Step(theory: Document.Node.Name, line: Int, goal: Command, command: Command, methods: String)

  /* run `by methods` on the goal of step */
  sealed case class Question(step: Step, methods: String, timeout: Time) {
    def key: (Long, String) = (step.command.id, methods)
  }

  sealed case class Answer(verdict: String, ms: Long, message: String) {
    def closes: Boolean = verdict == "closes"
  }

  type Answers = Map[(Long, String), Answer]

  sealed case class Finding(step: Step, message: String, replacement: String)

  val print_function = "linter_try"


  /** the steps of a checked theory **/

  def steps(snapshot: Document.Snapshot): List[Step] = {
    val node = snapshot.node
    val lines = Line.Document(node.source)
    val commands = node.command_iterator().toList.filterNot(_._1.is_ignored)
    for {
      ((goal, _), (command, offset)) <- commands.zip(commands.drop(1))
      if command.span.name == "by"
      methods = Token.implode(command.span.content.dropWhile(!_.is_command).drop(1)).trim
    } yield Step(snapshot.node_name, lines.position(offset).line1, goal, command, methods)
  }


  /** running **/

  /* check the session's theories, then ask the lint's questions in rounds until none are new */
  def run(
    options: Options,
    session_name: String,
    lint: Lint,
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
      val all_steps =
        for {
          (name, status) <- checked.nodes
          _ = if (!status.ok) progress.echo_warning("Theory " + name.theory + " does not check: skipped")
          if status.ok
          step <- steps(checked.snapshot(name))
        } yield step
      progress.echo(all_steps.length.toString + " `by` steps in " + theories.length + " theories")

      var answers: Answers = Map.empty
      var round = lint.ask(all_steps, answers, options).filterNot(q => answers.contains(q.key))
      while (round.nonEmpty) {
        progress.echo("Asking " + round.length + " questions ...")
        answers ++= ask(session, round, progress)
        round = lint.ask(all_steps, answers, options).filterNot(q => answers.contains(q.key))
      }
      lint.report(all_steps, answers, options)
    }
    finally { session.stop() }
  }

  /* one round: every question becomes an overlay, the answers come back as command results */
  private def ask(session: Headless.Session, questions: List[Question], progress: Progress): Answers = {
    val placed = questions.map(q => (Document_ID.make().toString, q))
    val overlays =
      placed.foldLeft(Map.empty[Document.Node.Name, Document.Node.Overlays]) {
        case (m, (instance, q)) =>
          val o = m.getOrElse(q.step.theory, Document.Node.Overlays.empty)
          m + (q.step.theory -> o.insert(q.step.goal, print_function, List(instance, q.timeout.ms.toString, q.methods)))
      }
    session.update(Document.Blobs.empty,
      overlays.toList.map({ case (name, o) => name -> Document.Node.Perspective(true, Text.Perspective.empty, o) }))

    /* the time limits are enforced by the prover; the watchdog only guards against a dead session */
    val watchdog = Time.seconds(questions.map(_.timeout.seconds).max + 120)
    var answers: Answers = Map.empty
    var last = Time.now()
    while (answers.size < placed.length && Time.now() - last < watchdog) {
      progress.expose_interrupt()
      Time.seconds(0.2).sleep()
      val state = session.get_state()
      for ((instance, q) <- placed if !answers.contains(q.key)) {
        val results = state.command_results(state.snapshot(q.step.theory).version, q.step.goal)
        results.iterator.collectFirst {
          case (_, XML.Elem(Markup(Markup.RESULT, props @ Markup.Instance(i)), body)) if i == instance =>
            Answer(Properties.get(props, "verdict").getOrElse("error"),
              Properties.get(props, "ms").flatMap(Value.Long.unapply).getOrElse(0L),
              cat_lines(split_lines(XML.content(body)).drop(1)))
        }.foreach { a => answers += (q.key -> a); last = Time.now() }
      }
    }
    if (answers.size < placed.length) progress.echo_warning((placed.length - answers.size) + " questions unanswered")
    answers
  }
}


/* A lint asks questions about `by` steps in rounds: each round is answered in parallel and the next
  round sees all answers so far. When there are no new questions, report turns answers into findings. */
abstract class Lint {
  def name: String
  def ask(steps: List[Pide.Step], answers: Pide.Answers, options: Options): List[Pide.Question]
  def report(steps: List[Pide.Step], answers: Pide.Answers, options: Options): List[Pide.Finding]
}
