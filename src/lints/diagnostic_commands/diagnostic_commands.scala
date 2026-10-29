/* The diagnostic_commands lint: commands like nitpick or value that prove nothing but run on every
   build. It reads their times from the check and asks the prover nothing. */

package isabelle.isabelle_linter

import isabelle._


object Diagnostic_Commands extends Lint {
  val name = "diagnostic_commands"

  /* Proof and counterexample search is only of use while writing a proof, so -F deletes it. */
  val exploration: Set[String] =
    Set("nitpick", "nunchaku", "refute", "quickcheck", "sledgehammer", "try", "try0", "solve_direct",
      "find_theorems", "find_consts", "find_unused_assms", "sketch", "explore", "sketch_subgoals")

  /* These compute, compile or check something, and may be meant as tests, so they are never deleted. */
  val tests: Set[String] =
    Set("export_code", "value", "values", "values_prolog", "test_code", "approximate", "real_limit",
      "real_expansion", "ML_val", "ML_command", "compile_generated_files", "export_generated_files",
      "scala_build_generated_files")


  /* By keyword kind; export_code is a declaration, but no proof can use what it generates. */
  def diagnostic(cmd: Cmd): Boolean = cmd.kind == Keyword.DIAG || cmd.name == "export_code"

  /* `nitpick [expect = genuine]` fails the build when it finds nothing, so it is a test; so,
     roughly, is every nitpick of a session with `nitpick_params [expect = ...]`. */
  def expecting(cmds: List[Cmd]): Set[String] =
    cmds.filter(c => c.name.endsWith("_params") && expects(c)).map(_.name.stripSuffix("_params")).toSet

  def expects(cmd: Cmd): Boolean = cmd.body.exists(_.is("expect"))

  /* Exploration, test, or noise, which only prints. */
  def category(cmd: Cmd, expected: Set[String]): String =
    if (tests(cmd.name)) "test"
    else if (exploration(cmd.name) && (expects(cmd) || expected(cmd.name))) "test"
    else if (exploration(cmd.name)) "exploration"
    else "noise"


  /* The time PIDE took for the command when the session was checked. */
  def time(snapshot: Document.Snapshot, cmd: Cmd): Time =
    snapshot.state.command_status(snapshot.version, cmd.command).timings.sum(Date.now())

  /* The languages of `export_code ... checking SML Haskell`, whose compilers it runs. */
  def compiled(cmd: Cmd): List[String] = {
    var depth = 0
    cmd.body.dropWhile(!_.is("checking")).drop(1).filter { t =>
      if (t.is("(")) depth += 1 else if (t.is(")")) depth -= 1
      depth == 0 && t.token.is_name
    }.map(_.source)
  }


  /* deletions */

  /* A lemma that only explores: its statement, exploration commands, then `oops`. */
  def exploring(lemma: Lemma, expected: Set[String]): Boolean =
    lemma.cmds.length > 2 && lemma.cmds.last.name == "oops" &&
      lemma.cmds.tail.init.forall(c => diagnostic(c) && category(c, expected) == "exploration")

  /* start to stop, with the whole line if nothing else is on it, else with the space before or after. */
  def deletion(text: String, start: Int, stop: Int): Text.Range = {
    val line_start = text.lastIndexOf('\n', start - 1) + 1
    val line_stop = text.indexOf('\n', stop) match { case -1 => text.length case i => i + 1 }
    val before = text.substring(line_start, start).nn.isBlank
    val after = text.substring(stop, line_stop).nn.isBlank
    if (before && after) Text.Range(line_start, line_stop)
    else if (before) Text.Range(start, spaces_after(text, stop))
    else Text.Range(spaces_before(text, start), stop)
  }

  private def spaces_after(text: String, i: Int): Int =
    text.indexWhere(_ != ' ', i) match { case -1 => text.length case j => j }

  private def spaces_before(text: String, i: Int): Int = text.lastIndexWhere(_ != ' ', i - 1) + 1

  /* The command, or the whole lemma if it only explores. */
  def delete(lemma: Lemma, cmd: Cmd, expected: Set[String]): (Text.Range, String) = {
    val (start, stop) =
      if (exploring(lemma, expected)) (lemma.start, lemma.cmds.last.span_stop)
      else (cmd.range.start, cmd.span_stop)
    deletion(lemma.text, start, stop) -> ""
  }

  /* The lemma's new text: without the command, or nothing when the deletion covers it. */
  def fixed(lemma: Lemma, edit: (Text.Range, String)): String =
    if (lemma.start <= edit._1.start && edit._1.stop <= lemma.stop) lemma.replace_all(List(edit)) else ""


  /* findings */

  override def read(checked: Pide.Checked, options: Options): List[Finding] = {
    val theories = checked.snapshots.map(s => s -> Cmd.read(s.node))
    val expected = theories.flatMap({ case (_, cmds) => expecting(cmds) }).toSet
    for {
      (snapshot, cmds) <- theories
      finding <- read_theory(snapshot, cmds, checked.lemmas.filter(_.theory == snapshot.node_name), expected)
    } yield finding
  }

  /* A command outside every lemma stands alone. */
  private def read_theory(snapshot: Document.Snapshot, cmds: List[Cmd], lemmas: List[Lemma],
      expected: Set[String]): List[Finding] = {
    val text = snapshot.node.source
    lazy val lines = Line.Document(text)
    for ((cmd, i) <- cmds.zipWithIndex if i > 0 && diagnostic(cmd)) yield {
      val lemma =
        lemmas.find(_.cmds.exists(_.command.id == cmd.command.id))
          .getOrElse(Lemma(snapshot.node_name, text, lines, cmds(i - 1), List(cmd), ok = true))
      finding(lemma, cmd, time(snapshot, cmd), expected)
    }
  }

  private def finding(lemma: Lemma, cmd: Cmd, time: Time, expected: Set[String]): Finding = {
    val what = category(cmd, expected)
    val languages = compiled(cmd)
    val compiling = if (languages.isEmpty) "" else ", compiling " + languages.mkString(" and ")
    val message = "`" + short(lemma, cmd) + "` takes " + time.ms + " ms" + compiling + ": " + advice(what, lemma, expected)
    val edit = if (what == "exploration") Some(delete(lemma, cmd, expected)) else None
    Finding(name, lemma, lemma.line(cmd.range.start), message, edit.map(fixed(lemma, _)), edit)
  }

  private def advice(what: String, lemma: Lemma, expected: Set[String]): String =
    what match {
      case "exploration" if exploring(lemma, expected) => "it proves nothing, delete it with its `lemma ... oops` (-F does)"
      case "exploration" => "it proves nothing, delete it (-F does)"
      case "test" => "if it is a test, move it to a test session, so that sessions importing this one do not wait for it"
      case _ => "it only prints, delete it"
    }

  /* The command's first line, cut short. */
  private def short(lemma: Lemma, cmd: Cmd): String = {
    val source = cmd.range.substring(lemma.text)
    val line = source.takeWhile(_ != '\n')
    if (line.length > 60) line.take(57) + "..." else if (line.length < source.length) line + " ..." else line
  }


  /* lint interface */

  def ask(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Pide.Question] = Nil

  def report(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] = Nil
}
