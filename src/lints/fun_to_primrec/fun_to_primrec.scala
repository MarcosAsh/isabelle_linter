/* The fun_to_primrec lint: a `fun` that `primrec` can define, which saves proving pattern
   completeness and termination. A slow `fun` that must stay is reported too. */

package isabelle.isabelle_linter

import isabelle._


object Fun_To_Primrec extends Lint {
  val name = "fun_to_primrec"

  /* primrec's medians against fun's, or a slow fun with the time of its pattern proof and why it stays. */
  sealed abstract class Outcome
  sealed case class Fix(before: Long, after: Long) extends Outcome
  sealed case class Slow(ms: Long, patterns: Option[Long], why: String) extends Outcome

  type Result = Either[List[Pide.Question], Option[Outcome]]


  /* `fun (in loc)` keeps its target; other options like `(domintros)` mean no edit. */
  def options_group(cmd: Cmd): List[Tok] =
    if (cmd.body.headOption.exists(_.is("("))) Syntax.take_group(cmd.body, "(", ")")._1 else Nil

  def target_only(cmd: Cmd): Boolean =
    options_group(cmd) match {
      case Nil => true
      case _ :: t :: _ => t.is("in")
      case _ => false
    }

  /* f, g of `fun f :: ... and g where`, and f_g, which names their joint facts. */
  def names(cmd: Cmd): List[String] = {
    val specs = cmd.body.drop(options_group(cmd).length).takeWhile(t => !(t.token.is_keyword && t.is("where")))
    val functions = Syntax.split_and(specs).map(spec => Library.perhaps_unquote(spec.head.source))
    if (functions.length > 1) functions :+ functions.mkString("_") else functions
  }

  def primrec(lemma: Lemma): String = {
    val keyword = lemma.cmds.head.tokens.head
    lemma.replace(keyword.range, "primrec")
  }

  /* What fun does before its termination proof. */
  def function(lemma: Lemma): String = {
    val cmd = lemma.cmds.head
    val keyword = cmd.tokens.head.range
    val edits =
      options_group(cmd) match {
        case Nil => List(keyword -> "function (sequential)")
        case group => List(keyword -> "function", Text.Range(group.last.range.stop) -> " (sequential)")
      }
    lemma.replace_all(edits) + " by pat_completeness auto"
  }


  /* Why primrec's facts may not do for a later use, if they may not. */
  def obstacle(lemma: Lemma, compared: Definitions.Compared): Option[String] = {
    val later = lemma.later
    val functions = names(lemma.cmds.head)
    def selected(fact: String): Option[String] =
      Downstream.find(later, ("(?<![\\w'])" + scala.util.matching.Regex.quote(fact) + "\\(").r)
    val fun_cases =
      Downstream.words(functions)
        .filter(regex => Downstream.commands(later, Set("fun_cases")).exists(regex.findFirstIn(_).isDefined))

    /* Other simp rules change later simp calls; f_def matters only where it is named. */
    val (simps, others) = compared.differ.partition(_.endsWith("simps"))
    if (simps.nonEmpty) Some("primrec proves other " + simps.mkString(", "))
    else Downstream.words(compared.missing ::: others).flatMap(Downstream.find(later, _)).map(word => "`" + word + "` later")
      .orElse(fun_cases.map(_ => "`fun_cases` later"))
      .orElse(compared.reordered.flatMap(selected).headOption
        .map(word => "`" + word + "` later, but primrec orders it differently"))
  }


  /* Per fun: run it as written, as primrec and as `function (sequential)`. It becomes primrec if
     nothing later uses a fact that only fun makes. */
  def check(lemma: Lemma, answers: Pide.Answers, options: Options): Result = {
    val cmd = lemma.cmds.head
    val edits = if (target_only(cmd)) List(primrec(lemma), function(lemma)) else Nil
    val question = Definitions.names(lemma, edits, options)

    answers.get(question.key) match {
      case None => Left(List(question))
      case Some(answer) if answer.verdict == "timeout" => Right(slow(answer, None, "it did not finish in time", options))
      case Some(answer) if !answer.closes => Right(None)
      case Some(answer) =>
        val as_primrec = Definitions.compared(answer, 1)
        val why =
          if (edits.isEmpty) Some("its options")
          else as_primrec.fold(Some("not primitive recursive"): Option[String])(obstacle(lemma, _))
        why match {
          case None => timed(lemma, answer, answers, options)
          case Some(reason) => Right(slow(answer, Definitions.compared(answer, 2).map(_.ms), reason, options))
        }
    }
  }

  private def slow(answer: Pide.Answer, patterns: Option[Long], why: String, options: Options): Option[Outcome] =
    if (answer.ms >= options.real("fun_slow") * 1000) Some(Slow(answer.ms, patterns, why)) else None

  private def timed(lemma: Lemma, original: Pide.Answer, answers: Pide.Answers, options: Options): Result = {
    val question = Definitions.timing(lemma, primrec(lemma), original, options)
    answers.get(question.key) match {
      case None => Left(List(question))
      case Some(timing) if Definitions.saves(timing, options) => Right(Some(Fix(timing.ms, timing.ms2)))
      case Some(_) => Right(slow(original, Definitions.compared(original, 2).map(_.ms), "primrec is not faster", options))
    }
  }


  override def targets(checked: Pide.Checked): List[Lemma] =
    checked.definitions.filter(definition => definition.ok && definition.cmds.head.name == "fun")

  def ask(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Pide.Question] =
    lemmas.flatMap(check(_, answers, options).left.getOrElse(Nil))

  def report(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] =
    for {
      lemma <- lemmas
      outcome <- check(lemma, answers, options).toOption.flatten.toList
    } yield finding(lemma, outcome)

  private def finding(lemma: Lemma, outcome: Outcome): Finding =
    outcome match {
      case Fix(before, after) =>
        val edit = lemma.cmds.head.tokens.head.range -> "primrec"
        val message = "`primrec` takes " + after + " ms instead of " + before + " ms for `fun` (medians, alone)"
        Finding(name, lemma, lemma.line, message, Some(lemma.replace_all(List(edit))), Some(edit))
      case Slow(ms, patterns, why) =>
        val split =
          patterns.map(pattern_ms =>
            "; its pattern proof alone takes " + pattern_ms + " ms, so termination about " + (ms - pattern_ms max 0) + " ms")
            .getOrElse("")
        Finding(name, lemma, lemma.line, "slow `fun`, " + ms + " ms" + split + "; stays fun: " + why)
    }
}
