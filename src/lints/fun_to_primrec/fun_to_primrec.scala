/* fun_to_primrec: a `fun` that `primrec` can define, without proving patterns and termination */

package isabelle.isabelle_linter

import isabelle._


object Fun_To_Primrec extends Lint {
  val name = "fun_to_primrec"

  /* primrec's times against fun's, or a slow fun with its pattern time and why it stays */
  sealed abstract class Outcome
  sealed case class Fix(before: Long, after: Long) extends Outcome
  sealed case class Slow(ms: Long, patterns: Option[Long], why: String) extends Outcome

  type Result = Either[List[Pide.Question], Option[Outcome]]


  /* `fun (in loc)` keeps its target; other options like `(domintros)` mean no edit */
  def options_group(cmd: Cmd): List[Tok] =
    if (cmd.body.headOption.exists(_.is("("))) Syntax.take_group(cmd.body, "(", ")")._1 else Nil

  def target_only(cmd: Cmd): Boolean =
    options_group(cmd) match {
      case Nil => true
      case _ :: t :: _ => t.is("in")
      case _ => false
    }

  /* f, g of `fun f :: ... and g where`, and f_g, which names their joint facts */
  def names(cmd: Cmd): List[String] = {
    val specs = cmd.body.drop(options_group(cmd).length).takeWhile(t => !(t.token.is_keyword && t.is("where")))
    val fs = Syntax.split_and(specs).map(spec => Library.perhaps_unquote(spec.head.source))
    if (fs.length > 1) fs :+ fs.mkString("_") else fs
  }

  def primrec(lemma: Lemma): String = {
    val keyword = lemma.cmds.head.tokens.head
    lemma.replace(keyword.range, "primrec")
  }

  /* what fun does before its termination proof */
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


  def obstacle(lemma: Lemma, c: Definitions.Compared): Option[String] = {
    val later = lemma.later
    val fs = names(lemma.cmds.head)
    def selected(fact: String): Option[String] =
      Downstream.find(later, ("(?<![\\w'])" + scala.util.matching.Regex.quote(fact) + "\\(").r)
    val fun_cases =
      Downstream.words(fs).filter(w => Downstream.commands(later, Set("fun_cases")).exists(w.findFirstIn(_).isDefined))

    /* other simp rules change later simp calls; f_def matters only where named */
    val (simps, others) = c.differ.partition(_.endsWith("simps"))
    if (simps.nonEmpty) Some("primrec proves other " + simps.mkString(", "))
    else Downstream.words(c.missing ::: others).flatMap(Downstream.find(later, _)).map(w => "`" + w + "` later")
      .orElse(fun_cases.map(_ => "`fun_cases` later"))
      .orElse(c.reordered.flatMap(selected).headOption.map(w => "`" + w + "` later, but primrec orders it differently"))
  }


  /* per fun: as written, as primrec, as `function (sequential)`; primrec if no fun-only facts used */

  def check(lemma: Lemma, answers: Pide.Answers, options: Options): Result = {
    val cmd = lemma.cmds.head
    val edits = if (target_only(cmd)) List(primrec(lemma), function(lemma)) else Nil
    val q = Definitions.names(lemma, edits, options)

    answers.get(q.key) match {
      case None => Left(List(q))
      case Some(a) if a.verdict == "timeout" => Right(slow(a, None, "it did not finish in time", options))
      case Some(a) if !a.closes => Right(None)
      case Some(a) =>
        val as_primrec = Definitions.compared(a, 1)
        val why =
          if (edits.isEmpty) Some("its options")
          else as_primrec.fold(Some("not primitive recursive"): Option[String])(obstacle(lemma, _))
        why match {
          case None => timed(lemma, a, answers, options)
          case Some(w) => Right(slow(a, Definitions.compared(a, 2).map(_.ms), w, options))
        }
    }
  }

  private def slow(a: Pide.Answer, patterns: Option[Long], why: String, options: Options): Option[Outcome] =
    if (a.ms >= options.real("fun_slow") * 1000) Some(Slow(a.ms, patterns, why)) else None

  private def timed(lemma: Lemma, original: Pide.Answer, answers: Pide.Answers, options: Options): Result = {
    val q = Definitions.timing(lemma, primrec(lemma), original, options)
    answers.get(q.key) match {
      case None => Left(List(q))
      case Some(t) if Definitions.saves(t, options) => Right(Some(Fix(t.ms, t.ms2)))
      case Some(_) => Right(slow(original, Definitions.compared(original, 2).map(_.ms), "primrec is not faster", options))
    }
  }


  override def targets(checked: Pide.Checked): List[Lemma] =
    checked.definitions.filter(d => d.ok && d.cmds.head.name == "fun")

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
        val split = patterns.map(p => "; its pattern proof alone takes " + p + " ms, so termination about " + (ms - p max 0) + " ms").getOrElse("")
        Finding(name, lemma, lemma.line, "slow `fun`, " + ms + " ms" + split + "; stays fun: " + why)
    }
}
