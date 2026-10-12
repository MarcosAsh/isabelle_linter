/* unused: facts, `have`s, `apply`s and assumptions a lemma does not need */

package isabelle.isabelle_linter

import isabelle._


object Unused extends Lint {
  val name = "unused"

  /* questions still to ask, or the unneeded pieces */
  type Result = Either[List[Pide.Question], List[Piece]]

  /* the unneeded pieces, with the lemma's median times before and after the fix */
  type Timed = Either[List[Pide.Question], (List[Piece], Option[(Long, Long)])]


  /* Per lemma: check it as written (its time sets the budget), delete each piece alone, then all
    unneeded pieces together, else one at a time. Then retry the `have`s that the deletions may
    have freed. Assumptions come last and are reported but never part of the fix. Last, time the
    lemma with and without the fix, alone, as a deletion can make a proof slower. */

  def check(lemma: Lemma, answers: Pide.Answers, options: Options): Timed = {
    val timeout = Time.seconds(options.real("linter_timeout"))
    val original = rerun(lemma, "original", Nil, timeout)

    answers.get(original.key) match {
      case None => Left(List(original))
      case Some(a) if !a.closes => Right((Nil, None))
      case Some(a) =>
        val budget = Time.ms((a.ms * options.real("linter_factor")).toLong max 1000L min timeout.ms)
        new Search(lemma, answers, budget).run() match {
          case Left(questions) => Left(questions)
          case Right(pieces) => timed(lemma, pieces, budget, answers, options)
        }
    }
  }

  private def timed(lemma: Lemma, pieces: List[Piece], budget: Time, answers: Pide.Answers,
      options: Options): Timed = {
    val fixed = pieces.filterNot(_.kind == "assumption")
    if (fixed.isEmpty) Right((pieces, None))
    else {
      val q = Pide.Question(lemma.key + ":time", lemma.theory, lemma.before.command, "linter_runs",
        List(options.int("unused_runs").toString, lemma.without(Nil), lemma.without(fixed.map(_.range))),
        budget, serial = true)
      answers.get(q.key) match {
        case None => Left(List(q))
        case Some(t) => Right((pieces, if (t.closes) Some((t.ms, t.ms2)) else None))
      }
    }
  }

  private class Search(lemma: Lemma, answers: Pide.Answers, budget: Time) {
    def run(): Result = {
      val alone = lemma.pieces.map(p => p -> drop(List(p)))
      val missing = alone.map(_._2).filterNot(asked)
      if (missing.nonEmpty) return Left(missing)

      val (unneeded, needed) = alone.partition(x => answers(x._2.key).closes)
      val (assumptions, others) = unneeded.map(_._1).partition(_.kind == "assumption")
      val haves = needed.map(_._1).filter(_.kind == "have")
      for {
        kept <- combine(Nil, others)
        freed <- one_by_one(kept, Nil, haves)
        more <- combine(kept ::: freed, assumptions)
      } yield kept ::: freed ::: more
    }

    private def drop(pieces: List[Piece]): Pide.Question =
      rerun(lemma, pieces.map(lemma.pieces.indexOf(_)).sorted.mkString("drop:", ",", ""), pieces, budget)

    private def asked(q: Pide.Question): Boolean = answers.contains(q.key)

    /* on top of base: all pieces at once, else one at a time */
    private def combine(base: List[Piece], pieces: List[Piece]): Result =
      if (pieces.isEmpty) Right(Nil)
      else {
        val all = drop(base ::: pieces)
        answers.get(all.key) match {
          case None => Left(List(all))
          case Some(a) if a.closes => Right(pieces)
          case _ => one_by_one(base, Nil, pieces)
        }
      }

    @scala.annotation.tailrec
    private def one_by_one(base: List[Piece], keep: List[Piece], rest: List[Piece]): Result =
      rest match {
        case Nil => Right(keep)
        case p :: ps if (base ::: keep).exists(_.range.contains(p.range)) => one_by_one(base, keep, ps)
        case p :: ps =>
          val q = drop(base ::: keep ::: List(p))
          answers.get(q.key) match {
            case None => Left(List(q))
            case Some(a) => one_by_one(base, if (a.closes) keep :+ p else keep, ps)
          }
      }
  }

  /* the lemma with pieces deleted, re-run from the state before it */
  private def rerun(lemma: Lemma, key: String, pieces: List[Piece], timeout: Time): Pide.Question =
    Pide.Question(lemma.key + ":" + key, lemma.theory, lemma.before.command, "linter_run",
      List(lemma.without(pieces.map(_.range))), timeout)


  /* lint interface */

  def ask(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Pide.Question] =
    lemmas.flatMap(check(_, answers, options).left.getOrElse(Nil))

  def report(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] =
    for {
      lemma <- lemmas
      (pieces, times) <- check(lemma, answers, options).toOption.toList
      if pieces.nonEmpty
    } yield finding(lemma, pieces, times)

  private def finding(lemma: Lemma, pieces: List[Piece], times: Option[(Long, Long)]): Finding = {
    val (assumptions, others) = pieces.partition(_.kind == "assumption")

    val timing = times.toList.map({ case (before, after) =>
      "time: " + before + " ms as written, " + after + " ms with the fix (medians, alone)" })
    val lines =
      section("not needed:", others) ::: timing :::
      section("not needed, but removing them changes the statement:", assumptions)
    val fix = if (others.isEmpty) None else Some(lemma.without(others.map(_.range)))

    Finding(name, lemma, lemma.line, lines.mkString("\n"), fix)
  }

  private def section(title: String, pieces: List[Piece]): List[String] =
    if (pieces.isEmpty) Nil else title :: pieces.map(p => "  " + describe(p))

  private def describe(p: Piece): String = {
    val what =
      p.kind match {
        case "fact" => "fact `" + p.text + "`"
        case "have" => "`" + p.text + "` and its proof"
        case "apply" => "`" + p.text + "`"
        case _ => "assumption `" + p.text + "`"
      }
    what + " (line " + p.line + ")"
  }
}
