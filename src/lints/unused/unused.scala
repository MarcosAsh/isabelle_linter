/* The unused lint: facts, `have`s, `apply`s and assumptions that a lemma does not need, found by
   re-running the lemma without them. */

package isabelle.isabelle_linter

import isabelle._


object Unused extends Lint {
  val name = "unused"

  /* Questions still to ask, or the unneeded pieces. */
  type Result = Either[List[Pide.Question], List[Piece]]

  /* The unneeded pieces, with the lemma's medians as written and fixed if they were timed. */
  sealed case class Unneeded(pieces: List[Piece], medians: Option[Medians])


  /* Per lemma: run it as written, which sets the budget; delete each piece alone, then all the
     unneeded pieces at once, else one at a time. */
  def check(lemma: Lemma, answers: Pide.Answers, options: Options): Either[List[Pide.Question], Unneeded] = {
    val timeout = Time.seconds(options.real("linter_timeout"))
    val original = rerun(lemma, "original", Nil, timeout)

    answers.get(original.key) match {
      case None => Left(List(original))
      case Some(answer) if !answer.closes => Right(Unneeded(Nil, None))
      case Some(answer) =>
        val budget = Time.ms(Pide.budget(answer, options) min timeout.ms)
        new Search(lemma, answers, budget, options.int("unused_ahead")).run() match {
          case Left(questions) => Left(questions)
          case Right(pieces) => timed(lemma, pieces, budget, answers, options)
        }
    }
  }

  /* A deletion can make a proof slower, so time the lemma alone with and without the fix. */
  private def timed(lemma: Lemma, pieces: List[Piece], budget: Time, answers: Pide.Answers,
      options: Options): Either[List[Pide.Question], Unneeded] = {
    val fixed = pieces.filterNot(_.kind == "assumption")
    if (fixed.isEmpty) Right(Unneeded(pieces, None))
    else {
      val question = Pide.Question(lemma.key + ":time", lemma.theory, lemma.before.command, "linter_runs",
        List(options.int("unused_runs").toString, lemma.without(Nil), lemma.without(fixed.map(_.range))),
        budget, serial = true)
      answers.get(question.key) match {
        case None => Left(List(question))
        case Some(answer) => Right(Unneeded(pieces, if (answer.closes) Some(answer.medians) else None))
      }
    }
  }

  private class Search(lemma: Lemma, answers: Pide.Answers, budget: Time, ahead: Int) {
    /* The deletions may free `have`s that were needed before. Assumptions come last: they are
       reported, but never part of the fix. */
    def run(): Result = {
      val alone = lemma.pieces.map(piece => piece -> drop(List(piece)))
      val missing = alone.map(_._2).filterNot(asked)
      if (missing.nonEmpty) return Left(missing)

      val (unneeded, needed) = alone.partition({ case (_, question) => answers(question.key).closes })
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

    private def asked(question: Pide.Question): Boolean = answers.contains(question.key)

    /* On top of base: all pieces at once, else one at a time. */
    private def combine(base: List[Piece], pieces: List[Piece]): Result =
      if (pieces.isEmpty) Right(Nil)
      else {
        val all = drop(base ::: pieces)
        answers.get(all.key) match {
          case None => Left(List(all))
          case Some(answer) if answer.closes => Right(pieces)
          case _ => one_by_one(base, Nil, pieces)
        }
      }

    @scala.annotation.tailrec
    private def one_by_one(base: List[Piece], kept: List[Piece], rest: List[Piece]): Result =
      rest match {
        case Nil => Right(kept)
        case piece :: more if inside(base ::: kept, piece) => one_by_one(base, kept, more)
        case piece :: more =>
          answers.get(drop(base ::: kept ::: List(piece)).key) match {
            case None => Left(guesses(base, kept, rest))
            case Some(answer) => one_by_one(base, if (answer.closes) kept :+ piece else kept, more)
          }
      }

    /* The next questions of one_by_one, each as if the ones before it can go. While pieces can go
       they are asked anyway, so a lemma takes a round per needed piece, not per piece. */
    private def guesses(base: List[Piece], kept: List[Piece], rest: List[Piece]): List[Pide.Question] =
      rest.foldLeft((kept, List.empty[Pide.Question])) {
        case ((guessed, questions), piece) if questions.length >= (ahead max 1) || inside(base ::: guessed, piece) =>
          (guessed, questions)
        case ((guessed, questions), piece) =>
          (guessed :+ piece, questions :+ drop(base ::: guessed ::: List(piece)))
      }._2

    private def inside(pieces: List[Piece], piece: Piece): Boolean = pieces.exists(_.range.contains(piece.range))
  }

  /* The lemma with pieces deleted, re-run from the state before it. */
  private def rerun(lemma: Lemma, key: String, pieces: List[Piece], timeout: Time): Pide.Question =
    Pide.Question(lemma.key + ":" + key, lemma.theory, lemma.before.command, "linter_run",
      List(lemma.without(pieces.map(_.range))), timeout)


  /* lint interface */

  def ask(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Pide.Question] =
    lemmas.flatMap(check(_, answers, options).left.getOrElse(Nil))

  def report(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] =
    for {
      lemma <- lemmas
      unneeded <- check(lemma, answers, options).toOption.toList
      if unneeded.pieces.nonEmpty
    } yield finding(lemma, unneeded)

  private def finding(lemma: Lemma, unneeded: Unneeded): Finding = {
    val (assumptions, others) = unneeded.pieces.partition(_.kind == "assumption")

    val timing = unneeded.medians.toList.map(medians =>
      "time: " + medians.before + " ms as written, " + medians.after + " ms with the fix (medians, alone)")
    val lines =
      section("not needed:", others) ::: timing :::
      section("not needed, but removing them changes the statement:", assumptions)
    val fix = if (others.isEmpty) None else Some(lemma.without(others.map(_.range)))

    Finding(name, lemma, lemma.line, lines.mkString("\n"), fix)
  }

  private def section(title: String, pieces: List[Piece]): List[String] =
    if (pieces.isEmpty) Nil else title :: pieces.map(piece => "  " + describe(piece))

  private def describe(piece: Piece): String = {
    val what =
      piece.kind match {
        case "fact" => "fact `" + piece.text + "`"
        case "have" => "`" + piece.text + "` and its proof"
        case "apply" => "`" + piece.text + "`"
        case _ => "assumption `" + piece.text + "`"
      }
    what + " (line " + piece.line + ")"
  }
}
