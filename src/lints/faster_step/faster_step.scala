/* faster_step: a `by` step that a standard method proves several times faster */

package isabelle.isabelle_linter

import isabelle._


object Faster_Step extends Lint {
  val name = "faster_step"

  val candidates: List[String] =
    List("simp", "auto", "blast", "fast", "fastforce", "force", "metis", "meson", "linarith", "presburger",
      "argo", "algebra")

  /* round 1: every step as written */
  private def original(step: Pide.Step, options: Options): Pide.Question =
    Pide.Question(step, step.methods, Time.seconds(options.real("faster_step_timeout")))

  /* the step checks as written and is slow */
  private def slow(step: Pide.Step, answers: Pide.Answers, options: Options): Option[Pide.Answer] =
    answers.get(original(step, options).key)
      .filter(a => a.closes && a.ms >= options.real("faster_step_slow") * 1000)

  /* round 2: on slow steps, every candidate with the original time over the speed-up as its limit,
    so a candidate that closes the goal is faster by construction */
  def ask(steps: List[Pide.Step], answers: Pide.Answers, options: Options): List[Pide.Question] =
    steps.flatMap { step =>
      slow(step, answers, options) match {
        case None => List(original(step, options))
        case Some(a) =>
          val limit = Time.ms((a.ms / options.real("faster_step_speedup")).toLong)
          for (m <- candidates if m != step.methods) yield Pide.Question(step, m, limit)
      }
    }

  def report(steps: List[Pide.Step], answers: Pide.Answers, options: Options): List[Pide.Finding] =
    for {
      step <- steps
      orig <- slow(step, answers, options).toList
      faster = candidates.flatMap(m => answers.get((step.command.id, m)).filter(_.closes).map(m -> _))
      (method, a) <- faster.sortBy(_._2.ms).headOption.toList
    } yield Pide.Finding(step,
      "`by " + method + "` checks in " + a.ms + " ms instead of " + orig.ms + " ms for `by " + step.methods + "`",
      method)
}
