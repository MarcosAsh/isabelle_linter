/* faster_step: a `by` step that another method proves several times faster */

package isabelle.isabelle_linter

import isabelle._


object Faster_Step extends Lint {
  val name = "faster_step"

  /* questions still to ask, or the faster method with both median times */
  type Result = Either[List[Pide.Question], Option[(String, Long, Long)]]


  val methods: List[String] =
    List("simp", "auto", "blast", "fast", "fastforce", "force", "metis", "meson", "linarith", "presburger",
      "argo", "algebra")

  /* the standard methods, and some that get the step's own facts */
  def candidates(step: Step): List[String] = {
    val facts = step.facts.mkString(" ")
    val with_facts =
      if (facts.isEmpty) Nil
      else
        List("metis " + facts, "simp add: " + facts, "auto simp: " + facts, "fastforce simp: " + facts,
          "force simp: " + facts, "blast intro: " + facts).map("(" + _ + ")")

    (with_facts ::: methods).filterNot(_ == step.methods).distinct
  }


  /* Per step: time it, try the candidates with the original time over the speed-up as their limit,
    then re-time the fastest against the original a few times (the first times are noisy). */

  def check(lemma: Lemma, step: Step, answers: Pide.Answers, options: Options): Result = {
    val speedup = options.real("faster_step_speedup")
    val original = try_by(lemma, step, step.methods, Time.seconds(options.real("linter_timeout")))

    answers.get(original.key) match {
      case None => Left(List(original))
      case Some(a) if !a.closes || a.ms < options.real("faster_step_slow") * 1000 => Right(None)
      case Some(a) =>
        val limit = Time.ms((a.ms / speedup).toLong max 1L)
        val tries = candidates(step).map(m => m -> try_by(lemma, step, m, limit))
        val missing = tries.map(_._2).filterNot(q => answers.contains(q.key))

        if (missing.nonEmpty) Left(missing)
        else {
          val closing = tries.filter(t => answers(t._2.key).closes).sortBy(t => answers(t._2.key).ms)
          closing.headOption match {
            case None => Right(None)
            case Some((m, _)) => confirm(lemma, step, m, a, answers, options)
          }
        }
    }
  }

  private def confirm(lemma: Lemma, step: Step, method: String, original: Pide.Answer,
      answers: Pide.Answers, options: Options): Result = {
    val runs = options.int("faster_step_runs").toString
    val timing =
      Pide.Question(key(lemma, step, "time:" + method), lemma.theory, step.goal.command, "linter_time",
        List(runs, step.methods, method), Time.ms(original.ms * 2 max 1000L))

    answers.get(timing.key) match {
      case None => Left(List(timing))
      case Some(t) if t.closes && t.ms2 * options.real("faster_step_speedup") < t.ms =>
        Right(Some((method, t.ms, t.ms2)))
      case _ => Right(None)
    }
  }

  private def key(lemma: Lemma, step: Step, what: String): String =
    lemma.key + ":" + step.cmd.offset + ":" + what

  private def try_by(lemma: Lemma, step: Step, methods: String, timeout: Time): Pide.Question =
    Pide.Question(key(lemma, step, methods), lemma.theory, step.goal.command, "linter_try", List(methods), timeout)


  /* lint interface */

  def ask(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Pide.Question] =
    for {
      lemma <- lemmas
      step <- lemma.steps
      q <- check(lemma, step, answers, options).left.getOrElse(Nil)
    } yield q

  def report(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] =
    for {
      lemma <- lemmas
      step <- lemma.steps
      (method, before, after) <- check(lemma, step, answers, options).toOption.flatten.toList
    } yield {
      val message = "`by " + method + "` takes " + after + " ms instead of " + before + " ms for `by " + step.methods + "`"
      Finding(name, lemma, lemma.line(step.cmd.range.start), message, Some(lemma.replace(step.cmd.range, "by " + method)))
    }
}
