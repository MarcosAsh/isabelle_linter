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

  /* they must close every subgoal left by the first method */
  val closers: List[String] = List("simp_all", "auto", "(fastforce+)", "(force+)", "(blast+)")

  /* the standard methods, some with the step's own facts, and the step without each fact */
  def candidates(step: Step): List[String] = {
    val swaps =
      step.split match {
        case Some((first, _)) => closing(step, first)
        case None => whole(step)
      }
    (swaps ::: dropping(step)).filterNot(_ == step.methods).distinct
  }

  /* keep `induction` or `cases`, change what closes the subgoals */
  def closing(step: Step, first: String): List[String] = {
    val facts = step.facts.mkString(" ")
    val with_facts =
      if (facts.isEmpty) Nil
      else List("(simp_all add: " + facts + ")", "(auto simp: " + facts + ")",
        "((fastforce simp: " + facts + ")+)", "((force simp: " + facts + ")+)")

    (with_facts ::: closers).map(first + " " + _)
  }

  def whole(step: Step): List[String] = fact_methods(step) ::: methods

  def fact_methods(step: Step): List[String] = {
    val facts = step.facts.mkString(" ")
    if (facts.isEmpty) Nil
    else
      List("metis " + facts, "simp add: " + facts, "auto simp: " + facts, "fastforce simp: " + facts,
        "force simp: " + facts, "blast intro: " + facts).map("(" + _ + ")")
  }

  /* the step's own methods without one of their facts */
  def dropping(step: Step): List[String] = {
    val start = step.cmd.body.head.range.start

    def cut(fact: List[Tok]): String = {
      val before = step.methods.substring(0, fact.head.range.start - start).stripTrailing
      val after = step.methods.substring(fact.last.range.stop - start).stripLeading
      val joined = if (after.startsWith(")")) before + after else before + " " + after
      Syntax.tidy("by " + joined).stripPrefix("by ")
    }

    Syntax.method_facts(step.cmd.body).map(cut)
  }


  /* `by M1 M2` to `by M1 (C1, C2, ...)`, with the fastest closer for each subgoal of M1 */

  def subgoal_closers(step: Step): List[String] = fact_methods(step) ::: methods

  def per_subgoal(step: Step, first: String, answer: Pide.Answer): Option[String] = {
    val closers = subgoal_closers(step)
    val n = answer.long("n").getOrElse(0L).toInt
    val chosen = (1 to n).toList.map(i => answer.long("sub" + i).map(j => closers(j.toInt)))

    if (n < 2 || chosen.exists(_.isEmpty)) None
    else {
      val texts = chosen.flatten
      Some(first + " (" + (texts.init.map(one_goal) :+ texts.last).mkString(", ") + ")")
    }
  }

  /* auto works on every subgoal; [1] keeps it to the first, and needs parentheses (`auto[1]` is
    auto with an argument) */
  def one_goal(method: String): String =
    if (method == "auto") "(auto)[1]"
    else if (method.startsWith("(auto ")) method + "[1]"
    else method


  /* `simp only:` with the rules the step's own proof used, after any `induction` or `cases` */

  val simp_methods: Set[String] = Set("simp", "simp_all", "auto", "fastforce", "force", "clarsimp")

  def uses_simp(step: Step): Boolean = step.cmd.body.exists(t => simp_methods(t.source))

  def simp_only(step: Step, answer: Pide.Answer): Option[String] =
    answer.get("rules").filter(rules => answer.closes && rules.nonEmpty).map { rules =>
      step.split match {
        case Some((first, _)) => first + " (simp_all only: " + rules + ")"
        case None if answer.long("subgoals").exists(_ > 1) => "(simp_all only: " + rules + ")"
        case None => "(simp only: " + rules + ")"
      }
    }


  /* Per step: time it, try the candidates with the original time over the speed-up as their limit,
    then re-time the fastest against the original a few times, alone (the first times are noisy). */

  def check(lemma: Lemma, step: Step, answers: Pide.Answers, options: Options): Result = {
    val speedup = options.real("faster_step_speedup")
    val original = try_by(lemma, step, step.methods, Time.seconds(options.real("linter_timeout")))

    answers.get(original.key) match {
      case None => Left(List(original))
      case Some(a) if !a.closes || a.ms < options.real("faster_step_slow") * 1000 => Right(None)
      case Some(a) =>
        val limit = Time.ms((a.ms / speedup).toLong max 1L)
        val split = step.split.map({ case (first, _) => first -> subgoals(lemma, step, first, limit) })
        val rules = if (uses_simp(step)) Some(used_rules(lemma, step, options)) else None
        val tries = edits(step, split, rules, answers).map(m => m -> try_by(lemma, step, m, limit))
        val missing =
          (split.map(_._2).toList ::: rules.toList ::: tries.map(_._2)).filterNot(q => answers.contains(q.key))

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
        List(runs, step.methods, method), Time.ms(original.ms * 2 max 1000L), serial = true)

    answers.get(timing.key) match {
      case None => Left(List(timing))
      case Some(t) if t.closes && t.ms2 * options.real("faster_step_speedup") < t.ms =>
        Right(Some((method, t.ms, t.ms2)))
      case _ => Right(None)
    }
  }

  /* the per-subgoal and `simp only:` edits join the others once their questions are answered */
  private def edits(step: Step, split: Option[(String, Pide.Question)], rules: Option[Pide.Question],
      answers: Pide.Answers): List[String] = {
    val subgoal_edit =
      for {
        (first, q) <- split
        answer <- answers.get(q.key)
        method <- per_subgoal(step, first, answer)
      } yield method
    val simp_edit = rules.flatMap(q => answers.get(q.key)).flatMap(simp_only(step, _))
    (candidates(step) ::: subgoal_edit.toList ::: simp_edit.toList).filterNot(_ == step.methods).distinct
  }

  private def subgoals(lemma: Lemma, step: Step, first: String, limit: Time): Pide.Question =
    Pide.Question(key(lemma, step, "subgoals"), lemma.theory, step.goal.command, "linter_subgoals",
      first :: subgoal_closers(step), limit)

  private def used_rules(lemma: Lemma, step: Step, options: Options): Pide.Question =
    Pide.Question(key(lemma, step, "rules"), lemma.theory, step.goal.command, "linter_used_rules",
      List(step.methods), Time.seconds(options.real("linter_timeout")))

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
