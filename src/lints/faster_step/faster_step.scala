/* The faster_step lint: a `by` step that another method proves several times faster. Edits
   come from standard methods, the step's own facts, its subgoals and the simp rules it used. */

package isabelle.isabelle_linter

import isabelle._


object Faster_Step extends Lint {
  val name = "faster_step"

  /* A faster method, with the medians of the original and of it. */
  sealed case class Faster(method: String, medians: Medians)

  type Result = Either[List[Pide.Question], Option[Faster]]


  val methods: List[String] =
    List("simp", "auto", "blast", "fast", "fastforce", "force", "metis", "meson", "linarith", "presburger",
      "argo", "algebra")

  /* After `induction` or `cases`, these must close every subgoal left by the first method. */
  val closers: List[String] = List("simp_all", "auto", "(fastforce+)", "(force+)", "(blast+)")

  /* The standard methods, some with the step's own facts, and the step without each fact. */
  def candidates(step: Step): List[String] = {
    val swaps =
      step.split match {
        case Some((first, _)) => closing(step, first)
        case None => whole(step)
      }
    (swaps ::: dropping(step)).filterNot(_ == step.methods).distinct
  }

  /* Keep `induction` or `cases`, change what closes the subgoals. */
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

  /* The step's own methods without one of their facts. */
  def dropping(step: Step): List[String] = {
    val start = step.cmd.body.head.range.start

    def cut(fact: List[Tok]): String = {
      val before = step.methods.substring(0, fact.head.range.start - start).nn.stripTrailing.nn
      val after = step.methods.substring(fact.last.range.stop - start).nn.stripLeading.nn
      val joined = if (after.startsWith(")")) before + after else before + " " + after
      Syntax.tidy("by " + joined).stripPrefix("by ")
    }

    Syntax.method_facts(step.cmd.body).map(cut)
  }


  /* `by M1 M2` to `by M1 (C1, C2, ...)`, with the fastest closer for each subgoal of M1 */

  def subgoal_closers(step: Step): List[String] = fact_methods(step) ::: methods

  /* The answer gives the number n of subgoals and for each subgoal i the index sub_i of its closer. */
  def per_subgoal(step: Step, first: String, answer: Pide.Answer): Option[String] = {
    val closers = subgoal_closers(step)
    val n = answer.long("n").getOrElse(0L).toInt
    val chosen = (1 to n).toList.map(i => answer.long("sub" + i).map(index => closers(index.toInt)))

    if (n < 2 || chosen.exists(_.isEmpty)) None
    else {
      val texts = chosen.flatten
      Some(first + " (" + (texts.init.map(one_goal) :+ texts.last).mkString(", ") + ")")
    }
  }

  /* auto works on every subgoal, and [1] keeps it to the first; it needs parentheses, as `auto[1]`
     is auto with an argument. */
  def one_goal(method: String): String =
    if (method == "auto") "(auto)[1]"
    else if (method.startsWith("(auto ")) method + "[1]"
    else method


  /* `simp only:` with the rules the step's own proof used, after any `induction` or `cases` */

  val simp_methods: Set[String] = Set("simp", "simp_all", "auto", "fastforce", "force", "clarsimp")

  def uses_simp(step: Step): Boolean = step.cmd.body.exists(t => simp_methods(t.source))

  def simp_only(step: Step, answer: Pide.Answer): Option[String] =
    answer.get("rules").filter(rules => answer.closes && rules.nonEmpty).map(Symbol.encode).map { rules =>
      step.split match {
        case Some((first, _)) => first + " (simp_all only: " + rules + ")"
        case None if answer.long("subgoals").exists(_ > 1) => "(simp_all only: " + rules + ")"
        case None => "(simp only: " + rules + ")"
      }
    }


  /* Per step: time it as written, then search for a faster method if it is slow enough. */
  def check(lemma: Lemma, step: Step, answers: Pide.Answers, options: Options): Result = {
    val original = try_by(lemma, step, step.methods, Time.seconds(options.real("linter_timeout")))
    answers.get(original.key) match {
      case None => Left(List(original))
      case Some(answer) if !answer.closes || answer.ms < options.real("faster_step_slow") * 1000 => Right(None)
      case Some(answer) => search(lemma, step, answer, answers, options)
    }
  }

  /* Try each edit with the original's time over the speed-up as its limit, at least 1 ms, as the
     prover ignores a smaller one. The fastest is re-timed, since the first times are noisy. */
  private def search(lemma: Lemma, step: Step, original: Pide.Answer, answers: Pide.Answers,
      options: Options): Result = {
    val limit = Time.ms((original.ms / options.real("faster_step_speedup")).toLong max 1L)
    val split = step.split.map({ case (first, _) => first -> subgoals(lemma, step, first, limit) })
    val rules = if (uses_simp(step)) Some(used_rules(lemma, step, options)) else None
    val try0_question = if (options.bool("faster_step_try0")) Some(try0(lemma, step, options)) else None
    val tries = edits(step, split, rules, answers).map(method => method -> try_by(lemma, step, method, limit))
    val (exhaustive_sources, exhaustive_tries) =
      if (options.bool("faster_step_exhaustive")) exhaustive(lemma, step, split, rules, original, answers, options)
      else (Nil, Nil)
    val missing =
      (split.map(_._2).toList ::: rules.toList ::: try0_question.toList ::: tries.map(_._2) :::
        exhaustive_sources ::: exhaustive_tries.map(_._2)).filterNot(question => answers.contains(question.key))

    if (missing.nonEmpty) Left(missing)
    else {
      val try0_proof = try0_question.flatMap(question => try0_method(step, answers(question.key), limit))
      confirm(lemma, step, fastest(tries, answers), try0_proof, fastest(exhaustive_tries, answers), original,
        answers, options)
    }
  }

  /* The label of the fastest try that closes. */
  private def fastest[A](tries: List[(A, Pide.Question)], answers: Pide.Answers): Option[A] =
    tries.filter({ case (_, question) => answers(question.key).closes })
      .sortBy({ case (_, question) => answers(question.key).ms }).headOption.map(_._1)

  /* The fastest edit is re-timed, and so are try0's proof and the exhaustive winner if asked for;
     only the edit is reported, the others' timings are for the question log. */
  private def confirm(lemma: Lemma, step: Step, winner: Option[String], try0_proof: Option[String],
      exhaustive_winner: Option[String], original: Pide.Answer, answers: Pide.Answers, options: Options): Result = {
    val timings =
      (winner.toList ::: try0_proof.toList).distinct.map(timing(lemma, step, "time:", _, original, options)) :::
        exhaustive_winner.toList.map(timing(lemma, step, "exhaustive:time:", _, original, options))

    timings.filterNot(question => answers.contains(question.key)) match {
      case Nil => Right(winner.flatMap(method => faster(method, answers(key(lemma, step, "time:" + method)), options)))
      case missing => Left(missing)
    }
  }

  /* Each run gets twice the original's time. */
  private def timing(lemma: Lemma, step: Step, mark: String, method: String, original: Pide.Answer,
      options: Options): Pide.Question = {
    val runs = options.int("faster_step_runs").toString
    Pide.Question(key(lemma, step, mark + method), lemma.theory, step.goal.command, "linter_time",
      List(runs, step.methods, method), Time.ms(original.ms * 2 max Pide.min_limit_ms), serial = true)
  }

  private def faster(method: String, timing: Pide.Answer, options: Options): Option[Faster] =
    if (timing.closes && timing.ms2 * options.real("faster_step_speedup") < timing.ms)
      Some(Faster(method, timing.medians))
    else None

  /* The per-subgoal and `simp only:` edits join the others once their questions are answered. */
  private def edits(step: Step, split: Option[(String, Pide.Question)], rules: Option[Pide.Question],
      answers: Pide.Answers): List[String] = {
    val subgoal_edit =
      for {
        (first, question) <- split
        answer <- answers.get(question.key)
        method <- per_subgoal(step, first, answer)
      } yield method
    val simp_edit = rules.flatMap(question => answers.get(question.key)).flatMap(simp_only(step, _))
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


  /* The exhaustive baseline, for the question log: every edit of every operator whatever the step's
     shape, with the original's time as limit; returns the questions the edits come from, and the tries. */
  private def exhaustive(lemma: Lemma, step: Step, split: Option[(String, Pide.Question)],
      simp_rules: Option[Pide.Question], original: Pide.Answer, answers: Pide.Answers,
      options: Options): (List[Pide.Question], List[(String, Pide.Question)]) = {
    val limit = Time.ms(original.ms max 1L)
    val rules =
      simp_rules.getOrElse(used_rules(lemma, step, options).copy(key = key(lemma, step, "exhaustive:rules")))

    /* Each closer is timed on each subgoal in full, not within the best time so far. */
    val closers = subgoal_closers(step).zipWithIndex
    val closer_tries =
      for {
        (first, question) <- split.toList
        n <- answers.get(question.key).flatMap(_.long("n")).toList
        i <- (1 to n.toInt).toList
      } yield i -> closers.map({ case (closer, index) => index -> subgoal(lemma, step, first, i, closer, limit) })
    val all_answered = closer_tries.forall(_._2.forall({ case (_, question) => answers.contains(question.key) }))

    val subgoal_edit =
      for {
        (first, _) <- split
        if all_answered
        chosen = closer_tries.flatMap({ case (i, tries) => fastest(tries, answers).map(index => ("sub" + i, index.toString)) })
        method <- per_subgoal(step, first, Pide.Answer("closes", ("n" -> closer_tries.length.toString) :: chosen))
      } yield method
    val methods =
      (edits(step, split, Some(rules), answers) ::: whole(step) ::: subgoal_edit.toList)
        .filterNot(_ == step.methods).distinct

    val tries =
      methods.map(method => method -> Pide.Question(key(lemma, step, "exhaustive:" + method), lemma.theory,
        step.goal.command, "linter_try", List(method), limit))
    (rules :: closer_tries.flatMap(_._2.map(_._2)), tries)
  }

  private def subgoal(lemma: Lemma, step: Step, first: String, i: Int, closer: String, limit: Time): Pide.Question =
    Pide.Question(key(lemma, step, "exhaustive:sub" + i + ":" + closer), lemma.theory, step.goal.command,
      "linter_subgoal", List(first, i.toString, closer), limit)


  /* The try0 baseline: Isabelle's try0 on the same goal. Its fastest proof is re-timed like an
     edit if try0 timed it under the same limit. */

  private def try0(lemma: Lemma, step: Step, options: Options): Pide.Question = {
    val per_method = Time.seconds(options.real("faster_step_try0_timeout")).ms.toString
    Pide.Question(key(lemma, step, "try0"), lemma.theory, step.goal.command, "linter_try0",
      List(per_method), Time.seconds(options.real("linter_timeout")))
  }

  private def try0_method(step: Step, answer: Pide.Answer, limit: Time): Option[String] =
    answer.get("method").filter(method =>
      answer.closes && method != step.methods && answer.long("method_ms").exists(_ < limit.ms))


  /* lint interface */

  def ask(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Pide.Question] =
    for {
      lemma <- lemmas
      step <- lemma.steps
      question <- check(lemma, step, answers, options).left.getOrElse(Nil)
    } yield question

  def report(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] =
    for {
      lemma <- lemmas
      step <- lemma.steps
      faster <- check(lemma, step, answers, options).toOption.flatten.toList
    } yield {
      val message = "`by " + faster.method + "` takes " + faster.medians.after + " ms instead of " +
        faster.medians.before + " ms for `by " + step.methods + "`"
      val edit = step.cmd.range -> ("by " + faster.method)
      Finding(name, lemma, lemma.line(step.cmd.range.start), message, Some(lemma.replace_all(List(edit))), Some(edit))
    }
}
