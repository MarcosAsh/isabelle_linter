/* The simp_scope lint: [simp] rules that a `note` sets for a whole block, or that a step adds to
   its simp methods, where the steps need fewer. */

package isabelle.isabelle_linter

import isabelle._


object Simp_Scope extends Lint {
  val name = "simp_scope"

  /* A command whose methods read the simpset, with the notes in scope and its step. */
  sealed case class Use(cmd: Cmd, methods: List[Simp_Method], notes: List[Simp_Note], step: Option[Step]) {
    def own: List[List[Tok]] = methods.flatMap(_.sections).flatMap(_.facts)
  }

  /* A fact or one of its theorems. With own, it replaces the use's own fact at that offset;
     otherwise it is added to the use's methods. */
  sealed case class Rule(name: String, fact: String, own: Option[Int] = None)

  type Edits = List[(Text.Range, String)]

  sealed case class Fix(edits: Edits, medians: Medians)

  type Result = Either[List[Pide.Question], Option[Fix]]


  /* [simp] notes with the commands in their scope */

  def notes(lemma: Lemma): List[(Simp_Note, List[Cmd])] =
    for {
      (cmd, i) <- lemma.cmds.zipWithIndex
      note <- Simp_Text.note(lemma.text, cmd)
    } yield (note, Simp_Text.scope(lemma.cmds, i))

  val method_commands: Set[String] = Set("by", "apply", "proof", "qed")

  def uses(lemma: Lemma): List[Use] = {
    val scoped = notes(lemma)
    for {
      cmd <- lemma.cmds
      if method_commands(cmd.name)
      methods = Simp_Text.methods(cmd.body)
      in_scope = scoped.collect({ case (note, scope) if scope.contains(cmd) => note })
      use = Use(cmd, methods, in_scope, lemma.steps.find(_.cmd == cmd))
      if methods.nonEmpty && (in_scope.nonEmpty || (use.step.isDefined && use.own.nonEmpty))
    } yield use
  }


  private def text(lemma: Lemma, fact: List[Tok]): String = Simp_Text.source(lemma.text, fact)

  /* The facts a use may need: those of its notes, then its own. */
  private def slots(lemma: Lemma, use: Use): List[Rule] =
    use.notes.flatMap(_.facts).map(fact => Rule(fact, fact)) :::
      use.own.map(fact => Rule(text(lemma, fact), text(lemma, fact), Some(fact.head.range.start)))

  /* The theorem names of an answer property, None if unknown. */
  private def theorem_names(answer: Pide.Answer, property: String): Option[List[String]] =
    answer.get(property).filter(_ => answer.closes) match {
      case None | Some("*") => None
      case Some("-") => Some(Nil)
      case Some(names) => Some(Library.space_explode(' ', names))
    }

  /* What the proof used, as theorems or as whole facts. */
  def used(lemma: Lemma, use: Use, proof: Pide.Answer, members: Boolean): List[Rule] =
    slots(lemma, use).zipWithIndex.flatMap { case (slot, i) =>
      theorem_names(proof, "used" + i) match {
        case Some(Nil) => Nil
        case Some(names) if members => names.map(name => slot.copy(name = name))
        case _ => List(slot)
      }
    }

  /* A fact of which every theorem is kept stays whole. */
  def compress(lemma: Lemma, use: Use, proof: Pide.Answer, rules: List[Rule]): List[Rule] =
    slots(lemma, use).zipWithIndex.flatMap { case (slot, i) =>
      val of_slot = rules.filter(rule => rule.fact == slot.fact && rule.own == slot.own)
      theorem_names(proof, "all" + i) match {
        case Some(all) if all.nonEmpty && all.forall(name => of_slot.exists(_.name == name)) => List(slot)
        case _ => of_slot
      }
    }

  def keep_own(lemma: Lemma, use: Use): List[Rule] = slots(lemma, use).filter(_.own.isDefined)

  def all_notes(use: Use): List[Rule] =
    use.notes.flatMap(note => note.name.map(List(_)).getOrElse(note.facts)).map(fact => Rule(fact, fact))


  def edits(lemma: Lemma, use: Use, rules: List[Rule]): Edits = {
    val add = by_name(use.notes, rules.filter(_.own.isEmpty).map(_.name).distinct)
    def own(fact: List[Tok]): List[String] = rules.filter(_.own.contains(fact.head.range.start)).map(_.name)
    use.methods.flatMap(Simp_Text.rewrite(lemma.text, _, own, add))
  }

  /* All facts of a named note go back in under its name. */
  private def by_name(notes: List[Simp_Note], add: List[String]): List[String] =
    notes.foldLeft(add) { (names, note) =>
      note.name match {
        case Some(name) if note.facts.forall(names.contains) => names.filterNot(note.facts.contains) :+ name
        case _ => names
      }
    }

  def methods(lemma: Lemma, use: Use, rules: List[Rule]): String = {
    val start = use.cmd.body.head.range.start
    Lemma.edit(lemma.text.substring(start, use.cmd.range.stop).nn, start, edits(lemma, use, rules))
  }


  /* Per lemma: ask what each step used, drop rules one by one, re-run the lemma with each fix from
     fine to coarse, and time the first that works. */
  def check(lemma: Lemma, answers: Pide.Answers, options: Options): Result = {
    val lemma_notes = notes(lemma).map(_._1)
    val lemma_uses = uses(lemma)
    val original = rerun(lemma, "original", lemma.source, Time.seconds(options.real("linter_timeout")))

    if (lemma_notes.isEmpty && lemma_uses.isEmpty) Right(None)
    else {
      answers.get(original.key) match {
        case None => Left(List(original))
        case Some(answer) if !answer.closes || answer.ms < options.real("simp_scope_slow") * 1000 => Right(None)
        case Some(answer) => new Search(lemma, lemma_notes, lemma_uses, answer, answers, options).run()
      }
    }
  }

  private class Search(lemma: Lemma, notes: List[Simp_Note], uses: List[Use], original: Pide.Answer,
      answers: Pide.Answers, options: Options) {
    private val timeout = Time.seconds(options.real("linter_timeout"))
    private val budget = Time.ms(Pide.budget(original, options) min timeout.ms)
    private val steps = uses.filter(_.step.isDefined)

    def run(): Result =
      for {
        found <- answered(steps.map(used_question))
        proofs = steps.zip(found).toMap
        kept <- combined(steps.map(use => use -> greedy(use, proofs(use))))
        fix <- first_closing(candidates(proofs, kept.toMap).zipWithIndex)
        result <- timed(fix)
      } yield result

    private def answered(questions: List[Pide.Question]): Either[List[Pide.Question], List[Pide.Answer]] =
      questions.filterNot(question => answers.contains(question.key)) match {
        case Nil => Right(questions.map(question => answers(question.key)))
        case missing => Left(missing)
      }

    /* The results of all uses, or the questions any of them still asks. */
    private def combined[A](results: List[(Use, Either[List[Pide.Question], A])]): Either[List[Pide.Question], List[(Use, A)]] =
      results.flatMap(_._2.left.getOrElse(Nil)) match {
        case Nil => Right(results.map({ case (use, result) => use -> result.toOption.get }))
        case missing => Left(missing)
      }

    /* The used rules minus each one the step does without alone. The base try decides for all of
       them, so it gets the lemma's budget, and is skipped when it is the step as written. */
    private def greedy(use: Use, proof: Pide.Answer): Either[List[Pide.Question], List[Rule]] = {
      val rules = used(lemma, use, proof, members = true)
      val limit = Time.ms(proof.ms * 2 max Pide.min_limit_ms min timeout.ms)
      def try_rules(rules: List[Rule], limit: Time): Pide.Question =
        try_question(use, compress(lemma, use, proof, rules), limit)

      if (rules.isEmpty || rules.length > options.int("simp_scope_greedy")) Right(rules)
      else {
        val base = if (as_written(use, proof, rules)) None else Some(try_rules(rules, budget))
        val without_each = rules.map(rule => rule -> try_rules(rules.filterNot(_ == rule), limit))
        def can_go(rule: Rule): Boolean =
          without_each.exists({ case (dropped, question) => dropped == rule && answers(question.key).closes })
        answered(base.toList ::: without_each.map(_._2)).map { _ =>
          if (!base.forall(question => answers(question.key).closes)) rules
          else rules.filterNot(can_go)
        }
      }
    }

    private def as_written(use: Use, proof: Pide.Answer, rules: List[Rule]): Boolean =
      use.notes.isEmpty && methods(lemma, use, compress(lemma, use, proof, rules)) == use.step.get.methods

    /* Fixes from fine to coarse: the rules left, all used, whole facts, then own facts only. */
    private def candidates(proofs: Map[Use, Pide.Answer], kept: Map[Use, List[Rule]]): List[Edits] = {
      def full(use: Use): List[Rule] = keep_own(lemma, use) ::: all_notes(use)
      def step(use: Use, rules: List[Rule]): List[Rule] = compress(lemma, use, proofs(use), rules)
      def members(use: Use): List[Rule] = step(use, used(lemma, use, proofs(use), members = true))
      def facts(use: Use): List[Rule] = step(use, used(lemma, use, proofs(use), members = false))

      List(
        candidate(notes, use => if (use.step.isDefined) step(use, kept(use)) else keep_own(lemma, use)),
        candidate(notes, use => if (use.step.isDefined) members(use) else full(use)),
        candidate(notes, use => if (use.step.isDefined) facts(use) else full(use)),
        candidate(Nil, use =>
          if (use.step.isDefined) step(use, kept(use).filter(_.own.isDefined)) else keep_own(lemma, use))
      ).distinctBy(lemma.replace_all).filterNot(edits => lemma.replace_all(edits) == lemma.source)
    }

    private def candidate(dropped: List[Simp_Note], rules: Use => List[Rule]): Edits =
      dropped.flatMap(_.attributes.map(_ -> "")) ::: uses.flatMap(use => edits(lemma, use, rules(use)))

    @scala.annotation.tailrec
    private def first_closing(candidates: List[(Edits, Int)]): Either[List[Pide.Question], Option[Edits]] =
      candidates match {
        case Nil => Right(None)
        case (edits, i) :: rest =>
          val question = rerun(lemma, "edit" + i, lemma.replace_all(edits), budget)
          answers.get(question.key) match {
            case None => Left(List(question))
            case Some(answer) if answer.closes => Right(Some(edits))
            case _ => first_closing(rest)
          }
      }

    /* Each run gets the budget, and the question's limit covers all of them. */
    private def timed(fix: Option[Edits]): Result =
      fix match {
        case None => Right(None)
        case Some(edits) =>
          val runs = options.int("simp_scope_runs")
          val question = Pide.Question(lemma.key + ":time", lemma.theory, lemma.before.command, "linter_runs",
            List(runs.toString, lemma.source, lemma.replace_all(edits)), Time.ms(budget.ms * 2 * runs),
            serial = true)
          answers.get(question.key) match {
            case None => Left(List(question))
            case Some(timing) if timing.closes && timing.ms2 * options.real("simp_scope_speedup") < timing.ms =>
              Right(Some(Fix(edits, timing.medians)))
            case _ => Right(None)
          }
      }

    private def used_question(use: Use): Pide.Question = {
      val step = use.step.get
      Pide.Question(lemma.key + ":used:" + use.cmd.offset, lemma.theory, step.goal.command, "linter_used_members",
        step.methods :: slots(lemma, use).map(_.fact), timeout)
    }

    private def try_question(use: Use, rules: List[Rule], limit: Time): Pide.Question = {
      val text = methods(lemma, use, rules)
      val note_facts = use.notes.flatMap(_.facts)
      val (function, args) =
        if (note_facts.isEmpty) ("linter_try", List(text)) else ("linter_try_del", text :: note_facts)
      Pide.Question(lemma.key + ":try:" + use.cmd.offset + ":" + text, lemma.theory, use.step.get.goal.command,
        function, args, limit)
    }
  }


  /* Theory-level [simp] declarations, tried on the later lemmas of their theory. They are only
     reported: other theories may see them. */

  val declaration_commands: Set[String] = Set("declare", "lemmas")

  def is_declaration(lemma: Lemma): Boolean = declaration_commands(lemma.cmds.head.name)

  /* A theory's [simp] declarations, each as a target of one command. */
  private def declaration_targets(snapshot: Document.Snapshot): List[Lemma] = {
    val text = snapshot.node.source
    val lines = Line.Document(text)
    val cmds = Cmd.read(snapshot.node)
    for {
      (cmd, i) <- cmds.zipWithIndex
      if i > 0 && declaration_commands(cmd.name) && Simp_Text.note(text, cmd).isDefined
    } yield Lemma(snapshot.node_name, text, lines, cmds(i - 1), List(cmd), ok = true)
  }

  def declarations(targets: List[Lemma]): List[(Simp_Note, List[Lemma])] = {
    val (declaring, lemmas) = targets.partition(is_declaration)
    for {
      declaration <- declaring
      note <- Simp_Text.note(declaration.text, declaration.cmds.head).toList
      after = lemmas.filter(lemma => lemma.theory == declaration.theory && lemma.start > declaration.start)
        .sortBy(_.start)
      if after.nonEmpty
    } yield (note, after)
  }

  /* The lemma after `declare a[simp del]`. Over a minute counts as needing it, as it may loop. */
  private def undeclared(note: Simp_Note, lemma: Lemma, options: Options): Pide.Question = {
    val off = note.name.map(List(_)).getOrElse(note.facts).map(_ + "[simp del]").mkString(" ")
    rerun(lemma, "declare:" + note.cmd.offset, "declare " + off + "\n" + lemma.source,
      Time.seconds(options.real("linter_timeout") min 60))
  }

  /* Reported if at most half of the lemmas after it fail without it. */
  private def declaration_finding(note: Simp_Note, after: List[Lemma], answers: Pide.Answers,
      options: Options): Option[Finding] = {
    val needed = after.filterNot(lemma => answers.get(undeclared(note, lemma, options).key).exists(_.closes))
    if (2 * needed.length > after.length) None
    else {
      val names = needed.map(lemma => "line " + lemma.line).mkString(", ")
      val message = "the [simp] here is needed by " + needed.length + " of the " + after.length +
        " lemmas after it in this theory" + (if (needed.isEmpty) "" else ": " + names) +
        " (the others still work with it deleted; other theories may need it)"
      Some(Finding(name, after.head, after.head.line(note.cmd.offset), message))
    }
  }

  private def rerun(lemma: Lemma, what: String, text: String, timeout: Time): Pide.Question =
    Pide.Question(lemma.key + ":" + what, lemma.theory, lemma.before.command, "linter_run", List(text), timeout)


  /* lint interface */

  override def targets(checked: Pide.Checked): List[Lemma] =
    super.targets(checked) ::: checked.snapshots.flatMap(declaration_targets)

  def ask(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Pide.Question] =
    lemmas.filterNot(is_declaration).flatMap(check(_, answers, options).left.getOrElse(Nil)) :::
      theory_questions(lemmas, options)

  private def theory_questions(lemmas: List[Lemma], options: Options): List[Pide.Question] =
    if (!options.bool("simp_scope_theory")) Nil
    else for ((note, after) <- declarations(lemmas); lemma <- after) yield undeclared(note, lemma, options)

  def report(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] =
    lemma_findings(lemmas, answers, options) ::: theory_findings(lemmas, answers, options)

  private def lemma_findings(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] =
    for {
      lemma <- lemmas.filterNot(is_declaration)
      fix <- check(lemma, answers, options).toOption.flatten.toList
    } yield {
      val changes =
        lemma.cmds.filter(cmd => fix.edits.exists(edit => inside(cmd, edit._1))).map(change(lemma, _, fix.edits))
      val message = ("simp rules only where the steps need them: " + fix.medians.before + " ms as written, " +
        fix.medians.after + " ms with the fix (medians, alone)") :: changes
      Finding(name, lemma, lemma.line, message.mkString("\n"), Some(lemma.replace_all(fix.edits)))
    }

  private def theory_findings(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] =
    if (!options.bool("simp_scope_theory")) Nil
    else declarations(lemmas).flatMap({ case (note, after) => declaration_finding(note, after, answers, options) })

  private def inside(cmd: Cmd, range: Text.Range): Boolean =
    cmd.range.start <= range.start && range.stop <= cmd.range.stop

  private def change(lemma: Lemma, cmd: Cmd, edits: Edits): String = {
    def flat(s: String): String = s.replaceAll("\\s+", " ").nn
    val old = lemma.text.substring(cmd.range.start, cmd.range.stop).nn
    val fixed = Lemma.edit(old, cmd.range.start, edits.filter(edit => inside(cmd, edit._1)))
    "  line " + lemma.line(cmd.range.start) + ": `" + flat(old) + "` -> `" + flat(fixed) + "`"
  }
}
