/* simp_scope: [simp] rules set for a block or bundled into a step that it does not need */

package isabelle.isabelle_linter

import isabelle._


object Simp_Scope extends Lint {
  val name = "simp_scope"

  /* a command whose methods read the simpset, with notes in scope and its step */
  sealed case class Use(cmd: Cmd, methods: List[Simp_Method], notes: List[Simp_Note], step: Option[Step]) {
    def own: List[List[Tok]] = methods.flatMap(_.sections).flatMap(_.facts)
  }

  /* a fact or one of its theorems; replaces the own fact at offset `own`, else is added */
  sealed case class Rule(name: String, fact: String, own: Option[Int] = None)

  type Edits = List[(Text.Range, String)]

  /* questions to ask, or edits with median times before and after */
  type Result = Either[List[Pide.Question], Option[(Edits, Long, Long)]]


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
      in_scope = scoped.filter(_._2.contains(cmd)).map(_._1)
      use = Use(cmd, methods, in_scope, lemma.steps.find(_.cmd == cmd))
      if methods.nonEmpty && (in_scope.nonEmpty || (use.step.isDefined && use.own.nonEmpty))
    } yield use
  }


  private def text(lemma: Lemma, fact: List[Tok]): String = Simp_Text.source(lemma.text, fact)

  /* the notes' facts, then the use's own */
  private def slots(lemma: Lemma, use: Use): List[Rule] =
    use.notes.flatMap(_.facts).map(f => Rule(f, f)) :::
      use.own.map(f => Rule(text(lemma, f), text(lemma, f), Some(f.head.range.start)))

  /* None if unknown */
  private def names(a: Pide.Answer, prop: String): Option[List[String]] =
    a.get(prop).filter(_ => a.closes) match {
      case None | Some("*") => None
      case Some("-") => Some(Nil)
      case Some(s) => Some(Library.space_explode(' ', s))
    }

  /* what the proof used, as theorems or whole facts */
  def used(lemma: Lemma, use: Use, a: Pide.Answer, members: Boolean): List[Rule] =
    slots(lemma, use).zipWithIndex.flatMap { case (slot, i) =>
      names(a, "used" + i) match {
        case Some(Nil) => Nil
        case Some(ns) if members => ns.map(n => slot.copy(name = n))
        case _ => List(slot)
      }
    }

  def compress(lemma: Lemma, use: Use, a: Pide.Answer, rules: List[Rule]): List[Rule] =
    slots(lemma, use).zipWithIndex.flatMap { case (slot, i) =>
      val mine = rules.filter(r => r.fact == slot.fact && r.own == slot.own)
      names(a, "all" + i) match {
        case Some(all) if all.nonEmpty && all.forall(n => mine.exists(_.name == n)) => List(slot)
        case _ => mine
      }
    }

  def keep_own(lemma: Lemma, use: Use): List[Rule] = slots(lemma, use).filter(_.own.isDefined)

  def all_notes(use: Use): List[Rule] =
    use.notes.flatMap(n => n.name.map(List(_)).getOrElse(n.facts)).map(f => Rule(f, f))


  def edits(lemma: Lemma, use: Use, rules: List[Rule]): Edits = {
    val add = by_name(use.notes, rules.filter(_.own.isEmpty).map(_.name).distinct)
    def own(fact: List[Tok]): List[String] = rules.filter(_.own.contains(fact.head.range.start)).map(_.name)
    use.methods.flatMap(Simp_Text.rewrite(lemma.text, _, own, add))
  }

  private def by_name(notes: List[Simp_Note], add: List[String]): List[String] =
    notes.foldLeft(add) { (names, n) =>
      n.name match {
        case Some(name) if n.facts.forall(names.contains) => names.filterNot(n.facts.contains) :+ name
        case _ => names
      }
    }

  def edited(text: String, start: Int, edits: Edits): String =
    edits.sortBy(_._1.start).reverse.foldLeft(text) { case (t, (r, s)) =>
      t.substring(0, r.start - start) + s + t.substring(r.stop - start)
    }

  def methods(lemma: Lemma, use: Use, rules: List[Rule]): String = {
    val start = use.cmd.body.head.range.start
    val es = edits(lemma, use, rules)
    edited(lemma.text.substring(start, use.cmd.range.stop), start, es)
  }


  /* ask what each step used, drop rules one by one, re-run, time the first fix */

  def check(lemma: Lemma, answers: Pide.Answers, options: Options): Result = {
    val ns = notes(lemma).map(_._1)
    val us = uses(lemma)
    val original = rerun(lemma, "original", lemma.source, Time.seconds(options.real("linter_timeout")))

    if (ns.isEmpty && us.isEmpty) Right(None)
    else {
      answers.get(original.key) match {
        case None => Left(List(original))
        case Some(a) if !a.closes || a.ms < options.real("simp_scope_slow") * 1000 => Right(None)
        case Some(a) => new Search(lemma, ns, us, a, answers, options).run()
      }
    }
  }

  private class Search(lemma: Lemma, notes: List[Simp_Note], uses: List[Use], original: Pide.Answer,
      answers: Pide.Answers, options: Options) {
    private val timeout = Time.seconds(options.real("linter_timeout"))
    private val budget = Time.ms((original.ms * options.real("linter_factor")).toLong max 1000L min timeout.ms)
    private val steps = uses.filter(_.step.isDefined)

    def run(): Result =
      for {
        found <- answered(steps.map(used_question))
        proofs = steps.zip(found).toMap
        kept <- all(steps.map(u => u -> greedy(u, proofs(u))))
        fix <- first(candidates(proofs, kept.toMap).zipWithIndex)
        result <- timed(fix)
      } yield result

    private def answered(qs: List[Pide.Question]): Either[List[Pide.Question], List[Pide.Answer]] =
      qs.filterNot(q => answers.contains(q.key)) match {
        case Nil => Right(qs.map(q => answers(q.key)))
        case missing => Left(missing)
      }

    private def all[A](xs: List[(Use, Either[List[Pide.Question], A])]): Either[List[Pide.Question], List[(Use, A)]] =
      xs.flatMap(_._2.left.getOrElse(Nil)) match {
        case Nil => Right(xs.map({ case (u, r) => u -> r.toOption.get }))
        case missing => Left(missing)
      }

    /* used rules minus each one the step does without alone */
    private def greedy(use: Use, proof: Pide.Answer): Either[List[Pide.Question], List[Rule]] = {
      val rules = used(lemma, use, proof, members = true)
      val limit = Time.ms(proof.ms * 2 max 1000L min timeout.ms)
      def ask(rs: List[Rule]): Pide.Question = try_question(use, compress(lemma, use, proof, rs), limit)

      if (rules.isEmpty || rules.length > options.int("simp_scope_greedy")) Right(rules)
      else {
        val base = ask(rules)
        val drops = rules.map(r => r -> ask(rules.filterNot(_ == r)))
        answered(base :: drops.map(_._2)).map { as =>
          if (!as.head.closes) rules
          else rules.filterNot(r => drops.exists({ case (s, q) => s == r && answers(q.key).closes }))
        }
      }
    }

    /* fixes from fine to coarse: rules left, all used, whole facts, then own facts only */
    private def candidates(proofs: Map[Use, Pide.Answer], kept: Map[Use, List[Rule]]): List[Edits] = {
      def full(u: Use): List[Rule] = keep_own(lemma, u) ::: all_notes(u)
      def step(u: Use, rules: List[Rule]): List[Rule] = compress(lemma, u, proofs(u), rules)
      def members(u: Use): List[Rule] = step(u, used(lemma, u, proofs(u), members = true))
      def facts(u: Use): List[Rule] = step(u, used(lemma, u, proofs(u), members = false))

      List(
        candidate(notes, u => if (u.step.isDefined) step(u, kept(u)) else keep_own(lemma, u)),
        candidate(notes, u => if (u.step.isDefined) members(u) else full(u)),
        candidate(notes, u => if (u.step.isDefined) facts(u) else full(u)),
        candidate(Nil, u => if (u.step.isDefined) step(u, kept(u).filter(_.own.isDefined)) else keep_own(lemma, u))
      ).distinctBy(lemma.replace_all).filterNot(es => lemma.replace_all(es) == lemma.source)
    }

    private def candidate(dropped: List[Simp_Note], rules: Use => List[Rule]): Edits =
      dropped.flatMap(_.attributes.map(_ -> "")) ::: uses.flatMap(u => edits(lemma, u, rules(u)))

    @scala.annotation.tailrec
    private def first(candidates: List[(Edits, Int)]): Either[List[Pide.Question], Option[Edits]] =
      candidates match {
        case Nil => Right(None)
        case (es, i) :: rest =>
          val q = rerun(lemma, "edit" + i, lemma.replace_all(es), budget)
          answers.get(q.key) match {
            case None => Left(List(q))
            case Some(a) if a.closes => Right(Some(es))
            case _ => first(rest)
          }
      }

    /* each run gets the budget, the question's limit covers all */
    private def timed(fix: Option[Edits]): Result =
      fix match {
        case None => Right(None)
        case Some(es) =>
          val runs = options.int("simp_scope_runs")
          val q = Pide.Question(lemma.key + ":time", lemma.theory, lemma.before.command, "linter_runs",
            List(runs.toString, lemma.source, lemma.replace_all(es)), Time.ms(budget.ms * 2 * runs), serial = true)
          answers.get(q.key) match {
            case None => Left(List(q))
            case Some(t) if t.closes && t.ms2 * options.real("simp_scope_speedup") < t.ms => Right(Some((es, t.ms, t.ms2)))
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

  /* theory-level [simp] declarations with later lemmas; reported only, others see them */

  val declaration_commands: Set[String] = Set("declare", "lemmas")

  def is_declaration(lemma: Lemma): Boolean = declaration_commands(lemma.cmds.head.name)

  /* a theory's [simp] declarations, each as a one-command target */
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
    val (decls, lemmas) = targets.partition(is_declaration)
    for {
      decl <- decls
      d <- Simp_Text.note(decl.text, decl.cmds.head).toList
      after = lemmas.filter(l => l.theory == decl.theory && l.start > decl.start).sortBy(_.start)
      if after.nonEmpty
    } yield (d, after)
  }

  /* lemma after `declare a[simp del]`; over a minute counts as needing it (may loop) */
  private def undeclared(d: Simp_Note, lemma: Lemma, options: Options): Pide.Question = {
    val off = d.name.map(List(_)).getOrElse(d.facts).map(_ + "[simp del]").mkString(" ")
    rerun(lemma, "declare:" + d.cmd.offset, "declare " + off + "\n" + lemma.source,
      Time.seconds(options.real("linter_timeout") min 60))
  }

  /* at most half of the lemmas after it fail without it */
  private def declaration_finding(d: Simp_Note, after: List[Lemma], answers: Pide.Answers,
      options: Options): Option[Finding] = {
    val needed = after.filterNot(l => answers.get(undeclared(d, l, options).key).exists(_.closes))
    if (2 * needed.length > after.length) None
    else {
      val names = needed.map(l => "line " + l.line).mkString(", ")
      val message = "the [simp] here is needed by " + needed.length + " of the " + after.length +
        " lemmas after it in this theory" + (if (needed.isEmpty) "" else ": " + names) +
        " (the others still work with it deleted; other theories may need it)"
      Some(Finding(name, after.head, after.head.line(d.cmd.offset), message))
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
    else for ((d, after) <- declarations(lemmas); l <- after) yield undeclared(d, l, options)

  def report(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] =
    lemma_findings(lemmas, answers, options) ::: theory_findings(lemmas, answers, options)

  private def lemma_findings(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] =
    for {
      lemma <- lemmas.filterNot(is_declaration)
      (es, before, after) <- check(lemma, answers, options).toOption.flatten.toList
    } yield {
      val changes = lemma.cmds.filter(c => es.exists(e => inside(c, e._1))).map(change(lemma, _, es))
      val message = ("simp rules only where the steps need them: " + before + " ms as written, " + after +
        " ms with the fix (medians, alone)") :: changes
      Finding(name, lemma, lemma.line, message.mkString("\n"), Some(lemma.replace_all(es)))
    }

  private def theory_findings(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] =
    if (!options.bool("simp_scope_theory")) Nil
    else declarations(lemmas).flatMap({ case (d, after) => declaration_finding(d, after, answers, options) })

  private def inside(cmd: Cmd, r: Text.Range): Boolean = cmd.range.start <= r.start && r.stop <= cmd.range.stop

  private def change(lemma: Lemma, cmd: Cmd, es: Edits): String = {
    def flat(s: String): String = s.replaceAll("\\s+", " ")
    val old = lemma.text.substring(cmd.range.start, cmd.range.stop)
    val mine = es.filter(e => inside(cmd, e._1))
    "  line " + lemma.line(cmd.range.start) + ": `" + flat(old) + "` -> `" + flat(edited(old, cmd.range.start, mine)) + "`"
  }
}
