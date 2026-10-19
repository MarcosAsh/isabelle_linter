/* simp_hygiene: rules that the simplifier and the classical reasoner keep trying for nothing;
  information only, it needs an Isabelle built with etc/simpstats.patch */

package isabelle.isabelle_linter

import isabelle._


object Simp_Hygiene extends Lint {
  val name = "simp_hygiene"

  /* the patched Isabelle sets this in its etc/settings */
  def available: Boolean = Isabelle_System.getenv("ISABELLE_RULE_STATISTICS") == "true"

  /* fail_us: time in the failed tries of a conditional rule */
  sealed case class Rule(candidates: Long, matches: Long, rewrites: Long, fail_us: Long,
      conditional: Boolean) {
    def +(r: Rule): Rule =
      Rule(candidates + r.candidates, matches + r.matches, rewrites + r.rewrites,
        fail_us + r.fail_us, conditional || r.conditional)
    def failed: Long = matches - rewrites
  }

  sealed case class Proc(calls: Long, rewrites: Long, us: Long) {
    def +(p: Proc): Proc = Proc(calls + p.calls, rewrites + p.rewrites, us + p.us)
  }

  /* tries: by the classical reasoner; offers: to blast; used: in the lemma's proof */
  sealed case class Intro(tries: Long, unified: Long, offers: Long, used: Boolean) {
    def +(i: Intro): Intro = Intro(tries + i.tries, unified + i.unified, offers + i.offers, used || i.used)
    def total: Long = tries + offers
  }

  /* one lemma's counts, run once with the statistics on; finished: it ran to the end, so
    its proof is known */
  sealed case class Stats(lemma: Lemma, finished: Boolean, ms: Long, rules: Map[String, Rule],
    procs: Map[String, Proc], intros: Map[String, Intro])


  /* Per lemma: run it once with the statistics on. Per session, of the rules and simprocs tried
    at least simp_hygiene_min times: report the [simp] rules and simprocs that never rewrote, the
    conditional rules whose condition nearly always fails, and the classical rules that are
    rarely in a proof. Nothing is re-run without them, so the findings are information only. */

  /* an unnamed result is not kept, so the run names it */
  val result_name = "linter_rule_stats_result"

  def named_source(lemma: Lemma): String = {
    val body = lemma.cmds.head.body
    val rest = if (body.headOption.exists(_.is("("))) Syntax.take_group(body, "(", ")")._2 else body
    rest match {
      case n :: t :: _ if n.token.is_ident && (t.is(":") || t.is("[")) => lemma.source
      case t :: _ =>
        val at = t.range.start - lemma.start
        val name = if (t.is("[")) result_name + " " else result_name + ": "
        lemma.source.substring(0, at) + name + lemma.source.substring(at)
      case Nil => lemma.source
    }
  }

  def question(lemma: Lemma, options: Options): Pide.Question =
    Pide.Question(lemma.key + ":rule_stats", lemma.theory, lemma.before.command, "linter_rule_stats",
      List(named_source(lemma)), Time.seconds(options.real("linter_timeout")))


  /* answers: lines of tab-separated fields */

  private def fields(text: String): List[List[String]] =
    Library.split_lines(text).filter(_.nonEmpty).map(Library.space_explode('\t', _))

  private def rules(text: String): Map[String, Rule] =
    fields(text).collect({ case List(n, c, m, r, us, cond) =>
      n -> Rule(c.toLong, m.toLong, r.toLong, us.toLong, cond == "1") }).toMap

  private def procs(text: String): Map[String, Proc] =
    fields(text).collect({ case List(n, c, r, us) => n -> Proc(c.toLong, r.toLong, us.toLong) }).toMap

  /* a rule's classical tries and blast offers go together */
  private def intros(text: String): Map[String, Intro] =
    fields(text).collect({ case List(kind, n, t, u, used) =>
      val (tries, offers) = if (kind == "blast") (0L, t.toLong) else (t.toLong, 0L)
      n -> Intro(tries, u.toLong, offers, used == "1") }).groupMapReduce(_._1)(_._2)(_ + _)

  def stats(lemma: Lemma, answer: Pide.Answer): Option[Stats] =
    for {
      r <- answer.get("rules")
      p <- answer.get("procs")
      c <- answer.get("classical")
    } yield Stats(lemma, answer.get("proved").contains("1"), answer.ms, rules(r), procs(p), intros(c))

  private def totals[A](maps: List[Map[String, A]], plus: (A, A) => A): Map[String, A] =
    maps.foldLeft(Map.empty[String, A]) { (acc, m) =>
      m.foldLeft(acc) { case (a, (k, v)) => a + (k -> a.get(k).map(plus(_, v)).getOrElse(v)) }
    }


  /* where a rule comes from */

  val simp_attributes: Set[String] = Set("simp")
  val classical_attributes: Set[String] = Set("intro", "elim", "dest")

  /* `lemma NAME [... simp ...]:` with one of the attributes */
  def declared_name(lemma: Lemma, attributes: Set[String]): Option[String] =
    lemma.cmds.head.body match {
      case n :: open :: rest if n.token.is_ident && open.is("[") =>
        val group = Syntax.take_group(open :: rest, "[", "]")._1
        if (group.exists(t => attributes(t.source))) Some(n.source) else None
      case _ => None
    }

  def theory_base(lemma: Lemma): String = Long_Name.base_name(lemma.theory.theory)

  /* the rule is `Thy.name`, `Thy.locale.name` ..., maybe with a `(i)` */
  def declaration(lemmas: List[Lemma], rule: String, attributes: Set[String]): Option[Lemma] = {
    val fact = rule.replaceAll("\\(\\d+\\)$", "")
    lemmas.find { l =>
      val thy = theory_base(l)
      declared_name(l, attributes).exists(n => fact.startsWith(thy + ".") && fact.endsWith("." + n))
    }
  }

  def own(lemmas: List[Lemma], rule: String): Boolean =
    lemmas.exists(l => unnamed(rule).getOrElse(rule).startsWith(theory_base(l) + "."))

  /* rules without a name, like the equations of fun, count under "??." and their head constant */
  def unnamed(rule: String): Option[String] = if (rule.startsWith("??.")) Some(rule.drop(3)) else None

  def simp_rule(rule: String): String =
    unnamed(rule) match {
      case Some(c) => "unnamed [simp] rules for `" + c + "` (like its fun equations)"
      case None => "[simp] rule `" + rule + "`"
    }

  /* what to write in `declare FACT [simp del]` */
  def simp_fact(rule: String): String = unnamed(rule).map(_ + ".simps").getOrElse(rule)

  /* the declaring lemma, else the lemma with the most of it */
  private def place(lemmas: List[Lemma], rule: String, attributes: Set[String], users: List[Stats],
      weight: Stats => Long): (Lemma, String) =
    declaration(lemmas, rule, attributes) match {
      case Some(l) => (l, "declared here")
      case None if own(lemmas, rule) => (users.maxBy(weight).lemma, "declared in this session")
      case None => (users.maxBy(weight).lemma, "imported")
    }


  /* findings */

  private def coverage(lemmas: List[Lemma], measured: List[Stats]): String =
    "information only, nothing was re-run without it; counted over " + measured.length + " of " +
      lemmas.length + " lemmas" + (measured.count(!_.finished) match {
        case 0 => ""
        case n => " (" + n + " did not finish)"
      })

  private def ms(us: Long): String = (us / 1000).toString + " ms"

  /* (1) [simp] rules offered often that never rewrote */
  private def dead_rules(lemmas: List[Lemma], measured: List[Stats], options: Options,
      note: String): List[Finding] =
    for {
      (rule, total) <- totals[Rule](measured.map(_.rules), _ + _).toList.sortBy(-_._2.candidates)
      if total.rewrites == 0 && total.candidates >= options.int("simp_hygiene_min")
    } yield {
      val users = measured.filter(_.rules.contains(rule))
      val (at, origin) = place(lemmas, rule, simp_attributes, users, _.rules(rule).candidates)
      val matched =
        if (total.matches == 0) "never matched"
        else if (total.conditional) "condition tried " + total.matches + " times (" + ms(total.fail_us) + ")"
        else "matched " + total.matches + " times"
      val fact = simp_fact(rule)
      val advice =
        if (origin == "declared here") "drop [simp], or `declare " + fact + " [simp del]` where it is not needed"
        else "`declare " + fact + " [simp del]` in this session, or `simp del: " + fact + "` in its steps"
      val message =
        simp_rule(rule) + " offered " + total.candidates + " times in " + users.length +
          " lemmas, " + matched + ", never rewrote\n  " + origin + ": " + advice + "\n  " + note
      Finding(name, at, at.line, message)
    }

  /* (2) simprocs called often that never rewrote */
  private def idle_procs(measured: List[Stats], options: Options, note: String): List[Finding] =
    for {
      (proc, total) <- totals[Proc](measured.map(_.procs), _ + _).toList.sortBy(-_._2.us)
      if total.rewrites == 0 && total.calls >= options.int("simp_hygiene_min")
    } yield {
      val users = measured.filter(_.procs.contains(proc))
      val at = users.maxBy(_.procs(proc).us).lemma
      val message =
        "simproc `" + proc + "` called " + total.calls + " times in " + users.length +
          " lemmas, never rewrote; " + ms(total.us) + " inside it, of the " + users.map(_.ms).sum +
          " ms these lemmas took counting\n  `declare [[simproc del: " + proc + "]]` in the theory, " +
          "or `using [[simproc del: " + proc + "]]` before the slow steps; most time in this lemma\n  " + note
      Finding(name, at, at.line, message)
    }

  /* (4) conditional rules that do rewrite, but whose condition nearly always fails */
  val held_share = 0.1

  private def failing_conditions(lemmas: List[Lemma], measured: List[Stats], options: Options,
      note: String): List[Finding] =
    for {
      (rule, total) <- totals[Rule](measured.map(_.rules), _ + _).toList.sortBy(-_._2.fail_us)
      if total.conditional && total.rewrites > 0 && total.rewrites <= held_share * total.matches &&
        total.failed >= options.int("simp_hygiene_min")
    } yield {
      val users = measured.filter(_.rules.get(rule).exists(_.failed > 0))
      val (at, origin) = place(lemmas, rule, simp_attributes, users, _.rules(rule).fail_us)
      val message =
        "conditional " + simp_rule(rule) + ": condition tried " + total.matches + " times in " +
          users.length + " lemmas and held " + total.rewrites + " of them; " + ms(total.fail_us) +
          " in the failed tries\n  " + origin + ": a cheaper premise, or `simp del: " + simp_fact(rule) +
          "` where it fails\n  " + note
      Finding(name, at, at.line, message)
    }

  /* (5) classical rules tried often that are rarely in a proof */
  val used_share = 0.05

  private def idle_intros(lemmas: List[Lemma], measured: List[Stats], options: Options,
      note: String): List[Finding] =
    for {
      (rule, total) <- totals[Intro](measured.map(_.intros), _ + _).toList.sortBy(-_._2.total)
      if total.total >= options.int("simp_hygiene_min")
      users = measured.filter(_.intros.contains(rule))
      proved = users.filter(_.finished)
      used = proved.count(_.intros(rule).used)
      if proved.nonEmpty && used <= used_share * proved.length
    } yield {
      val (at, origin) = place(lemmas, rule, classical_attributes, users, _.intros(rule).total)
      val message =
        "classical rule `" + rule + "` tried " + total.tries + " times (" + total.unified +
          " unified) and offered to blast " + total.offers + " times in " + users.length +
          " lemmas, in the proof of " + used + " of the " + proved.length + " that finished\n  " +
          origin + ": drop or weaken its [intro]/[elim]/[dest], or `declare " + rule +
          " [rule del]` where it is not needed\n  " + note
      Finding(name, at, at.line, message)
    }


  /* lint interface */

  def ask(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Pide.Question] =
    if (!available) error("simp_hygiene needs an Isabelle built with etc/simpstats.patch")
    else lemmas.map(question(_, options))

  def report(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] = {
    val measured = lemmas.flatMap(l => answers.get(question(l, options).key).flatMap(stats(l, _)))
    val note = coverage(lemmas, measured)
    dead_rules(lemmas, measured, options, note) ::: idle_procs(measured, options, note) :::
      failing_conditions(lemmas, measured, options, note) ::: idle_intros(lemmas, measured, options, note)
  }
}
