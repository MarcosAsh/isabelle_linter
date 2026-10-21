/* simp_scope: [simp] notes and the simp methods of a command */

package isabelle.isabelle_linter

import isabelle._


/* a note's [simp] facts, the name it binds them to, and the ranges of its [simp] */
sealed case class Simp_Note(cmd: Cmd, facts: List[String], name: Option[String], attributes: List[Text.Range])

/* a section like `simp add: a b`; only: `simp only:` */
sealed case class Simp_Section(header: List[Tok], facts: List[List[Tok]], only: Boolean)

/* a method that reads the simpset; wrap: needs parentheses for arguments */
sealed case class Simp_Method(head: Tok, args: List[Tok], sections: List[Simp_Section], wrap: Boolean) {
  def add_header: String = if (Simp_Text.simp_methods(head.source)) "add:" else "simp add:"
  def stop: Int = (head :: args).last.range.stop
}


object Simp_Text {
  val simp_methods: Set[String] = Set("simp", "simp_all")
  val clasimp_methods: Set[String] = Set("auto", "force", "fastforce", "clarsimp", "bestsimp", "slowsimp")

  def reads_simpset(t: Tok): Boolean = t.token.is_name && (simp_methods(t.source) || clasimp_methods(t.source))

  def source(text: String, toks: List[Tok]): String = text.substring(toks.head.range.start, toks.last.range.stop)


  /* `note NAME[simp] = a b`, `note [simp] = a b`, `note a[simp] b[simp]`; also declare */

  private def is_simp(toks: List[Tok]): Boolean = toks.map(_.source) == List("[", "simp", "]")

  private def attributes(item: List[Tok]): (List[Tok], List[Tok]) = item.span(t => !t.is("["))

  def note(text: String, cmd: Cmd): Option[Simp_Note] = {
    val body = cmd.body
    val eq = outside_brackets(body).indexWhere(_.exists(_.is("=")))
    val (binding, rest) = if (eq < 0) (Nil, body) else (body.take(eq), body.drop(eq + 1))
    val items = Syntax.fact_items(rest)

    val unsupported =
      !Set("note", "declare", "lemmas")(cmd.name) || body.exists(t => t.is("and") || t.is("this")) || items.isEmpty ||
        (binding.exists(_.is("simp")) && !is_simp(binding.dropWhile(!_.is("[")))) ||
        items.exists(i => attributes(i)._2.exists(_.is("simp")) && !is_simp(attributes(i)._2))

    val simp_items = items.filter(i => is_simp(attributes(i)._2))
    if (unsupported) None
    else if (binding.exists(_.is("simp")) && simp_items.isEmpty) Some(bound(text, cmd, binding, rest, items))
    else if (binding.exists(_.is("simp")) || simp_items.isEmpty) None
    else {
      val facts = simp_items.map(i => source(text, attributes(i)._1))
      val ranges = simp_items.map(i => Text.Range(attributes(i)._1.last.range.stop, i.last.range.stop))
      Some(Simp_Note(cmd, facts, None, ranges))
    }
  }

  /* `NAME[simp] = a b` loses `[simp]`, `[simp] = a b` loses `[simp] =` */
  private def bound(text: String, cmd: Cmd, binding: List[Tok], rest: List[Tok], items: List[List[Tok]]): Simp_Note = {
    val facts = items.map(source(text, _))
    binding match {
      case name :: _ if name.token.is_name =>
        Simp_Note(cmd, facts, Some(name.source), List(Text.Range(name.range.stop, binding.last.range.stop)))
      case _ =>
        Simp_Note(cmd, facts, None, List(Text.Range(binding.head.range.start, rest.head.range.start)))
    }
  }

  /* tokens, None inside brackets */
  private def outside_brackets(toks: List[Tok]): List[Option[Tok]] = {
    val brackets = depths(toks.toVector)._2
    toks.zipWithIndex.map({ case (t, k) => if (brackets(k) == 0) Some(t) else None })
  }


  /* commands after cmds(i) to the end of its block */
  def scope(cmds: List[Cmd], i: Int): List[Cmd] = {
    var depth = 0
    cmds.drop(i + 1).takeWhile { c =>
      if (Keyword.proof_open(c.kind)) depth += 1
      else if (Keyword.proof_close(c.kind)) depth -= 1
      depth >= 0 && !(depth == 0 && c.kind == Keyword.NEXT_BLOCK) && !Keyword.qed_global(c.kind)
    }
  }


  /* like `auto` in `(cases x; auto)` */

  private val before_method = Set("(", ",", ";", "|")

  def methods(body: List[Tok]): List[Simp_Method] = {
    val toks = body.toVector
    val (parens, brackets) = depths(toks)
    for {
      k <- toks.indices.toList
      if reads_simpset(toks(k)) && brackets(k) == 0
      if parens(k) == 0 || before_method(toks(k - 1).source)
    } yield method(toks, k, parens(k) == 0)
  }

  private def depths(toks: Vector[Tok]): (Vector[Int], Vector[Int]) = {
    def depth(open: String, close: String): Vector[Int] =
      toks.scanLeft(0)((d, t) => if (t.is(open)) d + 1 else if (t.is(close)) d - 1 else d).init
    (depth("(", ")"), depth("[", "]"))
  }

  /* at the top of `by`, a method takes no arguments without parens */
  private def method(toks: Vector[Tok], k: Int, top: Boolean): Simp_Method = {
    val args = if (top) Nil else arguments(toks.drop(k + 1).toList)
    val next = toks.lift(k + 1 + args.length).map(_.source)
    val wrap = args.isEmpty && (top || next.exists(Set("+", "?", "[")))
    Simp_Method(toks(k), args, sections(args, simp_methods(toks(k).source)), wrap)
  }

  private def arguments(toks: List[Tok]): List[Tok] = {
    var depth = 0
    toks.takeWhile { t =>
      if (t.is("(") || t.is("[")) depth += 1
      else if (t.is(")") || t.is("]")) depth -= 1
      depth >= 0 && !(depth == 0 && Set(",", ";", "|")(t.source))
    }
  }


  /* `simp:`, `simp add:`, `simp only:` of auto and friends; `add:`, `only:` of simp */

  private val modifiers = Set("simp", "cong", "split", "iff", "intro", "elim", "dest")

  private def header(toks: List[Tok]): Option[(String, Int)] =
    toks match {
      case a :: b :: c :: _ if modifiers(a.source) && Set("add", "del", "only", "flip")(b.source) && c.is(":") =>
        Some((a.source + " " + b.source, 3))
      case a :: b :: c :: _ if a.token.is_name && (b.is("!") || b.is("?")) && c.is(":") => Some((a.source + b.source, 3))
      case a :: b :: _ if a.token.is_name && b.is(":") => Some((a.source, 2))
      case _ => None
    }

  private def simp_section(name: String, simp_method: Boolean): Option[Boolean] =
    if (simp_method && (name == "add" || name == "only")) Some(name == "only")
    else if (!simp_method && (name == "simp" || name == "simp add" || name == "simp only")) Some(name == "simp only")
    else None

  private def sections(args: List[Tok], simp_method: Boolean): List[Simp_Section] = {
    val found = new scala.collection.mutable.ListBuffer[Simp_Section]
    var current: Option[Simp_Section] = None
    var rest = args

    def close(): Unit = { current.foreach(found += _); current = None }

    while (rest.nonEmpty) {
      header(rest) match {
        case Some((name, n)) =>
          close()
          current = simp_section(name, simp_method).map(only => Simp_Section(rest.take(n), Nil, only))
          rest = rest.drop(n)
        case None if current.isDefined && Syntax.is_fact_start(rest.head) =>
          val (fact, rest1) = Syntax.take_fact(rest)
          current = current.map(s => s.copy(facts = s.facts :+ fact))
          rest = rest1
        case None => rest = rest.tail
      }
    }
    close()
    found.toList
  }


  /* own(f) replaces simp fact f; add goes in the first simp section or a new one, not `only:` */

  def rewrite(text: String, m: Simp_Method, own: List[Tok] => List[String], add: List[String]): List[(Text.Range, String)] = {
    val target = if (m.sections.exists(_.only)) None else m.sections.headOption
    val section_edits = m.sections.flatMap(s => replace(text, m, s, own, if (target.contains(s)) add else Nil))

    if (add.isEmpty || m.sections.exists(_.only) || target.isDefined) section_edits
    else if (m.wrap) List(m.head.range -> ("(" + m.head.source + " " + m.add_header + " " + add.mkString(" ") + ")"))
    else List(Text.Range(m.stop, m.stop) -> (" " + m.add_header + " " + add.mkString(" ")))
  }

  private def replace(text: String, m: Simp_Method, s: Simp_Section, own: List[Tok] => List[String],
      add: List[String]): List[(Text.Range, String)] = {
    val facts = (s.facts.flatMap(own) ::: add).distinct
    val before = (m.head :: m.args).takeWhile(_ != s.header.head).last
    if (facts == s.facts.map(source(text, _))) Nil
    else if (facts.isEmpty) List(Text.Range(before.range.stop, (s.header ::: s.facts.flatten).last.range.stop) -> "")
    else if (s.facts.isEmpty) List(Text.Range(s.header.last.range.stop, s.header.last.range.stop) -> (" " + facts.mkString(" ")))
    else List(Text.Range(s.facts.head.head.range.start, s.facts.last.last.range.stop) -> facts.mkString(" "))
  }
}
