/* The text side of simp_scope: [simp] notes and their scope, the methods of a command that read
   the simpset, and the edits that change their simp facts. */

package isabelle.isabelle_linter

import isabelle._


/* A note's [simp] facts, the name it binds them to, and the ranges that delete its [simp]. */
sealed case class Simp_Note(cmd: Cmd, facts: List[String], name: Option[String], attributes: List[Text.Range])

/* A section like `simp add: a b`, or with only `simp only: a b`. */
sealed case class Simp_Section(header: List[Tok], facts: List[List[Tok]], only: Boolean)

/* A method that reads the simpset; with wrap it needs parentheses to take arguments. */
sealed case class Simp_Method(head: Tok, args: List[Tok], sections: List[Simp_Section], wrap: Boolean) {
  def add_header: String = if (Simp_Text.simp_methods(head.source)) "add:" else "simp add:"
  def stop: Int = (head :: args).last.range.stop
}


object Simp_Text {
  val simp_methods: Set[String] = Set("simp", "simp_all")
  val clasimp_methods: Set[String] = Set("auto", "force", "fastforce", "clarsimp", "bestsimp", "slowsimp")

  def reads_simpset(t: Tok): Boolean = t.token.is_name && (simp_methods(t.source) || clasimp_methods(t.source))

  def source(text: String, toks: List[Tok]): String = text.substring(toks.head.range.start, toks.last.range.stop).nn


  /* `note NAME[simp] = a b`, `note [simp] = a b`, `note a[simp] b[simp]`; also declare */

  private def is_simp(toks: List[Tok]): Boolean = toks.map(_.source) == List("[", "simp", "]")

  /* A fact item as the fact and its attributes. */
  private def split_attributes(item: List[Tok]): (List[Tok], List[Tok]) = item.span(t => !t.is("["))

  /* Notes with more than a plain [simp], or with `and` or `this`, are left alone. */
  def note(text: String, cmd: Cmd): Option[Simp_Note] = {
    val body = cmd.body
    val equals = outside_brackets(body).indexWhere(_.exists(_.is("=")))
    val (binding, rest) = if (equals < 0) (Nil, body) else (body.take(equals), body.drop(equals + 1))
    val items = Syntax.fact_items(rest)
    def attributes(item: List[Tok]): List[Tok] = split_attributes(item)._2
    val binds_simp = binding.exists(_.is("simp"))

    val unsupported =
      !Set("note", "declare", "lemmas")(cmd.name) || body.exists(t => t.is("and") || t.is("this")) || items.isEmpty ||
        (binds_simp && !is_simp(binding.dropWhile(!_.is("[")))) ||
        items.exists(item => attributes(item).exists(_.is("simp")) && !is_simp(attributes(item)))

    val simp_items = items.filter(item => is_simp(attributes(item)))
    if (unsupported) None
    else if (binds_simp && simp_items.isEmpty) Some(bound(text, cmd, binding, rest, items))
    else if (binds_simp || simp_items.isEmpty) None
    else {
      val facts = simp_items.map(item => source(text, split_attributes(item)._1))
      val ranges = simp_items.map(item => Text.Range(split_attributes(item)._1.last.range.stop, item.last.range.stop))
      Some(Simp_Note(cmd, facts, None, ranges))
    }
  }

  /* `NAME[simp] = a b` loses `[simp]`, and `[simp] = a b` loses `[simp] =`. */
  private def bound(text: String, cmd: Cmd, binding: List[Tok], rest: List[Tok], items: List[List[Tok]]): Simp_Note = {
    val facts = items.map(source(text, _))
    binding match {
      case name :: _ if name.token.is_name =>
        Simp_Note(cmd, facts, Some(name.source), List(Text.Range(name.range.stop, binding.last.range.stop)))
      case _ =>
        Simp_Note(cmd, facts, None, List(Text.Range(binding.head.range.start, rest.head.range.start)))
    }
  }

  /* The tokens, with None for those inside brackets. */
  private def outside_brackets(toks: List[Tok]): List[Option[Tok]] = {
    val brackets = depths(toks.toVector)._2
    toks.zipWithIndex.map({ case (t, k) => if (brackets(k) == 0) Some(t) else None })
  }


  /* The commands after cmds(i) to the end of its block. */
  def scope(cmds: List[Cmd], i: Int): List[Cmd] = {
    var depth = 0
    cmds.drop(i + 1).takeWhile { c =>
      if (Keyword.proof_open_kinds(c.kind)) depth += 1
      else if (Keyword.proof_close_kinds(c.kind)) depth -= 1
      depth >= 0 && !(depth == 0 && c.kind == Keyword.NEXT_BLOCK) && !Keyword.qed_global_kinds(c.kind)
    }
  }


  /* Methods at the top of the command, or after `(`, `,`, `;` or `|`, like auto in `(cases x; auto)`. */

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

  /* At the top of `by`, a method takes no arguments without parentheses. */
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

  /* A section header with its length in tokens. */
  private def header(toks: List[Tok]): Option[(String, Int)] =
    toks match {
      case modifier :: kind :: colon :: _
        if modifiers(modifier.source) && Set("add", "del", "only", "flip")(kind.source) && colon.is(":") =>
          Some((modifier.source + " " + kind.source, 3))
      case name :: mark :: colon :: _ if name.token.is_name && (mark.is("!") || mark.is("?")) && colon.is(":") =>
        Some((name.source + mark.source, 3))
      case name :: colon :: _ if name.token.is_name && colon.is(":") => Some((name.source, 2))
      case _ => None
    }

  /* Some(only) for a section that adds simp facts, with only for `only:`. */
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
        case Some((name, length)) =>
          close()
          current = simp_section(name, simp_method).map(only => Simp_Section(rest.take(length), Nil, only))
          rest = rest.drop(length)
        case None if current.isDefined && Syntax.is_fact_start(rest.head) =>
          val (fact, after) = Syntax.take_fact(rest)
          current = current.map(section => section.copy(facts = section.facts :+ fact))
          rest = after
        case None => rest = rest.tail
      }
    }
    close()
    found.toList
  }


  /* own(fact) replaces a simp fact. The facts to add go in the first simp section, or a new one,
     but never next to `only:`. */

  def rewrite(text: String, method: Simp_Method, own: List[Tok] => List[String],
      add: List[String]): List[(Text.Range, String)] = {
    val only = method.sections.exists(_.only)
    val target = if (only) None else method.sections.headOption
    val section_edits =
      method.sections.flatMap(section => replace(text, method, section, own, if (target.contains(section)) add else Nil))
    val added = method.add_header + " " + add.mkString(" ")

    if (add.isEmpty || only || target.isDefined) section_edits
    else if (method.wrap) List(method.head.range -> ("(" + method.head.source + " " + added + ")"))
    else List(Text.Range(method.stop, method.stop) -> (" " + added))
  }

  private def replace(text: String, method: Simp_Method, section: Simp_Section, own: List[Tok] => List[String],
      add: List[String]): List[(Text.Range, String)] = {
    val facts = (section.facts.flatMap(own) ::: add).distinct
    val header_end = section.header.last.range.stop
    val before = (method.head :: method.args).takeWhile(_ != section.header.head).last
    if (facts == section.facts.map(source(text, _))) Nil
    else if (facts.isEmpty) List(Text.Range(before.range.stop, (section.header ::: section.facts.flatten).last.range.stop) -> "")
    else if (section.facts.isEmpty) List(Text.Range(header_end, header_end) -> (" " + facts.mkString(" ")))
    else List(Text.Range(section.facts.head.head.range.start, section.facts.last.last.range.stop) -> facts.mkString(" "))
  }
}
