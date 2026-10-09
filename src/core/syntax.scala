/* isabelle_linter: facts and assumptions in command tokens */

package isabelle.isabelle_linter

import isabelle._


object Syntax {
  val fact_commands: Set[String] = Set("using", "unfolding", "from", "with")
  val method_commands: Set[String] = Set("by", "apply", "proof")

  /* go with the `have` after them */
  val lead_ins: Set[String] = Set("then", "from", "with", "moreover")

  val calculation: Set[String] = Set("also", "finally", "moreover", "ultimately")

  val fact_methods: Set[String] = Set("metis", "meson", "smt", "argo")
  val fact_sections: Set[String] = Set("add", "simp", "intro", "elim", "dest", "iff", "split", "cong", "only")

  /* a keyword left without arguments */
  val empty_keyword: String =
    "\\b(assumes|using|unfolding|from|with)\\s+" +
      "(?=(shows|obtains|by|apply|proof|using|unfolding|have|show|hence|thus|obtain)\\b)"


  /* like `add:` before a closing paren */
  val empty_section: String = "\\s+\\w+!?:\\s*(?=\\))"

  /* `by (simp)` left after removing all its facts, to `by simp` */
  val bare_method: String = "\\b(by|apply)\\s+\\((\\w+)\\)"

  /* text after a deletion */
  def tidy(s: String): String =
    s.replaceAll(empty_keyword, "").replaceAll(empty_section, "").replaceAll(bare_method, "$1 $2")

  /* a fact: name, optional (selection), optional [attributes] */

  def is_fact_start(t: Tok): Boolean =
    (t.token.is_name && !t.token.is_keyword) ||
      t.token.kind == Token.Kind.CARTOUCHE ||
      t.token.kind == Token.Kind.ALT_STRING

  def take_fact(toks: List[Tok]): (List[Tok], List[Tok]) = {
    val name = toks.head
    val (selection, rest1) =
      toks.tail match {
        case t :: _ if t.is("(") && t.range.start == name.range.stop => take_group(toks.tail, "(", ")")
        case rest => (Nil, rest)
      }
    val (attributes, rest2) =
      rest1 match {
        case t :: _ if t.is("[") => take_group(rest1, "[", "]")
        case rest => (Nil, rest)
      }
    (name :: selection ::: attributes, rest2)
  }

  def take_group(toks: List[Tok], open: String, close: String): (List[Tok], List[Tok]) = {
    var depth = 0
    val n = toks.indexWhere { t =>
      if (t.is(open)) depth += 1 else if (t.is(close)) depth -= 1
      depth == 0
    }
    if (n < 0) (toks, Nil) else toks.splitAt(n + 1)
  }


  def fact_items(toks: List[Tok]): List[List[Tok]] =
    toks match {
      case Nil => Nil
      case t :: _ if is_fact_start(t) =>
        val (item, rest) = take_fact(toks)
        item :: fact_items(rest)
      case _ :: rest => fact_items(rest)
    }


  /* arguments of fact_methods, and lists like `simp add:` */
  def method_facts(toks: List[Tok]): List[List[Tok]] = {
    val facts = new scala.collection.mutable.ListBuffer[List[Tok]]
    var rest = toks
    var depth = 0
    var listing: Option[Int] = None   // paren depth of the current fact list

    while (rest.nonEmpty) {
      val t = rest.head
      section_header(rest) match {
        case Some((name, n)) =>
          listing = if (fact_sections(name)) Some(depth) else None
          rest = rest.drop(n)

        case None if t.token.is_name && fact_methods(t.source) =>
          listing = Some(depth)
          rest = skip_options(rest.tail)

        case None if listing.contains(depth) && is_fact_start(t) =>
          val (item, rest1) = take_fact(rest)
          facts += item
          rest = rest1

        case None =>
          if (t.is("(")) depth += 1
          else if (t.is(")")) depth -= 1
          if (listing.exists(d => depth < d) || (listing.contains(depth) && separators(t.source))) listing = None
          rest = rest.tail
      }
    }
    facts.toList
  }

  private val separators = Set(",", ";", "|", "+", "?")

  private def section_header(toks: List[Tok]): Option[(String, Int)] =
    toks match {
      case a :: b :: _ if a.token.is_name && b.is(":") => Some((a.source, 2))
      case a :: b :: c :: _ if a.token.is_name && b.is("!") && c.is(":") => Some((a.source, 3))
      case _ => None
    }

  /* like smt (verit) */
  private def skip_options(toks: List[Tok]): List[Tok] =
    toks match {
      case t :: _ if t.is("(") => take_group(toks, "(", ")")._2
      case _ => toks
    }


  /* each clause with its deletion range, including `assumes` or an `and` */
  def assumptions(toks: List[Tok]): List[(List[Tok], Int, Int)] = {
    def keyword(t: Tok, names: String*): Boolean = t.token.is_keyword && names.exists(t.is)

    val start = toks.indexWhere(keyword(_, "assumes"))
    val stop = toks.indexWhere(keyword(_, "shows", "obtains"), start max 0)
    if (start < 0 || stop < 0) return Nil

    val clauses = split_and(toks.slice(start + 1, stop))
    def after(t: Tok): Tok = toks(toks.indexOf(t) + 1)

    clauses.zipWithIndex.map {
      case (c, _) if clauses.length == 1 =>
        val from = if (start > 0) toks(start - 1).range.stop else toks(start).range.start
        (c, from, c.last.range.stop)
      case (c, 0) => (c, toks(start).range.stop, after(c.last).range.stop)
      case (c, k) => (c, clauses(k - 1).last.range.stop, c.last.range.stop)
    }
  }

  def split_and(toks: List[Tok]): List[List[Tok]] =
    toks.foldRight(List(List.empty[Tok])) { (t, acc) =>
      if (t.is("and") && t.token.is_keyword) Nil :: acc else (t :: acc.head) :: acc.tail
    }.filter(_.nonEmpty)
}
