/* Facts, method arguments and assumptions in the tokens of a command, and the tidying of a text
   after a deletion. */

package isabelle.isabelle_linter

import isabelle._


object Syntax {
  val fact_commands: Set[String] = Set("using", "unfolding", "from", "with")
  val method_commands: Set[String] = Set("by", "apply", "proof")

  /* These go with the `have` after them. */
  val lead_ins: Set[String] = Set("then", "from", "with", "moreover")

  val calculation: Set[String] = Set("also", "finally", "moreover", "ultimately")

  val fact_methods: Set[String] = Set("metis", "meson", "smt", "argo")
  val fact_sections: Set[String] = Set("add", "simp", "intro", "elim", "dest", "iff", "split", "cong", "only")

  /* A keyword left without arguments. */
  val empty_keyword: String =
    "\\b(assumes|using|unfolding|from|with)\\s+" +
      "(?=(shows|obtains|by|apply|proof|using|unfolding|have|show|hence|thus|obtain)\\b)"

  /* A section like `add:` left before a closing paren. */
  val empty_section: String = "\\s+\\w+!?:\\s*(?=\\))"

  /* `by (simp)` left after removing all its facts becomes `by simp`. */
  val bare_method: String = "\\b(by|apply)\\s+\\((\\w+)\\)"

  def tidy(s: String): String =
    s.replaceAll(empty_keyword, "").nn.replaceAll(empty_section, "").nn.replaceAll(bare_method, "$1 $2").nn

  /* A fact is a name, an optional (selection) and optional [attributes]. */

  def is_fact_start(t: Tok): Boolean =
    (t.token.is_name && !t.token.is_keyword) ||
      t.token.kind == Token.Kind.CARTOUCHE ||
      t.token.kind == Token.Kind.ALT_STRING

  def take_fact(toks: List[Tok]): (List[Tok], List[Tok]) = {
    val name = toks.head
    val (selection, after_selection) =
      toks.tail match {
        case t :: _ if t.is("(") && t.range.start == name.range.stop => take_group(toks.tail, "(", ")")
        case rest => (Nil, rest)
      }
    val (attributes, rest) =
      after_selection match {
        case t :: _ if t.is("[") => take_group(after_selection, "[", "]")
        case rest => (Nil, rest)
      }
    (name :: selection ::: attributes, rest)
  }

  def take_group(toks: List[Tok], open: String, close: String): (List[Tok], List[Tok]) = {
    var depth = 0
    val closing = toks.indexWhere { t =>
      if (t.is(open)) depth += 1 else if (t.is(close)) depth -= 1
      depth == 0
    }
    if (closing < 0) (toks, Nil) else toks.splitAt(closing + 1)
  }


  def fact_items(toks: List[Tok]): List[List[Tok]] =
    toks match {
      case Nil => Nil
      case t :: _ if is_fact_start(t) =>
        val (item, rest) = take_fact(toks)
        item :: fact_items(rest)
      case _ :: rest => fact_items(rest)
    }


  /* The arguments of fact_methods, and the facts of sections like `simp add:`. */
  def method_facts(toks: List[Tok]): List[List[Tok]] = {
    val facts = new scala.collection.mutable.ListBuffer[List[Tok]]
    var rest = toks
    var depth = 0
    var listing: Option[Int] = None   /* the paren depth of the current list of facts */

    while (rest.nonEmpty) {
      val t = rest.head
      section_header(rest) match {
        case Some((name, length)) =>
          listing = if (fact_sections(name)) Some(depth) else None
          rest = rest.drop(length)

        case None if t.token.is_name && fact_methods(t.source) =>
          listing = Some(depth)
          rest = skip_options(rest.tail)

        case None if listing.contains(depth) && is_fact_start(t) =>
          val (item, after) = take_fact(rest)
          facts += item
          rest = after

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

  /* A header like `add:` or `simp!:`, with its length in tokens. */
  private def section_header(toks: List[Tok]): Option[(String, Int)] =
    toks match {
      case name :: colon :: _ if name.token.is_name && colon.is(":") => Some((name.source, 2))
      case name :: bang :: colon :: _ if name.token.is_name && bang.is("!") && colon.is(":") => Some((name.source, 3))
      case _ => None
    }

  /* The options of a method, like (verit) in `smt (verit)`. */
  private def skip_options(toks: List[Tok]): List[Tok] =
    toks match {
      case t :: _ if t.is("(") => take_group(toks, "(", ")")._2
      case _ => toks
    }


  /* Each clause with its deletion range, which takes `assumes` or an `and` with it. */
  def assumptions(toks: List[Tok]): List[(List[Tok], Text.Range)] = {
    def keyword(t: Tok, names: String*): Boolean = t.token.is_keyword && names.exists(t.is)

    val start = toks.indexWhere(keyword(_, "assumes"))
    val stop = toks.indexWhere(keyword(_, "shows", "obtains"), start max 0)
    if (start < 0 || stop < 0) return Nil

    val clauses = split_and(toks.slice(start + 1, stop))
    def after(t: Tok): Tok = toks(toks.indexOf(t) + 1)

    clauses.zipWithIndex.map {
      case (clause, _) if clauses.length == 1 =>
        val from = if (start > 0) toks(start - 1).range.stop else toks(start).range.start
        (clause, Text.Range(from, clause.last.range.stop))
      case (clause, 0) => (clause, Text.Range(toks(start).range.stop, after(clause.last).range.stop))
      case (clause, k) => (clause, Text.Range(clauses(k - 1).last.range.stop, clause.last.range.stop))
    }
  }

  def split_and(toks: List[Tok]): List[List[Tok]] =
    toks.foldRight(List(List.empty[Tok])) { (t, acc) =>
      if (t.is("and") && t.token.is_keyword) Nil :: acc else (t :: acc.head) :: acc.tail
    }.filter(_.nonEmpty)
}
