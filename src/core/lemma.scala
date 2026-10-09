/* isabelle_linter: lemmas, their `by` steps and removable pieces */

package isabelle.isabelle_linter

import isabelle._


/* a proper token with its range in the theory */
sealed case class Tok(token: Token, range: Text.Range) {
  def source: String = token.source
  def is(s: String): Boolean = source == s
}

/* a command with its proper tokens */
sealed case class Cmd(command: Command, offset: Int) {
  def name: String = command.span.name
  def kind: String = command.span.kind.keyword_kind.getOrElse("")

  lazy val tokens: List[Tok] = {
    var o = offset
    command.span.content.flatMap { t =>
      val r = Text.Range(o, o + t.source.length)
      o = r.stop
      if (t.is_proper) Some(Tok(t, r)) else None
    }
  }

  def body: List[Tok] = tokens.drop(1)
  def range: Text.Range = Text.Range(tokens.head.range.start, tokens.last.range.stop)
}

/* something removable from a lemma */
sealed case class Piece(kind: String, text: String, range: Text.Range, line: Int)

/* a `by` step; goal is the command before it; split is `by M1 M2` as (M1, M2) */
sealed case class Step(goal: Cmd, cmd: Cmd, methods: String, facts: List[String],
  split: Option[(String, String)] = None)


sealed case class Lemma(theory: Document.Node.Name, text: String, lines: Line.Document,
    before: Cmd, cmds: List[Cmd], ok: Boolean) {

  /* text */

  def start: Int = cmds.head.range.start
  def stop: Int = cmds.last.range.stop
  def source: String = text.substring(start, stop)
  def key: String = theory.theory + ":" + start

  def line(offset: Int): Int = lines.position(offset).line1
  def line: Int = line(start)

  def replace(range: Text.Range, s: String): String =
    source.substring(0, range.start - start) + s + source.substring(range.stop - start)

  /* the source with ranges deleted, and any keyword left empty */
  def without(ranges: List[Text.Range]): String = {
    val merged =
      ranges.sortBy(_.start).foldLeft(List.empty[Text.Range]) {
        case (r :: rs, s) if s.start <= r.stop => Text.Range(r.start, r.stop max s.stop) :: rs
        case (rs, s) => s :: rs
      }
    Syntax.tidy(merged.foldLeft(source)((s, r) => s.substring(0, r.start - start) + s.substring(r.stop - start)))
  }


  /* `by` steps */

  lazy val steps: List[Step] =
    for ((goal, cmd) <- cmds.zip(cmds.tail) if cmd.name == "by") yield {
      val methods = text.substring(cmd.body.head.range.start, cmd.body.last.range.stop)
      val facts = Syntax.method_facts(cmd.body).map(_.map(_.source).mkString)
      Step(goal, cmd, methods, facts, split(cmd.body))
    }

  private def split(body: List[Tok]): Option[(String, String)] = {
    val (first, rest) =
      if (body.head.is("(")) Syntax.take_group(body, "(", ")") else (List(body.head), body.tail)
    def source(toks: List[Tok]) = text.substring(toks.head.range.start, toks.last.range.stop)
    if (rest.isEmpty) None else Some((source(first), source(rest)))
  }


  /* pieces, in text order */

  lazy val pieces: List[Piece] =
    (assumption_pieces ::: fact_pieces ::: have_pieces ::: apply_pieces).sortBy(_.range.start)

  private def piece(kind: String, toks: List[Tok], from: Int, to: Int): Piece = {
    val start = toks.head.range.start
    Piece(kind, text.substring(start, toks.last.range.stop), Text.Range(from, to), line(start))
  }

  /* toks with the white space before them; a command in mid-line takes the space after it */
  private def piece(kind: String, toks: List[Tok]): Piece = {
    val next = all_tokens.lift(all_tokens.indexOf(toks.last) + 1)
    next match {
      case Some(t) if toks.head.token.is_command && !text.substring(toks.last.range.stop, t.range.start).contains('\n') =>
        piece(kind, toks, toks.head.range.start, t.range.start)
      case _ => piece(kind, toks, end_before(toks.head), toks.last.range.stop)
    }
  }

  private lazy val all_tokens: Vector[Tok] = cmds.flatMap(_.tokens).toVector

  private def end_before(t: Tok): Int =
    all_tokens.lift(all_tokens.indexOf(t) - 1).map(_.range.stop).getOrElse(t.range.start)

  private def assumption_pieces: List[Piece] =
    Syntax.assumptions(cmds.head.body).map({ case (toks, from, to) => piece("assumption", toks, from, to) })

  /* the only fact of `using x` takes the command with it */
  private def fact_pieces: List[Piece] =
    cmds.flatMap { cmd =>
      if (Syntax.fact_commands(cmd.name)) {
        Syntax.fact_items(cmd.body) match {
          case List(_) => List(piece("fact", cmd.tokens))
          case items => items.map(piece("fact", _))
        }
      }
      else if (Syntax.method_commands(cmd.name)) Syntax.method_facts(cmd.body).map(piece("fact", _))
      else Nil
    }

  /* a `have` with its proof and any `then`, `from` ... before it */
  private def have_pieces: List[Piece] =
    for {
      (cmd, i) <- cmds.zipWithIndex
      if cmd.name == "have" || cmd.name == "hence"
      end <- Lemma.goal_end(cmds, i)
      lead_in = cmds.take(i).reverse.takeWhile(c => Syntax.lead_ins(c.name))
      if !in_calculation(lead_in, i - lead_in.length, end)
    } yield {
      val toks = cmds.slice(i - lead_in.length, end + 1).flatMap(_.tokens)
      piece("have", toks).copy(text = cmd.tokens.map(_.source).mkString(" "))
    }

  /* deleting a step of a calculation leaves its `also`, `finally` ... dangling; only a
    `moreover` step can go, together with its `moreover` */
  private def in_calculation(lead_in: List[Cmd], first: Int, last: Int): Boolean = {
    def name(i: Int): String = cmds.lift(i).map(_.name).getOrElse("")
    val chain_before = Syntax.calculation(name(first - 1))
    val chain_after = Syntax.calculation(name(last + 1)) && !lead_in.exists(_.name == "moreover")
    chain_before || chain_after
  }

  private def apply_pieces: List[Piece] =
    cmds.filter(_.name == "apply").map(cmd => piece("apply", cmd.tokens))
}


object Lemma {
  /* ok: every command checked, and no `sorry` or `oops` */
  def read(state: Document.State, snapshot: Document.Snapshot): List[Lemma] = {
    val node = snapshot.node
    val text = node.source
    val lines = Line.Document(text)
    val cmds =
      node.command_iterator().filterNot(_._1.is_ignored)
        .map({ case (c, o) => Cmd(c, o) }).filter(_.tokens.nonEmpty).toList

    def checked(c: Cmd): Boolean = {
      val status = state.command_status(snapshot.version, c.command)
      !status.is_failed && status.is_finished && c.name != "sorry" && c.name != "oops"
    }

    for {
      (cmd, i) <- cmds.zipWithIndex
      if Keyword.theory_goal(cmd.kind) && i > 0
      end <- goal_end(cmds, i)
    } yield {
      val lemma = cmds.slice(i, end + 1)
      Lemma(snapshot.node_name, text, lines, cmds(i - 1), lemma, lemma.forall(checked))
    }
  }

  /* the command that closes the goal opened by cmds(i) */
  def goal_end(cmds: List[Cmd], i: Int): Option[Int] = {
    var depth = 0
    cmds.indices.drop(i).find { j =>
      val kind = cmds(j).kind
      if (Keyword.theory_goal(kind) || Keyword.proof_goal(kind)) depth += 1
      else if (Keyword.qed(kind)) depth -= 1
      else if (Keyword.qed_global(kind)) depth = 0
      depth <= 0
    }
  }
}
