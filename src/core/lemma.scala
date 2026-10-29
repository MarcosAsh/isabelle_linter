/* Lemmas as the lints see them: their commands and tokens, their `by` steps, and the pieces that
   a lemma might not need. */

package isabelle.isabelle_linter

import isabelle._


/* A proper token with its range in the theory. */
sealed case class Tok(token: Token, range: Text.Range) {
  def source: String = token.source
  def is(s: String): Boolean = source == s
}

/* A command with its proper tokens. */
sealed case class Cmd(command: Command, offset: Int) {
  def name: String = command.span.name
  def kind: String = command.span.kind.keyword_kind.getOrElse("")

  lazy val tokens: List[Tok] = {
    var start = offset
    command.span.content.flatMap { token =>
      val range = Text.Range(start, start + token.source.length)
      start = range.stop
      if (token.is_proper) Some(Tok(token, range)) else None
    }
  }

  def body: List[Tok] = tokens.drop(1)
  def range: Text.Range = Text.Range(tokens.head.range.start, tokens.last.range.stop)

  /* The end of the whole span, with any formal comment after the last token. */
  def span_stop: Int = offset + command.length
}

object Cmd {
  /* The commands of a theory, without white space and comments. */
  def read(node: Document.Node): List[Cmd] =
    node.command_iterator().filterNot(_._1.is_ignored)
      .map({ case (command, offset) => Cmd(command, offset) }).filter(_.tokens.nonEmpty).toList
}

/* Something the unused lint might delete from a lemma: an assumption, fact, `have` or `apply`.
   Its range is what to delete, which may be wider than its text. */
sealed case class Piece(kind: String, text: String, range: Text.Range, line: Int)

/* A `by` step, whose goal is the state after the command before it; split is `by M1 M2` as (M1, M2). */
sealed case class Step(goal: Cmd, cmd: Cmd, methods: String, facts: List[String],
  split: Option[(String, String)] = None)


/* A lemma, or a single command like `datatype` for the definition lints. */
sealed case class Lemma(theory: Document.Node.Name, text: String, lines: Line.Document,
    before: Cmd, cmds: List[Cmd], ok: Boolean, downstream: Downstream = Downstream.none) {

  /* text */

  def start: Int = cmds.head.range.start
  def stop: Int = cmds.last.range.stop
  def source: String = text.substring(start, stop).nn
  def key: String = theory.theory + ":" + start

  /* Texts that may use what the lemma defines: the rest of its theory, then the theories after it. */
  def later: List[String] = downstream.theory.substring(stop).nn :: downstream.texts

  def line(offset: Int): Int = lines.position(offset).line1
  def line: Int = line(start)

  def replace(range: Text.Range, s: String): String = replace_all(List(range -> s))

  def replace_all(edits: List[(Text.Range, String)]): String = Lemma.edit(source, start, edits)

  /* The source with the ranges deleted, then tidied of any keyword left empty. */
  def without(ranges: List[Text.Range]): String = {
    val merged =
      ranges.sortBy(_.start).foldLeft(List.empty[Text.Range]) {
        case (last :: done, next) if next.start <= last.stop => Text.Range(last.start, last.stop max next.stop) :: done
        case (done, next) => next :: done
      }
    val deleted =
      merged.foldLeft(source)((text, range) => text.substring(0, range.start - start).nn + text.substring(range.stop - start))
    Syntax.tidy(deleted)
  }


  /* `by` steps */

  lazy val steps: List[Step] =
    for ((goal, cmd) <- cmds.zip(cmds.tail) if cmd.name == "by") yield {
      val methods = text.substring(cmd.body.head.range.start, cmd.body.last.range.stop).nn
      val facts = Syntax.method_facts(cmd.body).map(_.map(_.source).mkString)
      Step(goal, cmd, methods, facts, split(cmd.body))
    }

  private def split(body: List[Tok]): Option[(String, String)] = {
    val (first, rest) =
      if (body.head.is("(")) Syntax.take_group(body, "(", ")") else (List(body.head), body.tail)
    def source(toks: List[Tok]) = text.substring(toks.head.range.start, toks.last.range.stop).nn
    if (rest.nonEmpty) Some((source(first), source(rest)))
    else if (first.head.is("(")) split_semicolon(first.tail.init).map {
      case (m1, m2) => ("(" + source(m1) + ")", "(" + source(m2) + ")")
    }
    else None
  }

  /* `M1; M2 ...` at the top level of a group runs like `M1 M2` when M2 works on every goal. */
  private def split_semicolon(toks: List[Tok]): Option[(List[Tok], List[Tok])] = {
    var depth = 0
    val semicolon = toks.indexWhere { t =>
      if (t.is("(")) depth += 1 else if (t.is(")")) depth -= 1
      depth == 0 && t.is(";")
    }
    if (semicolon <= 0 || semicolon == toks.length - 1) None
    else Some((toks.take(semicolon), toks.drop(semicolon + 1)))
  }


  /* pieces */

  lazy val pieces: List[Piece] =
    (assumption_pieces ::: fact_pieces ::: have_pieces ::: apply_pieces).sortBy(_.range.start)

  private def piece(kind: String, toks: List[Tok], deletion: Text.Range): Piece = {
    val start = toks.head.range.start
    Piece(kind, text.substring(start, toks.last.range.stop).nn, deletion, line(start))
  }

  /* toks with the white space before them; a command in mid-line takes the space after it. */
  private def piece(kind: String, toks: List[Tok]): Piece = {
    val start = toks.head.range.start
    val stop = toks.last.range.stop
    all_tokens.lift(all_tokens.indexOf(toks.last) + 1) match {
      case Some(next) if toks.head.token.is_command && !text.substring(stop, next.range.start).nn.contains('\n') =>
        piece(kind, toks, Text.Range(start, next.range.start))
      case _ => piece(kind, toks, Text.Range(end_before(toks.head), stop))
    }
  }

  private lazy val all_tokens: Vector[Tok] = cmds.flatMap(_.tokens).toVector

  private def end_before(t: Tok): Int =
    all_tokens.lift(all_tokens.indexOf(t) - 1).map(_.range.stop).getOrElse(t.range.start)

  private def assumption_pieces: List[Piece] =
    Syntax.assumptions(cmds.head.body).map({ case (toks, deletion) => piece("assumption", toks, deletion) })

  /* The only fact of `using x` takes the command with it. */
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

  /* A `have` goes with its proof and any `then`, `from` ... before it. */
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

  /* Deleting a step of a calculation leaves its `also`, `finally` ... dangling; only a `moreover`
     step can go, together with its `moreover`. */
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
  /* In an interactive PIDE session a lemma with `sorry` or `\<proof>` closes without a real proof. */
  val cheats: Set[String] = Set("sorry", "\\<proof>", "oops")

  private def checked(state: Document.State, snapshot: Document.Snapshot)(c: Cmd): Boolean = {
    val status = state.command_status(snapshot.version, c.command)
    !status.is_failed && status.is_finished && !cheats(c.name)
  }

  /* A lemma is ok if every command checked and none of them cheats. */
  def read(state: Document.State, snapshot: Document.Snapshot): List[Lemma] = {
    val text = snapshot.node.source
    val lines = Line.Document(text)
    val cmds = Cmd.read(snapshot.node)
    for {
      (cmd, i) <- cmds.zipWithIndex
      if theorem_commands(cmd.name) && i > 0
      end <- goal_end(cmds, i)
    } yield {
      val lemma = cmds.slice(i, end + 1)
      Lemma(snapshot.node_name, text, lines, cmds(i - 1), lemma, lemma.forall(checked(state, snapshot)))
    }
  }

  val definition_commands: Set[String] = Set("datatype", "codatatype", "fun")

  def definitions(state: Document.State, snapshot: Document.Snapshot, downstream: Downstream): List[Lemma] = {
    val text = snapshot.node.source
    val lines = Line.Document(text)
    val cmds = Cmd.read(snapshot.node)
    for ((cmd, i) <- cmds.zipWithIndex if definition_commands(cmd.name) && i > 0)
      yield Lemma(snapshot.node_name, text, lines, cmds(i - 1), List(cmd), checked(state, snapshot)(cmd), downstream)
  }

  /* Goals stored as a theorem, whose forked proofs Thm.consolidate_theory waits for (an instance's
     may fail unseen). Not schematic_goal: its proof chooses the statement, so another may differ. */
  val theorem_commands: Set[String] =
    Set("lemma", "theorem", "corollary", "proposition")

  /* The index of the command that closes the goal opened by cmds(i). */
  def goal_end(cmds: List[Cmd], i: Int): Option[Int] = {
    var depth = 0
    cmds.indices.drop(i).find { j =>
      val kind = cmds(j).kind
      if (Keyword.theory_goal_kinds(kind) || Keyword.proof_goal_kinds(kind)) depth += 1
      else if (Keyword.qed_kinds(kind)) depth -= 1
      else if (Keyword.qed_global_kinds(kind)) depth = 0
      depth <= 0
    }
  }

  /* Apply disjoint edits to text, which starts at offset start of its theory. */
  def edit(text: String, start: Int, edits: List[(Text.Range, String)]): String =
    edits.sortBy(_._1.start).reverse.foldLeft(text) { case (edited, (range, replacement)) =>
      edited.substring(0, range.start - start).nn + replacement + edited.substring(range.stop - start)
    }
}
