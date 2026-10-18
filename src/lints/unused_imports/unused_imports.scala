/* unused_imports: theory imports that can go, checked by building an edited copy of the session */

package isabelle.isabelle_linter

import isabelle._


object Unused_Imports {
  val name = "unused_imports"

  /* a theory and one of its imports, by long name */
  type Edge = (String, String)


  /* Ask the prover, for each theory of the session, which theories it uses. Propose the
    imports that another import already brings in, then each import whose removal leaves
    every theory of the session with the theories it uses. Build a copy with the proposed
    removals; on failure keep the ones that touch no failed theory and try the others again,
    several at a time when no theory sees two of them. Report the removals of the last
    build that succeeded, with the time and critical path before and after. */


  /* the prover's view of a theory: the theories it uses, and what each theory in its context
    contributes (facts, simp rules, constants, types, classes) */
  sealed case class Uses(uses: Set[String], context: Map[String, List[Int]])

  private val entity_kinds =
    Set(Markup.CONSTANT, Markup.TYPE_NAME, Markup.CLASS, Markup.FACT, Markup.LOCALE, Markup.BUNDLE,
      Markup.METHOD, Markup.ATTRIBUTE)

  /* the entities the text refers to, as "kind name" */
  def refs(snapshot: Document.Snapshot): List[String] =
    snapshot.select(Text.Range(0, snapshot.node.source.length), Markup.Elements(Markup.ENTITY), _ =>
      {
        case Text.Info(_, XML.Elem(markup @ Markup.Entity(kind, name), _))
        if entity_kinds(kind) && Markup.Entity.Ref.unapply(markup).isDefined => Some(kind + " " + name)
        case _ => None
      }).map(_.info).distinct

  private def commands(snapshot: Document.Snapshot): List[Cmd] =
    snapshot.node.command_iterator().filterNot(_._1.is_ignored)
      .map({ case (c, o) => Cmd(c, o) }).filter(_.tokens.nonEmpty).toList

  /* the commands and minor keywords of the text */
  def keywords_used(snapshot: Document.Snapshot): Set[String] =
    commands(snapshot).flatMap(_.tokens.filter(t => t.token.is_command || t.token.is_keyword).map(_.source)).toSet

  /* asked on the command before `end`, which sees the whole theory */
  def question(snapshot: Document.Snapshot, timeout: Time): Option[Pide.Question] =
    commands(snapshot).reverse match {
      case _ :: last :: _ =>
        Some(Pide.Question(name + ":" + snapshot.node_name.theory, snapshot.node_name, last.command,
          "linter_imports", refs(snapshot), timeout))
      case _ => None
    }

  def read_uses(answer: Pide.Answer): Option[Uses] =
    if (!answer.closes) None
    else {
      def words(s: String, sep: Char): List[String] = Library.space_explode(sep, s).filter(_.nonEmpty)
      val context =
        words(answer.get("context").getOrElse(""), ';').map(words(_, ' ')).collect({
          case theory :: counts if counts.length == 5 => theory -> counts.map(Value.Int.parse) })
      Some(Uses(words(answer.get("uses").getOrElse(""), ' ').toSet, context.toMap))
    }

  /* the theories that declare each keyword in their header */
  def keyword_theories(scope: Scope): Map[String, Set[String]] =
    (for {
      (thy, entry) <- scope.known.toList
      (keyword, _) <- entry.header.keywords
    } yield keyword -> thy).groupMap(_._1)(_._2).map({ case (k, ts) => k -> ts.toSet })

  /* a theory also uses the theories that declare its keywords */
  def ask_uses(options: Options, scope: Scope, dirs: List[Path], progress: Progress): Map[String, Uses] = {
    val declared = keyword_theories(scope)
    Pide.check(options, scope.session, dirs, progress) { checked =>
      /* a whole theory's facts and derivations, not one lemma */
      val timeout = Time.seconds(10 * options.real("linter_timeout"))
      val asked = checked.snapshots.flatMap(s => question(s, timeout).map(s -> _))
      val log = proper_string(options.string("linter_log")).map(Path.explode)
      val answers = Pide.rounds(checked.session, name, progress, log, options.int("linter_batch"))(_ => asked.map(_._2))
      val result =
        (for {
          (snapshot, q) <- asked
          uses <- read_uses(answers(q.key))
          keyword_uses = keywords_used(snapshot).flatMap(declared.getOrElse(_, Set.empty))
        } yield snapshot.node_name.theory -> uses.copy(uses = uses.uses ++ keyword_uses)).toMap
      val missing = scope.own.filterNot(result.isDefinedAt)
      if (missing.nonEmpty) {
        progress.echo_warning(name + ": no answer for " + commas(missing) + ", so nothing may leave their contexts")
      }
      result
    }
  }


  /* the session, and the sessions of its ROOT file that build on it */

  sealed case class Scope(
    session: String,
    structure: Sessions.Structure,
    dir: Path,
    sessions: List[String],
    elsewhere: List[String],
    theories: Map[String, List[String]],
    known: Map[String, Document.Node.Entry]
  ) {
    def own: List[String] = theories(session)
    def info: Sessions.Info = structure(session)

    /* the theories the ROOT names for the session */
    def listed: Set[String] =
      info.theories.flatMap(_._2).map(x => Thy_Header.import_name(x._1)).map(a =>
        if (Long_Name.is_qualified(a) || info.global_theories.contains(a)) a else Long_Name.qualify(session, a)).toSet

    /* how the ROOT can name a theory of the session */
    def root_entry(thy: String): String =
      File.relative_path(info.dir.canonical, path(thy).canonical).map(_.implode.stripSuffix(".thy"))
        .getOrElse(Long_Name.base_name(thy))
    def checked: List[String] = sessions.flatMap(theories)
    def graph: Theory_Graph = new Theory_Graph(known.map({ case (t, e) => t -> e.header.imports.map(_.theory) }))
    def path(thy: String): Path = known(thy).name.path

    /* the header's imports, as the text has them */
    def editable(thy: String): Boolean =
      Patch.import_ranges(File.read(path(thy))).length == known(thy).header.imports.length

    /* a theory of the copy */
    def copy_path(copy: Path, thy: String): Path =
      copy + File.relative_path(dir.canonical, path(thy).canonical).getOrElse(error("Theory outside " + dir))

    /* outside the Isabelle distribution, or everything if the option says so */
    def in_scope(thy: String, distribution: Boolean): Boolean = {
      val q = structure.theory_qualifier(thy)
      distribution || !structure.defined(q) ||
        File.relative_path(Path.explode("~~").canonical, structure(q).dir.canonical).isEmpty
    }
  }

  private def root_file(info: Sessions.Info): Path =
    Path.explode(Position.File.get(info.pos)).canonical

  def scope(options: Options, session: String, dirs: List[Path], progress: Progress): Scope = {
    val structure = Sessions.load_structure(options, dirs = dirs)
    val root = root_file(structure(session))
    val (same, elsewhere) =
      structure.imports_descendants(List(session)).filter(_ != session)
        .partition(s => root_file(structure(s)) == root)
    val sessions = session :: same
    val deps = Sessions.deps(structure.selection(Sessions.Selection(sessions = sessions)), progress = progress)
    val theories = sessions.map(s => s -> deps(s).proper_session_theories.map(_.theory)).toMap
    val known = sessions.flatMap(deps(_).known_theories).toMap
    Scope(session, structure, root.dir, sessions, elsewhere, theories, known)
  }


  /* proposals */

  /* theories of the session that only imports kept in it: they go into the ROOT's theories */
  def dropped(scope: Scope, edited: Theory_Graph): List[String] = {
    val listed = scope.listed
    scope.own.filterNot(t => listed(t) || listed.exists(edited.ancestors(_)(t)))
  }

  /* each theory of the session keeps an import and the theories it uses */
  def acceptable(scope: Scope, uses: Map[String, Uses], graph: Theory_Graph, edited: Theory_Graph): Boolean = {
    scope.own.forall { t =>
      edited.imports_of(t).nonEmpty || graph.imports_of(t).isEmpty
    } && scope.own.forall { t =>
      val needed = uses.get(t).map(_.uses & graph.ancestors(t)).getOrElse(graph.ancestors(t))
      needed.subsetOf(edited.ancestors(t))
    }
  }

  /* the redundant imports, then each other import that keeps the session acceptable */
  def propose(scope: Scope, uses: Map[String, Uses], graph: Theory_Graph, distribution: Boolean): Set[Edge] = {
    def candidates(f: String => List[String]): List[Edge] =
      for (t <- scope.own if scope.editable(t); a <- f(t).distinct if scope.in_scope(a, distribution))
      yield (t, a)
    val redundant = candidates(graph.redundant).toSet
    candidates(graph.imports_of).filterNot(redundant).foldLeft(redundant) { (removed, e) =>
      if (acceptable(scope, uses, graph, graph.without(removed + e))) removed + e else removed
    }
  }


  /* builds of the copy, each with its removals written into the copy's original text */

  def indices(graph: Theory_Graph, thy: String, removed: Set[Edge]): Set[Int] =
    graph.imports_of(thy).zipWithIndex.collect({ case (a, i) if removed((thy, a)) => i }).toSet

  /* timings: seconds of each theory's commands; changed: theories that build but no longer export
    what they did before */
  sealed case class Round(removed: Set[Edge], built: Map[String, Patch.Built], timings: Map[String, Double],
      changed: Set[String]) {
    def ok: Boolean = built.values.forall(_.ok) && changed.isEmpty
    def cancelled: Set[String] = built.collect({ case (s, b) if b.cancelled => s }).toSet
    def content: Map[String, Set[String]] =
      built.values.flatMap(_.content).map({ case (t, x) => Patch.original_theory(t) -> x }).toMap
    def finished: Set[String] = content.keySet -- changed
  }

  private class Copy(options: Options, dirs: List[Path], scope: Scope, dir: Path, progress: Progress) {
    Patch.copy(scope.dir, dir)
    val sessions: List[String] = scope.sessions.map(Patch.patched)
    private val root = File.read(dir + Sessions.ROOT)
    private val texts = scope.own.map(t => t -> File.read(scope.copy_path(dir, t))).toMap
    private val files = scope.checked.map(t => scope.copy_path(dir, t).canonical.implode -> t).toMap
    private val graph = scope.graph
    private var before: Map[String, Set[String]] = Map.empty
    var builds = 0

    private def write(removed: Set[Edge]): Unit = {
      for ((t, text) <- texts) File.write(scope.copy_path(dir, t), Patch.remove_imports(text, indices(graph, t, removed)))
      val added = dropped(scope, graph.without(removed)).map(scope.root_entry)
      File.write(dir + Sessions.ROOT, Patch.add_theories(root, Patch.patched(scope.session), added))
    }

    def build(removed: Set[Edge]): Round = {
      write(removed)
      builds += 1
      progress.echo(name + ": build " + builds + ", " + removed.size + " imports removed")
      val built = Patch.build(options, dirs ::: List(dir), sessions, progress)
      val timings = built.values.flatMap(_.times).flatMap({ case (f, x) => files.get(f).map(_ -> x) }).toMap
      val round0 = Round(removed, built.map({ case (s, b) => s.stripSuffix(Patch.suffix) -> b }), timings, Set.empty)
      if (builds == 1) before = round0.content
      val round = round0.copy(changed = round0.content.keySet.filter(t => before.get(t) != round0.content.get(t)))
      for ((s, b) <- round.built if !b.ok && !b.cancelled) {
        val error = b.errors.find(!_.startsWith("Failed to load theory")).orElse(b.errors.headOption).getOrElse("")
        progress.echo(name + ": " + s + " failed: " + error.linesIterator.take(2).mkString(" "))
      }
      if (round.changed.nonEmpty) progress.echo(name + ": changed exports: " + commas(round.changed.toList.sorted))
      round
    }
  }


  /* the search */

  sealed case class Result(removed: Set[Edge], round: Round, rejected: List[(Edge, String)],
    untried: List[Edge], builds: Int)

  private class Search(copy: Copy, scope: Scope, baseline: Round, max_builds: Int) {
    private val graph = scope.graph
    private val theories = scope.checked
    private val checked = theories.toSet

    /* the theories whose ancestors shrink when e is removed on top of rest */
    def affected(e: Edge, rest: Set[Edge]): Set[String] =
      graph.without(rest - e).changed(graph.without(rest + e), theories)

    /* it did not finish, though the theories it imports did */
    private def failed(t: String, round: Round): Boolean = {
      val session = scope.sessions.find(scope.theories(_).contains(t)).get
      val imports = graph.without(round.removed).imports_of(t).filter(checked)
      !round.finished(t) && !round.cancelled(session) && imports.forall(round.finished)
    }

    def run(proposed: Set[Edge]): Result = {
      val first = copy.build(proposed)
      if (first.ok) Result(proposed, first, Nil, Nil, copy.builds)
      else {
        val suspects = proposed.filter(e => affected(e, proposed).exists(t => !first.finished(t))).toList.sorted
        loop(proposed -- suspects, suspects, Nil, List(baseline), max_builds)
      }
    }

    /* edges that no theory sees together */
    private def group(accepted: Set[Edge], pending: List[Edge]): List[Edge] =
      pending.foldLeft((List.empty[Edge], Set.empty[String])) { case ((g, seen), e) =>
        val aff = affected(e, accepted + e)
        if (g.isEmpty || !aff.exists(seen)) (g :+ e, seen ++ aff) else (g, seen)
      }._1

    /* Some(None): keep it; Some(Some(t)): t failed because of it alone; None: no verdict */
    private def verdict(e: Edge, round: Round, tried: List[Edge]): Option[Option[String]] = {
      val aff = affected(e, round.removed)
      val alone = aff.filter(t => failed(t, round) && tried.forall(g => g == e || !affected(g, round.removed)(t)))
      if (aff.forall(round.finished)) Some(None)
      else alone.headOption.map(Some(_))
    }

    @scala.annotation.tailrec
    private def loop(accepted: Set[Edge], pending: List[Edge], rejected: List[(Edge, String)],
        ok: List[Round], left: Int): Result =
      if (pending.isEmpty || left <= 0) finish(accepted, pending, rejected, ok)
      else {
        val tried = group(accepted, pending)
        val round = copy.build(accepted ++ tried)
        val verdicts = tried.flatMap(e => verdict(e, round, tried).map(e -> _))
        val kept = verdicts.collect({ case (e, None) => e })
        val failing = verdicts.collect({ case (e, Some(t)) => (e, t + " failed") })
        val ok1 = if (round.ok) round :: ok else ok
        if (verdicts.isEmpty) finish(accepted, pending, rejected, ok1)
        else {
          val decided = verdicts.map(_._1).toSet
          loop(accepted ++ kept, pending.filterNot(decided), rejected ::: failing, ok1, left - 1)
        }
      }

    /* what is reported must have been built as it is */
    private def finish(accepted: Set[Edge], untried: List[Edge], rejected: List[(Edge, String)],
        ok: List[Round]): Result =
      ok.find(_.removed == accepted) match {
        case Some(round) => Result(accepted, round, rejected, untried, copy.builds)
        case None =>
          val round = copy.build(accepted)
          val best = if (round.ok) round else ok.maxBy(_.removed.size)
          Result(best.removed, best, rejected, untried, copy.builds)
      }
  }


  /* report */

  private def plural(n: Int, what: String, whats: String = ""): String =
    n.toString + " " + (if (n == 1) what else proper_string(whats).getOrElse(what + "s"))

  private def seconds(x: Double): String = String.format("%.2f s", x)

  private def quoted(thy: String): String = "`" + Long_Name.base_name(thy) + "`"

  /* the facts, simp rules, constants, types and classes that the lost theories gave a theory */
  private def counts(uses: Option[Uses], lost: Set[String]): List[Int] = {
    val rows = uses.toList.flatMap(u => lost.toList.flatMap(u.context.get))
    (0 until 5).toList.map(i => rows.map(_(i)).sum)
  }

  private def describe_counts(cs: List[Int]): String =
    List("fact", "simp rule", "constant", "type", "class").zip(cs)
      .map({ case (w, n) => plural(n, w, if (w == "class") "classes" else "") }).mkString(", ")

  sealed case class Found(path: Path, line: Int, message: String)

  /* one finding per theory with removed imports, at the first of them */
  private def finding(scope: Scope, result: Result, baseline: Round, uses: Map[String, Uses], thy: String): Found = {
    val graph = scope.graph
    val after = graph.without(result.removed)
    val removed = graph.imports_of(thy).zipWithIndex.filter(x => result.removed((thy, x._1)))
    val (redundant, unused) = removed.map(_._1).partition(after.ancestors(thy))
    val lost = graph.ancestors(thy) -- after.ancestors(thy)

    def via(a: String): String =
      after.imports_of(thy).find(after.ancestors(_)(a)).map(b => " (via " + quoted(b) + ")").getOrElse("")
    def time(r: Round): String = r.timings.get(thy).map(seconds).getOrElse("?")

    val lines =
      (if (redundant.isEmpty) Nil else List("imported anyway: " + redundant.map(a => quoted(a) + via(a)).mkString(", "))) :::
      (if (unused.isEmpty) Nil
       else List("not needed: " + unused.map(quoted).mkString(", "),
         "the context loses " + plural(lost.size, "theory", "theories") + ": " + describe_counts(counts(uses.get(thy), lost)),
         "its commands take " + time(baseline) + " before, " + time(result.round) + " after (one build each)"))

    val text = File.read(scope.path(thy))
    val first = Patch.import_ranges(text)(removed.head._2)
    Found(scope.path(thy), Line.Document(text).position(first.start).line1, "[" + name + "] " + lines.mkString("\n  "))
  }

  private def headline(scope: Scope, proposed: Set[Edge], considered: Int, result: Result): String = {
    val after = scope.graph.without(result.removed)
    val redundant = result.removed.count(e => after.ancestors(e._1)(e._2))
    name + ": " + scope.session + ": " + plural(considered, "import") + " in scope, " +
      plural(proposed.size, "proposed removal") + ", " + result.removed.size + " removed (" + redundant +
      " imported anyway, " + (result.removed.size - redundant) + " not needed) after " +
      plural(result.builds, "build") + " of the copy"
  }

  private def kept(result: Result): List[String] = {
    def edge(e: Edge): String = quoted(e._2) + " in " + Long_Name.base_name(e._1)
    result.rejected.map({ case (e, why) => "  kept " + edge(e) + ": " + why + " without it" }) :::
    result.untried.map(e => "  kept " + edge(e) + ": not tried, out of builds (unused_imports_builds)")
  }

  private def built(scope: Scope, after: Theory_Graph): List[String] = {
    val added = dropped(scope, after)
    val elsewhere =
      if (scope.elsewhere.isEmpty) "no other session builds on " + scope.session
      else plural(scope.elsewhere.length, "session") + " elsewhere that build on it: " +
        commas(scope.elsewhere.take(8)) + (if (scope.elsewhere.length > 8) ", ..." else "")
    (if (added.isEmpty) Nil
     else List("  the ROOT's theories of " + scope.session + " get " + commas(added.map(Long_Name.base_name)) +
       ", which only these imports kept in the session")) :::
    List("  built: " + commas(scope.sessions) + "; not built: " + elsewhere)
  }

  /* other sessions that a theory of these sessions imports, directly or not */
  private def needed_sessions(scope: Scope, graph: Theory_Graph): Set[String] =
    scope.checked.flatMap(t => graph.ancestors(t)).map(scope.structure.theory_qualifier).toSet -- scope.sessions

  /* build times, the critical path, and what the contexts lose */
  private def effect(scope: Scope, result: Result, baseline: Round, uses: Map[String, Uses]): List[String] = {
    val graph = scope.graph
    val after = graph.without(result.removed)

    def total(r: Round): (Double, Double) = r.built.values.foldLeft((0.0, 0.0))((x, b) => (x._1 + b.elapsed, x._2 + b.cpu))
    def path(g: Theory_Graph, weight: String => Double): Double = g.critical_path(scope.checked.toSet, weight)._1
    def time(r: Round)(t: String): Double = r.timings.getOrElse(t, 0.0)

    val ((e0, c0), (e1, c1)) = (total(baseline), total(result.round))
    val shrunk = scope.own.map(t => t -> (graph.ancestors(t) -- after.ancestors(t))).filter(_._2.nonEmpty)
    val lost = shrunk.map({ case (t, ts) => counts(uses.get(t), ts) }).transpose.map(_.sum)
    val unneeded = needed_sessions(scope, graph) -- needed_sessions(scope, after)

    List(
      "  sessions: " + seconds(e0) + " -> " + seconds(e1) + " elapsed, " + seconds(c0) + " -> " + seconds(c1) + " CPU",
      "  critical path: " + path(graph, _ => 1).toInt + " -> " + path(after, _ => 1).toInt + " theories, " +
        seconds(path(graph, time(baseline))) + " -> " + seconds(path(after, time(result.round))) + " (command times)",
      "  contexts: " + plural(shrunk.length, "theory", "theories") + " of " + scope.session + " lose " +
        plural(shrunk.map(_._2.size).sum, "theory", "theories") + " in all" +
        (if (lost.isEmpty) "" else ": " + describe_counts(lost))) :::
    (if (unneeded.isEmpty) Nil else List("  no theory needs these sessions any more: " + commas(unneeded.toList.sorted)))
  }


  /* the lint */

  def run(options: Options, session: String, dirs: List[Path], progress: Progress, fix: Boolean): Unit = {
    val distribution = options.bool("unused_imports_distribution")
    val sc = scope(options, session, dirs, progress)
    val graph = sc.graph
    val uses = ask_uses(options, sc, dirs, progress)
    val considered = sc.own.map(t => graph.imports_of(t).count(sc.in_scope(_, distribution))).sum
    val proposed = propose(sc, uses, graph, distribution)
    progress.echo(name + ": " + plural(proposed.size, "removal") + " proposed of " + plural(considered, "import") + " in scope")

    if (proposed.isEmpty) progress.echo("\n0 findings")
    else {
      val outside = sc.structure.build_requirements(sc.sessions).filterNot(sc.sessions.contains)
      Patch.check_built(options, dirs, outside)
      val keep = proper_string(options.string("unused_imports_dir")).map(Path.explode)
      def body(dir: Path): Unit = {
        val copy = new Copy(options, dirs, sc, dir + sc.dir.base, progress)
        try {
          val baseline = copy.build(Set.empty)
          if (!baseline.ok) error("The copy of " + session + " does not build as it is")
          val result = new Search(copy, sc, baseline, options.int("unused_imports_builds")).run(proposed)
          report(sc, proposed, considered, result, baseline, uses, progress)
          if (fix) apply_fix(sc, result, progress)
        }
        finally { Patch.clean(options, copy.sessions) }
      }
      keep match {
        case Some(dir) => body(dir)
        case None => Isabelle_System.with_tmp_dir(name)(body)
      }
    }
  }

  private def report(scope: Scope, proposed: Set[Edge], considered: Int, result: Result, baseline: Round,
      uses: Map[String, Uses], progress: Progress): Unit = {
    val theories = scope.own.filter(t => result.removed.exists(_._1 == t))
    for (f <- theories.map(finding(scope, result, baseline, uses, _)).sortBy(f => (f.path.implode, f.line))) {
      progress.echo("\n" + f.path.implode + ":" + f.line + ": " + f.message)
    }
    val after = scope.graph.without(result.removed)
    val summary =
      headline(scope, proposed, considered, result) :: kept(result) ::: built(scope, after) :::
        effect(scope, result, baseline, uses)
    progress.echo("\n" + summary.mkString("\n"))
    progress.echo("\n" + theories.length + " findings")
  }

  private def apply_fix(scope: Scope, result: Result, progress: Progress): Unit = {
    val graph = scope.graph
    for (t <- scope.own) {
      val is = indices(graph, t, result.removed)
      if (is.nonEmpty) {
        val path = scope.path(t)
        File.write(path, Patch.remove_imports(File.read(path), is))
        progress.echo("Removed " + plural(is.size, "import") + " in " + path.implode)
      }
    }
    val added = dropped(scope, graph.without(result.removed)).map(scope.root_entry)
    if (added.nonEmpty) {
      val root = scope.dir + Sessions.ROOT
      File.write(root, Patch.add_theories(File.read(root), scope.session, added))
      progress.echo("Added " + plural(added.length, "theory", "theories") + " to " + root.implode)
    }
  }
}
