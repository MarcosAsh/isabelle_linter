/* The unused_imports lint: theory imports that can go, proposed from what the prover says each
   theory uses, and checked by building an edited copy of the session. */

package isabelle.isabelle_linter

import isabelle._


object Unused_Imports {
  val name = "unused_imports"

  /* A theory and one of its imports, by long name. */
  type Edge = (String, String)


  /* The prover's view of a theory: the theories it uses, and how many facts, simp rules,
     constants, types and classes each theory in its context gives it. */
  sealed case class Uses(uses: Set[String], context: Map[String, List[Int]])

  private val entity_kinds =
    Set(Markup.CONSTANT, Markup.TYPE_NAME, Markup.CLASS, Markup.FACT, Markup.LOCALE, Markup.BUNDLE,
      Markup.METHOD, Markup.ATTRIBUTE)

  /* The entities the text refers to, as "kind name". */
  def refs(snapshot: Document.Snapshot): List[String] =
    snapshot.select(Text.Range(0, snapshot.node.source.length), Markup.Elements(Markup.ENTITY), _ =>
      {
        case Text.Info(_, XML.Elem(markup @ Markup.Entity(entry), _))
        if entity_kinds(entry.kind) && Markup.Entity.Ref.unapply(markup).isDefined => Some(entry.kind + " " + entry.name)
        case _ => None
      }).map(_.info).distinct

  /* The commands and minor keywords of the text. */
  def keywords_used(snapshot: Document.Snapshot): Set[String] =
    Cmd.read(snapshot.node).flatMap(_.tokens.filter(t => t.token.is_command || t.token.is_keyword).map(_.source)).toSet

  /* Asked on the command before `end`, which sees the whole theory. */
  def question(snapshot: Document.Snapshot, timeout: Time): Option[Pide.Question] =
    Cmd.read(snapshot.node).reverse match {
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

  /* The theories that declare each keyword in their header. */
  def keyword_theories(scope: Scope): Map[String, Set[String]] =
    (for {
      (thy, entry) <- scope.known.toList
      (keyword, _) <- entry.keywords
    } yield keyword -> thy).groupMap(_._1)(_._2).map({ case (keyword, theories) => keyword -> theories.toSet })

  /* A theory also uses the theories that declare its keywords. */
  def ask_uses(options: Options, scope: Scope, dirs: List[Path], progress: Progress): Map[String, Uses] = {
    val declared = keyword_theories(scope)
    Pide.check(options, scope.session, dirs, progress) { checked =>
      /* The question covers a whole theory's facts and derivations, not one lemma. */
      val timeout = Time.seconds(10 * options.real("linter_timeout"))
      val asked = checked.snapshots.flatMap(snapshot => question(snapshot, timeout).map(snapshot -> _))
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


  /* The session, and the sessions of its ROOT file that build on it. */

  sealed case class Scope(
    session: String,
    structure: Sessions.Structure,
    dir: Path,
    sessions: List[String],
    elsewhere: List[String],
    theories: Map[String, List[String]],
    known: Map[String, Resources.Thy]
  ) {
    def own: List[String] = theories(session)
    def info: Sessions.Info = structure(session)

    /* The theories the ROOT names for the session. */
    def listed: Set[String] =
      info.theories.flatMap(_._2).map({ case (entry, _) => Thy_Header.import_name(entry) }).map(thy =>
        if (Long_Name.is_qualified(thy) || info.global_theories.contains(thy)) thy
        else Long_Name.qualify(session, thy)).toSet

    /* How the ROOT can name a theory of the session. */
    def root_entry(thy: String): String =
      File.get_relative_path(info.dir.canonical, path(thy).canonical).map(_.implode.stripSuffix(".thy"))
        .getOrElse(Long_Name.base_name(thy))
    def checked: List[String] = sessions.flatMap(theories)
    def graph: Theory_Graph = new Theory_Graph(known.map({ case (thy, entry) => thy -> entry.imports.map(_._1.theory) }))
    def path(thy: String): Path = known(thy).name.path

    /* The header's imports are as the text has them. */
    def editable(thy: String): Boolean =
      Patch.import_ranges(File.read(path(thy))).length == known(thy).imports.length

    /* The path of a theory in the copy. */
    def copy_path(copy: Path, thy: String): Path =
      copy + File.get_relative_path(dir.canonical, path(thy).canonical).getOrElse(error("Theory outside " + dir))

    /* An import outside the Isabelle distribution, or any with unused_imports_distribution. */
    def in_scope(thy: String, distribution: Boolean): Boolean = {
      val session = structure.theory_qualifier(thy)
      distribution || !structure.defined(session) ||
        File.get_relative_path(Path.explode("~~").canonical, structure(session).dir.canonical).isEmpty
    }
  }

  private def root_file(info: Sessions.Info): Path =
    Path.explode(Position.File.get(info.pos)).canonical

  def read_scope(options: Options, session: String, dirs: List[Path], progress: Progress): Scope = {
    val structure = Sessions.load_structure(options, dirs = dirs)
    val root = root_file(structure(session))
    val (same, elsewhere) =
      structure.imports_descendants(List(session)).filter(_ != session)
        .partition(other => root_file(structure(other)) == root)
    val sessions = session :: same
    val deps = Sessions.deps(structure.selection(Sessions.Selection(sessions = sessions)), progress = progress)
    val theories = sessions.map(name => name -> deps(name).proper_session_theories.map(_.theory)).toMap
    val known = sessions.flatMap(deps(_).known_theories).toMap
    Scope(session, structure, root.dir, sessions, elsewhere, theories, known)
  }


  /* proposals */

  /* Theories of the session that only imports kept in it; they go into the ROOT's theories. */
  def dropped(scope: Scope, edited: Theory_Graph): List[String] = {
    val listed = scope.listed
    scope.own.filterNot(thy => listed(thy) || listed.exists(edited.ancestors(_)(thy)))
  }

  /* Each theory of the session keeps an import, and the theories it uses. */
  def acceptable(scope: Scope, uses: Map[String, Uses], graph: Theory_Graph, edited: Theory_Graph): Boolean = {
    scope.own.forall { thy =>
      edited.imports_of(thy).nonEmpty || graph.imports_of(thy).isEmpty
    } && scope.own.forall { thy =>
      val needed = uses.get(thy).map(_.uses & graph.ancestors(thy)).getOrElse(graph.ancestors(thy))
      needed.subsetOf(edited.ancestors(thy))
    }
  }

  /* The imports that another import already brings in, then each other import that keeps the
     session acceptable. */
  def propose(scope: Scope, uses: Map[String, Uses], graph: Theory_Graph, distribution: Boolean): Set[Edge] = {
    def candidates(imports: String => List[String]): List[Edge] =
      for {
        thy <- scope.own if scope.editable(thy)
        imported <- imports(thy).distinct if scope.in_scope(imported, distribution)
      } yield (thy, imported)
    val redundant = candidates(graph.redundant).toSet
    candidates(graph.imports_of).filterNot(redundant).foldLeft(redundant) { (removed, edge) =>
      if (acceptable(scope, uses, graph, graph.without(removed + edge))) removed + edge else removed
    }
  }


  /* builds of the copy, each with its removals written into the copy's original text */

  def indices(graph: Theory_Graph, thy: String, removed: Set[Edge]): Set[Int] =
    graph.imports_of(thy).zipWithIndex.collect({ case (imported, i) if removed((thy, imported)) => i }).toSet

  /* A build of the copy. Timings are the seconds of each theory's commands; changed are theories
     that build but no longer export what they did before. */
  sealed case class Round(removed: Set[Edge], built: Map[String, Patch.Built], timings: Map[String, Double],
      changed: Set[String]) {
    def ok: Boolean = built.values.forall(_.ok) && changed.isEmpty
    def cancelled: Set[String] = built.collect({ case (session, result) if result.cancelled => session }).toSet
    def content: Map[String, Set[String]] =
      built.values.flatMap(_.content).map({ case (thy, digests) => Patch.original_theory(thy) -> digests }).toMap
    def finished: Set[String] = content.keySet -- changed
  }

  private class Copy(options: Options, dirs: List[Path], scope: Scope, dir: Path, progress: Progress) {
    Patch.copy(scope.dir, dir)
    val sessions: List[String] = scope.sessions.map(Patch.patched)
    private val root = File.read(dir + Sessions.ROOT)
    private val texts = scope.own.map(thy => thy -> File.read(scope.copy_path(dir, thy))).toMap
    private val files = scope.checked.map(thy => scope.copy_path(dir, thy).canonical.implode -> thy).toMap
    private val graph = scope.graph
    private var before: Map[String, Set[String]] = Map.empty
    var builds = 0

    private def write(removed: Set[Edge]): Unit = {
      for ((thy, text) <- texts) {
        File.write(scope.copy_path(dir, thy), Patch.remove_imports(text, indices(graph, thy, removed)))
      }
      val added = dropped(scope, graph.without(removed)).map(scope.root_entry)
      File.write(dir + Sessions.ROOT, Patch.add_theories(root, Patch.patched(scope.session), added))
    }

    /* The first build has no removals; what it exports is what later builds must export too. */
    def build(removed: Set[Edge]): Round = {
      write(removed)
      builds += 1
      progress.echo(name + ": build " + builds + ", " + removed.size + " imports removed")
      val built = Patch.build(options, dirs ::: List(dir), sessions, progress)
      val timings =
        built.values.flatMap(_.times).flatMap({ case (file, seconds) => files.get(file).map(_ -> seconds) }).toMap
      val by_session = built.map({ case (session, result) => session.stripSuffix(Patch.suffix) -> result })
      val unchecked = Round(removed, by_session, timings, Set.empty)
      if (builds == 1) before = unchecked.content
      val content = unchecked.content
      val round = unchecked.copy(changed = content.keySet.filter(thy => before.get(thy) != content.get(thy)))
      for ((session, result) <- round.built if !result.ok && !result.cancelled) {
        val error =
          result.errors.find(!_.startsWith("Failed to load theory")).orElse(result.errors.headOption).getOrElse("")
        progress.echo(name + ": " + session + " failed: " + error.linesIterator.take(2).mkString(" "))
      }
      if (round.changed.nonEmpty) progress.echo(name + ": changed exports: " + commas(round.changed.toList.sorted))
      round
    }
  }


  /* The search: build the copy with all proposed removals; on failure keep those that touch no
     failed theory and try the others again, several at a time when no theory sees two of them. */

  sealed case class Result(removed: Set[Edge], round: Round, rejected: List[(Edge, String)],
    untried: List[Edge], builds: Int)

  private class Search(copy: Copy, scope: Scope, baseline: Round, max_builds: Int) {
    private val graph = scope.graph
    private val theories = scope.checked
    private val checked = theories.toSet

    /* The theories whose ancestors shrink when edge is removed on top of rest. */
    def affected(edge: Edge, rest: Set[Edge]): Set[String] =
      graph.without(rest - edge).changed(graph.without(rest + edge), theories)

    /* The theory did not finish, though the theories it imports did. */
    private def failed(thy: String, round: Round): Boolean = {
      val session = scope.sessions.find(scope.theories(_).contains(thy)).get
      val imports = graph.without(round.removed).imports_of(thy).filter(checked)
      !round.finished(thy) && !round.cancelled(session) && imports.forall(round.finished)
    }

    def run(proposed: Set[Edge]): Result = {
      val first = copy.build(proposed)
      if (first.ok) Result(proposed, first, Nil, Nil, copy.builds)
      else {
        val suspects =
          proposed.filter(edge => affected(edge, proposed).exists(thy => !first.finished(thy))).toList.sorted
        loop(proposed -- suspects, suspects, Nil, List(baseline), max_builds)
      }
    }

    /* Edges that no theory sees together. */
    private def group(accepted: Set[Edge], pending: List[Edge]): List[Edge] =
      pending.foldLeft((List.empty[Edge], Set.empty[String])) { case ((chosen, seen), edge) =>
        val touched = affected(edge, accepted + edge)
        if (chosen.isEmpty || !touched.exists(seen)) (chosen :+ edge, seen ++ touched) else (chosen, seen)
      }._1

    /* A removal stays if every theory it affects finished. */
    private def keeps(edge: Edge, round: Round): Boolean = affected(edge, round.removed).forall(round.finished)

    /* An affected theory that failed because of this removal alone, of those tried together. */
    private def blamed(edge: Edge, round: Round, tried: List[Edge]): Option[String] =
      affected(edge, round.removed).find(thy =>
        failed(thy, round) && tried.forall(other => other == edge || !affected(other, round.removed)(thy)))

    /* Removals that neither stay nor fail alone are tried again; without any verdict the search ends. */
    @scala.annotation.tailrec
    private def loop(accepted: Set[Edge], pending: List[Edge], rejected: List[(Edge, String)],
        succeeded: List[Round], left: Int): Result =
      if (pending.isEmpty || left <= 0) finish(accepted, pending, rejected, succeeded)
      else {
        val tried = group(accepted, pending)
        val round = copy.build(accepted ++ tried)
        val kept = tried.filter(keeps(_, round))
        val failing =
          tried.filterNot(keeps(_, round)).flatMap(edge => blamed(edge, round, tried).map(thy => (edge, thy + " failed")))
        val now_succeeded = if (round.ok) round :: succeeded else succeeded
        val decided = kept.toSet ++ failing.map(_._1)
        if (decided.isEmpty) finish(accepted, pending, rejected, now_succeeded)
        else loop(accepted ++ kept, pending.filterNot(decided), rejected ::: failing, now_succeeded, left - 1)
      }

    /* What is reported must have been built as it is. */
    private def finish(accepted: Set[Edge], untried: List[Edge], rejected: List[(Edge, String)],
        succeeded: List[Round]): Result =
      succeeded.find(_.removed == accepted) match {
        case Some(round) => Result(accepted, round, rejected, untried, copy.builds)
        case None =>
          val round = copy.build(accepted)
          val best = if (round.ok) round else succeeded.maxBy(_.removed.size)
          Result(best.removed, best, rejected, untried, copy.builds)
      }
  }


  /* report */

  private def plural(n: Int, what: String, whats: String = ""): String =
    n.toString + " " + (if (n == 1) what else proper_string(whats).getOrElse(what + "s"))

  private def seconds(x: Double): String = Library.format("%.2f s", x)

  private def quoted(thy: String): String = "`" + Long_Name.base_name(thy) + "`"

  /* The facts, simp rules, constants, types and classes that the lost theories gave a theory. */
  private def counts(uses: Option[Uses], lost: Set[String]): List[Int] = {
    val rows = uses.toList.flatMap(theory_uses => lost.toList.flatMap(theory_uses.context.get))
    (0 until 5).toList.map(i => rows.map(_(i)).sum)
  }

  private def describe_counts(counts: List[Int]): String =
    List("fact", "simp rule", "constant", "type", "class").zip(counts)
      .map({ case (what, n) => plural(n, what, if (what == "class") "classes" else "") }).mkString(", ")

  sealed case class Found(path: Path, line: Int, message: String)

  /* One finding per theory with removed imports, at the first of them. */
  private def finding(scope: Scope, result: Result, baseline: Round, uses: Map[String, Uses], thy: String): Found = {
    val graph = scope.graph
    val after = graph.without(result.removed)
    val removed = graph.imports_of(thy).zipWithIndex.filter({ case (imported, _) => result.removed((thy, imported)) })
    val (redundant, unused) = removed.map(_._1).partition(after.ancestors(thy))
    val lost = graph.ancestors(thy) -- after.ancestors(thy)

    def via(imported: String): String =
      after.imports_of(thy).find(after.ancestors(_)(imported)).map(kept => " (via " + quoted(kept) + ")").getOrElse("")
    def time(round: Round): String = round.timings.get(thy).map(seconds).getOrElse("?")

    val lines =
      (if (redundant.isEmpty) Nil
       else List("imported anyway: " + redundant.map(imported => quoted(imported) + via(imported)).mkString(", "))) :::
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
    val redundant = result.removed.count({ case (thy, imported) => after.ancestors(thy)(imported) })
    name + ": " + scope.session + ": " + plural(considered, "import") + " in scope, " +
      plural(proposed.size, "proposed removal") + ", " + result.removed.size + " removed (" + redundant +
      " imported anyway, " + (result.removed.size - redundant) + " not needed) after " +
      plural(result.builds, "build") + " of the copy"
  }

  private def kept(result: Result): List[String] = {
    def edge(thy: String, imported: String): String = quoted(imported) + " in " + Long_Name.base_name(thy)
    result.rejected.map({ case ((thy, imported), why) => "  kept " + edge(thy, imported) + ": " + why + " without it" }) :::
    result.untried.map({ case (thy, imported) =>
      "  kept " + edge(thy, imported) + ": not tried, out of builds (unused_imports_builds)" })
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

  /* Other sessions that a theory of these sessions imports, directly or not. */
  private def needed_sessions(scope: Scope, graph: Theory_Graph): Set[String] =
    scope.checked.flatMap(graph.ancestors).map(scope.structure.theory_qualifier).toSet -- scope.sessions

  /* Build times, the critical path, and what the contexts lose. */
  private def effect(scope: Scope, result: Result, baseline: Round, uses: Map[String, Uses]): List[String] = {
    val graph = scope.graph
    val after = graph.without(result.removed)

    def total(round: Round): (Double, Double) =
      round.built.values.foldLeft((0.0, 0.0)) { case ((elapsed, cpu), built) => (elapsed + built.elapsed, cpu + built.cpu) }
    def path(imports: Theory_Graph, weight: String => Double): Double =
      imports.critical_path(scope.checked.toSet, weight)._1
    def time(round: Round)(thy: String): Double = round.timings.getOrElse(thy, 0.0)

    val (elapsed_before, cpu_before) = total(baseline)
    val (elapsed_after, cpu_after) = total(result.round)
    val shrunk = scope.own.map(thy => thy -> (graph.ancestors(thy) -- after.ancestors(thy))).filter(_._2.nonEmpty)
    val lost = shrunk.map({ case (thy, gone) => counts(uses.get(thy), gone) }).transpose.map(_.sum)
    val unneeded = needed_sessions(scope, graph) -- needed_sessions(scope, after)

    List(
      "  sessions: " + seconds(elapsed_before) + " -> " + seconds(elapsed_after) + " elapsed, " +
        seconds(cpu_before) + " -> " + seconds(cpu_after) + " CPU",
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
    val scope = read_scope(options, session, dirs, progress)
    val graph = scope.graph
    val uses = ask_uses(options, scope, dirs, progress)
    val considered = scope.own.map(thy => graph.imports_of(thy).count(scope.in_scope(_, distribution))).sum
    val proposed = propose(scope, uses, graph, distribution)
    progress.echo(name + ": " + plural(proposed.size, "removal") + " proposed of " + plural(considered, "import") + " in scope")

    if (proposed.isEmpty) progress.echo("\n0 findings")
    else {
      val outside = scope.structure.build_requirements(scope.sessions).filterNot(scope.sessions.contains)
      Patch.check_built(options, dirs, outside)
      val keep = proper_string(options.string("unused_imports_dir")).map(Path.explode)
      def body(dir: Path): Unit = {
        val copy = new Copy(options, dirs, scope, dir + scope.dir.base, progress)
        try {
          val baseline = copy.build(Set.empty)
          if (!baseline.ok) error("The copy of " + session + " does not build as it is")
          val result = new Search(copy, scope, baseline, options.int("unused_imports_builds")).run(proposed)
          report(scope, proposed, considered, result, baseline, uses, progress)
          if (fix) apply_fix(scope, result, progress)
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
    val theories = scope.own.filter(thy => result.removed.exists(_._1 == thy))
    for (found <- theories.map(finding(scope, result, baseline, uses, _)).sortBy(found => (found.path.implode, found.line))) {
      progress.echo("\n" + found.path.implode + ":" + found.line + ": " + found.message)
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
    for (thy <- scope.own) {
      val removed = indices(graph, thy, result.removed)
      if (removed.nonEmpty) {
        val path = scope.path(thy)
        File.write(path, Patch.remove_imports(File.read(path), removed))
        progress.echo("Removed " + plural(removed.size, "import") + " in " + path.implode)
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
