/* The linter_parent tool: for each session, the parent whose heap would hold the most of the
   theories it checks again, by their times in the build logs. */

package isabelle.isabelle_linter

import isabelle._

import java.io.{File => JFile}


object Parent {
  /* A theory that is not in a parent heap is checked again by every session that imports it. */
  sealed case class Suggestion(
    session: String,
    parent: String,
    stored: Double,
    foreign: Double,
    saved: Double,
    redundant: List[String],
    new_heap: Boolean)


  /* The stored command time of one session, summed per theory file. */
  def read_log(store: Store, log_dir: Option[Path], session: String): Option[Map[String, Double]] = {
    val db =
      log_dir match {
        case Some(dir) =>
          val path = dir + Path.basic(session).db
          if (path.is_file) Some(SQLite.open_database(path)) else None
        case None => store.try_open_database(session)
      }
    db.map(opened =>
      using(opened) { db =>
        val timings = Properties.uncompress(store.read_command_timings(db, session))
        timings.groupMapReduce(props => Properties.get(props, Markup.FILE).getOrElse(""))(
          Markup.Timing_Properties.Elapsed.get)(_ + _)
      })
  }


  /* The session whose directory holds a theory file. */
  final class Homes(structure: Sessions.Structure) {
    private val cache = Synchronized(Map.empty[String, Option[String]])

    private def lookup(dir: JFile | Null): Option[String] =
      dir match {
        case null => None
        case d: JFile => structure.session_directories.get(d).orElse(lookup(d.getParentFile))
      }

    def apply(file: String): Option[String] =
      cache.change_result { homes =>
        val home = homes.getOrElse(file, lookup(Path.explode(file).expand.dir.canonical_file))
        (home, homes + (file -> home))
      }
  }


  /* The build log and the heap content of each session, read once. */
  final class Logs(structure: Sessions.Structure, store: Store, log_dir: Option[Path]) {
    private val logs = Synchronized(Map.empty[String, Option[Map[String, Double]]])
    private val heaps = Synchronized(Map.empty[String, Set[String]])

    def apply(session: String): Option[Map[String, Double]] =
      logs.change_result { cache =>
        val log = cache.getOrElse(session, read_log(store, log_dir, session))
        (log, cache + (session -> log))
      }

    /* The theory files in a session's heap: what it and its ancestors checked. */
    def heap(session: String): Set[String] =
      heaps.value.getOrElse(session, {
        val files = structure.build_requirements(List(session)).flatMap(apply(_).getOrElse(Map.empty).keys).toSet
        heaps.change(_ + (session -> files))
        files
      })
  }


  def is_distribution(info: Sessions.Info): Boolean =
    info.dir.canonical_file.toPath.nn.startsWith(Path.explode("~~").canonical_file.toPath)

  /* Parents that keep every current ancestor and do not import the session: sessions it imports
     already, or distribution sessions. */
  def candidates(structure: Sessions.Structure, distribution: List[String], session: String): List[String] = {
    val ancestors = structure.build_requirements(List(session)).filterNot(_ == session).toSet
    val imported = structure.imports_requirements(List(session)).filterNot(_ == session)
    (imported ::: distribution).distinct.filter { parent =>
      !ancestors(parent) &&
      ancestors.subsetOf(structure.build_requirements(List(parent)).toSet) &&
      !structure.imports_graph.all_preds(List(parent)).contains(session)
    }
  }

  def suggest(
    structure: Sessions.Structure,
    distribution: List[String],
    logs: Logs,
    homes: Homes,
    session: String
  ): Option[Suggestion] =
    for (log <- logs(session)) yield {
      val foreign = log.filter({ case (file, _) => !homes(file).contains(session) })
      val savings =
        for (candidate <- candidates(structure, distribution, session) if logs(candidate).isDefined) yield {
          val heap = logs.heap(candidate)
          candidate -> foreign.iterator.collect({ case (file, seconds) if heap(file) => seconds }).sum
        }
      /* On a tie, the smaller heap wins. */
      val size = (candidate: String) => structure.build_requirements(List(candidate)).length
      val (parent, saved) =
        savings.filter(_._2 > 0).maxByOption({ case (candidate, seconds) => (seconds, -size(candidate)) })
          .getOrElse(("", 0.0))
      val chain = if (parent.isEmpty) Set.empty[String] else structure.build_requirements(List(parent)).toSet
      Suggestion(session, parent, log.values.sum, foreign.values.sum, saved,
        structure(session).imports.filter(chain),
        parent.nonEmpty && structure.build_graph.imm_succs(parent).isEmpty)
    }


  /* the ROOT edit: the session header with the parent replaced */

  def root_edit(info: Sessions.Info, parent: String): String =
    (Position.File.unapply(info.pos), Position.Line.unapply(info.pos)) match {
      case (Some(file), Some(line)) =>
        val text = split_lines(File.read(Path.explode(file))).drop(line - 1).mkString("\n")
        val header = text.take(text.indexOf('+', text.indexOf('=')) + 1)
        val old = "=\\s*\"?" + java.util.regex.Pattern.quote(info.parent.getOrElse("")) + "\"?\\s*\\+"
        val edited = header.replaceFirst(old, java.util.regex.Matcher.quoteReplacement("= " + quote_name(parent) + " +"))
        file + ":" + line + ": " + edited.nn.replaceAll("\\s+", " ")
      case _ => "session " + info.name + " = " + quote_name(parent) + " +"
    }

  def quote_name(name: String): String =
    if (name.forall(c => c.isLetterOrDigit || c == '_' || c == '\'')) name else quote(name)


  def report(structure: Sessions.Structure, suggestions: List[Suggestion], min: Double, progress: Progress): Unit = {
    def secs(seconds: Double): String = Library.format(if (seconds < 10) "%.1f s" else "%.0f s", seconds)
    for (suggestion <- suggestions.sortBy(-_.saved) if suggestion.parent.nonEmpty && suggestion.saved >= min) {
      val info = structure(suggestion.session)
      progress.echo(suggestion.session + ": parent " + suggestion.parent + " instead of " +
        info.parent.getOrElse("-") + " saves " + secs(suggestion.saved) + " of " + secs(suggestion.foreign) +
        " re-checked (" + secs(suggestion.stored) + " stored)")
      progress.echo("  " + root_edit(info, suggestion.parent))
      if (suggestion.redundant.nonEmpty) {
        progress.echo("  now ancestors, may leave `sessions`: " + commas(suggestion.redundant))
      }
      if (suggestion.new_heap) progress.echo("  " + suggestion.parent + " will store a heap")
    }
    val stored = suggestions.map(_.stored).sum
    val foreign = suggestions.map(_.foreign).sum
    val saved = suggestions.map(_.saved).sum
    progress.echo("\n" + suggestions.length + " sessions, " + secs(stored) + " stored, " + secs(foreign) +
      " re-checked (" + Census.share(foreign, stored) + "), " + secs(saved) + " saved by a new parent (" +
      Census.share(saved, stored) + ")")
  }


  def write_tsv(path: Path, structure: Sessions.Structure, suggestions: List[Suggestion]): Unit = {
    val lines =
      for (suggestion <- suggestions)
      yield List(suggestion.session, structure(suggestion.session).parent.getOrElse(""), suggestion.parent,
        suggestion.stored, suggestion.foreign, suggestion.saved, suggestion.new_heap).mkString("\t")
    File.write(path, ("session\tparent\tnew_parent\tstored\tforeign\tsaved\tnew_heap" :: lines).mkString("", "\n", "\n"))
  }


  val parent_tool: Isabelle_Tool =
    Isabelle_Tool("linter_parent", "suggest parent sessions that save re-checked theories", Scala_Project.here,
      { args =>
        val dirs = new scala.collection.mutable.ListBuffer[Path]
        val select_dirs = new scala.collection.mutable.ListBuffer[Path]
        var log_dir: Option[Path] = None
        var output: Option[Path] = None
        var min = 1.0
        var options = Options.init()

        val getopts = Getopts("""
Usage: isabelle linter_parent [OPTIONS] [SESSIONS]

  Options are:
    -D DIR       include session directory and select its sessions
    -L DIR       read the log databases from DIR (default: the heap store)
    -O FILE      also write every session's suggestion to FILE (TSV)
    -d DIR       include session directory
    -m SECONDS   show suggestions that save at least this much (default: 1)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  For SESSIONS and the sessions of each -D DIR (default: every session with
  a log database), read which theories isabelle build checked and how long
  each took, and suggest the parent that saves the most time on theories of
  other sessions: a theory outside the parent heaps is checked again in each
  session that imports it. The new parent keeps every current ancestor and
  does not import the session. Build with -o build_timing_threshold=0.01.
""",
          "D:" -> (arg => select_dirs += Path.explode(arg)),
          "L:" -> (arg => log_dir = Some(Path.explode(arg))),
          "O:" -> (arg => output = Some(Path.explode(arg))),
          "d:" -> (arg => dirs += Path.explode(arg)),
          "m:" -> (arg => min = Value.Double.parse(arg)),
          "o:" -> (arg => options = options + arg))

        val more_args = getopts(args)
        val store = Store(options)
        val structure = Sessions.load_structure(options, dirs = (dirs ++ select_dirs).toList)
        val logs = new Logs(structure, store, log_dir)
        val names =
          (more_args ::: Census.selected(options, dirs.toList, select_dirs.toList)) match {
            case Nil => structure.build_topological_order.filter(logs(_).isDefined)
            case sessions => structure.check_sessions(sessions); sessions.distinct
          }

        val homes = new Homes(structure)
        val distribution = structure.build_topological_order.filter(session => is_distribution(structure(session)))
        val suggestions = names.flatMap(suggest(structure, distribution, logs, homes, _))
        report(structure, suggestions, min, new Console_Progress())
        output.foreach(write_tsv(_, structure, suggestions))
      })
}
