/* unused_imports: a copy of a session's directory with its sessions renamed, edited and built */

package isabelle.isabelle_linter

import isabelle._

import java.util.regex.{Matcher, Pattern}


object Patch {
  /* like scripts/lint_afp.py, but with its own suffix, so that the two never share a heap */
  val suffix = "_Imports"

  def patched(session: String): String = session + suffix

  def original_theory(theory: String): String = {
    val q = Long_Name.qualifier(theory)
    if (q.endsWith(suffix)) Long_Name.qualify(q.stripSuffix(suffix), Long_Name.base_name(theory)) else theory
  }


  /* copy */

  private val Session = """(?m)^\s*session\s+"?([\w+.-]+)"?""".r

  def session_names(root: String): List[String] = Session.findAllMatchIn(root).map(_.group(1)).toList

  /* names of the directory's theories qualified by one of the sessions; others, like a locale's
    LocalLexing.items_le_def in session LocalLexing, are left alone */
  def qualify(text: String, names: List[String], theories: Set[String]): String =
    names.foldLeft(text) { (t, name) =>
      ("(?<![\\w.])" + Pattern.quote(name) + "\\.(\\w+)").r.replaceAllIn(t, m =>
        Matcher.quoteReplacement(if (theories(m.group(1))) patched(name) + "." + m.group(1) else m.matched))
    }

  private val root_keywords =
    Set("chapter", "session", "sessions", "theories", "options", "description", "directories",
      "document_files", "document_theories", "export_files", "export_classpath", "global_theories")

  private def whole(name: String): String = "(?<![\\w+.-])\"?" + Pattern.quote(name) + "\"?(?![\\w+.-])"

  private def rename_line(line: String, section: String, name: String): String = {
    val renamed = Matcher.quoteReplacement("\"" + patched(name) + "\"")
    section match {
      case "session" =>
        line.replaceAll("(session\\s+)" + whole(name), "$1" + renamed)
          .replaceAll("(=\\s*)" + whole(name) + "(\\s*\\+)", "$1" + renamed + "$2")
      case "sessions" => line.replaceAll(whole(name), renamed)
      case _ => line
    }
  }

  private def root_keyword(line: String): Option[String] =
    """^\s*([a-z_]+)\b""".r.findFirstMatchIn(line).map(_.group(1)).filter(root_keywords)

  /* session names, parents, `sessions` lists and qualified theory names; no PDF document */
  def rename_root(root: String, names: List[String], theories: Set[String]): String = {
    var section = ""
    val lines =
      for (line <- root.linesWithSeparators.toList) yield {
        root_keyword(line).foreach(section = _)
        names.foldLeft(line)(rename_line(_, section, _))
      }
    qualify(lines.mkString.replaceAll("\\bdocument\\s*=\\s*\"?pdf\"?", "document = false"), names, theories)
  }

  /* the ROOT with theories (quoted) added after the last `theories` section of session */
  def add_theories(root: String, session: String, theories: List[String]): String =
    if (theories.isEmpty) root
    else {
      val lines = root.linesWithSeparators.toList
      var current = ""
      var section = ""
      var last = -1
      for ((line, i) <- lines.zipWithIndex) {
        session_names(line).foreach(current = _)
        root_keyword(line).foreach(section = _)
        if (current == session && section == "theories" && line.trim.nonEmpty) last = i
      }
      if (last < 0) error("No theories for session " + quote(session) + " in ROOT")
      val (before, after) = lines.splitAt(last + 1)
      val end = if (before.last.endsWith("\n")) "" else "\n"
      (before ::: List(end) ::: theories.map(t => "    " + quote(t) + "\n") ::: after).mkString
    }

  /* the copy's session names */
  def copy(dir: Path, target: Path): List[String] = {
    Isabelle_System.rm_tree(target)
    Isabelle_System.copy_dir(dir, target)
    val root_path = target + Sessions.ROOT
    val root = File.read(root_path)
    val names = session_names(root)
    val files = File.find_files(target.file, _.getName.endsWith(".thy")).map(File.path)
    val theories = files.map(_.base.implode.stripSuffix(".thy")).toSet
    File.write(root_path, rename_root(root, names, theories))
    for (path <- files) File.write(path, qualify(File.read(path), names, theories))
    names
  }


  /* header edits */

  private def tokens(text: String): List[(Token, Text.Range)] = {
    val toks = Token.explode(Thy_Header.bootstrap_keywords, text)
    toks.zip(toks.scanLeft(0)(_ + _.source.length)).map({ case (t, o) => (t, Text.Range(o, o + t.source.length)) })
  }

  private def header(text: String): List[(Token, Text.Range)] =
    tokens(text).takeWhile(!_._1.is_keyword(Thy_Header.BEGIN))

  /* the ranges of the header's imports, in order */
  def import_ranges(text: String): List[Text.Range] =
    header(text).dropWhile(!_._1.is_keyword(Thy_Header.IMPORTS)).drop(1)
      .takeWhile(t => !t._1.is_keyword(Thy_Header.KEYWORDS) && !t._1.is_keyword(Thy_Header.ABBREVS))
      .filter(_._1.is_proper).map(_._2)

  /* the text without the imports at these indices, each with the white space before it */
  def remove_imports(text: String, indices: Set[Int]): String = {
    val toks = header(text)
    val ranges = import_ranges(text)
    def start(r: Text.Range): Int =
      toks.filter(t => !t._1.is_space && t._2.stop <= r.start).lastOption.map(_._2.stop).getOrElse(r.start)
    indices.toList.sorted.reverse.foldLeft(text) { (t, i) =>
      val r = ranges(i)
      t.substring(0, start(r)) + t.substring(r.stop)
    }
  }


  /* build */

  /* a session of the copy after a build: ok, cancelled (never ran), what each theory that finished
    exports, the seconds its commands took by file, and the errors of the build log */
  sealed case class Built(ok: Boolean, cancelled: Boolean, content: Map[String, Set[String]],
    times: Map[String, Double], elapsed: Double, cpu: Double, errors: List[String])

  /* only the copy's sessions get these options: the export is session content, so other sessions
    would be out of date with it and built again; the timings of nearly every command */
  def build(options: Options, dirs: List[Path], sessions: List[String], progress: Progress): Map[String, Built] = {
    val extra = List("document=false", "export_theory", "build_timing_threshold=0.001").map(Options.Spec.make)
    val results =
      Build.build(options, selection = Sessions.Selection(sessions = sessions), dirs = dirs, progress = progress,
        augment_options = s => if (sessions.contains(s)) extra else Nil)
    def cancelled = Built(false, true, Map.empty, Map.empty, 0, 0, Nil)
    sessions.map(s => s -> (if (results.cancelled(s)) cancelled else read(results, s))).toMap
  }

  private def read(results: Build.Results, session: String): Built = {
    val store = results.store
    using(store.open_database(session)) { db =>
      val commands = Properties.uncompress(store.read_command_timings(db, session))
      val times =
        commands.groupMapReduce(props => Path.explode(Position.File.get(props)).canonical.implode)(
          Markup.Elapsed.get)(_ + _)
      val timing = store.read_session_timing(db, session)
      Built(results(session).ok, false, content(store, session), times, Markup.Elapsed.get(timing),
        Markup.CPU.get(timing), store.read_errors(db, session))
    }
  }

  /* what each theory declares and proves, from its exports: a digest per type, constant, axiom,
    theorem statement, class relation and type instance; not positions or printed names */
  def content(store: Store, session: String): Map[String, Set[String]] =
    using(Export.open_session_context0(store, session)) { context =>
      (for (thy <- Export_Theory.theory_names(context)) yield {
        val t = Export_Theory.read_theory(context.theory(thy), permissive = true)
        def entities[A <: Export_Theory.Content[A]](kind: String, es: List[Export_Theory.Entity[A]],
            f: A => Any): List[String] = es.map(e => kind + " " + e.name + " " + e.content.map(f))
        val lines =
          entities("type", t.types, identity) ::: entities("const", t.consts, identity) :::
          entities("axiom", t.axioms, _.prop) ::: entities("thm", t.thms, _.prop) :::
          t.classrel.map(_.toString) ::: t.arities.map(_.toString)
        thy -> lines.map(SHA1.digest(_).toString).toSet
      }).toMap
    }

  /* the sessions the copy needs from elsewhere must be built already, as a build would rebuild them */
  def check_built(options: Options, dirs: List[Path], sessions: List[String]): Unit =
    if (sessions.nonEmpty) {
      val results =
        Build.build(options, selection = Sessions.Selection(sessions = sessions), dirs = dirs, build_heap = true,
          no_build = true)
      if (!results.ok) error("Build these first, the copy needs them: " + commas(sessions))
    }

  def clean(options: Options, sessions: List[String]): Unit = {
    val store = Store(options)
    for (s <- sessions) store.clean_output(None, s)
  }
}
