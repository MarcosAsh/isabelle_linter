/* The copy that unused_imports builds: a session's directory with its sessions renamed, imports
   removed from theory headers, and what each build of it checked and exported. */

package isabelle.isabelle_linter

import isabelle._

import java.util.regex.{Matcher, Pattern}


object Patch {
  /* Like scripts/lint_afp.py, but with its own suffix, so that the two never share a heap. */
  val suffix = "_Imports"

  def patched(session: String): String = session + suffix

  def original_theory(theory: String): String = {
    val session = Long_Name.qualifier(theory)
    if (session.endsWith(suffix)) Long_Name.qualify(session.stripSuffix(suffix), Long_Name.base_name(theory))
    else theory
  }


  /* copy */

  private val Session = """(?m)^\s*session\s+"?([\w+.-]+)"?""".r

  def session_names(root: String): List[String] = Session.findAllMatchIn(root).map(_.group(1)).toList

  /* Rename the session in names of the directory's theories that it qualifies. Other names, like
     the locale fact LocalLexing.items_le_def in session LocalLexing, are left alone. */
  def qualify(text: String, names: List[String], theories: Set[String]): String =
    names.foldLeft(text) { (renamed, name) =>
      ("(?<![\\w.])" + Pattern.quote(name) + "\\.(\\w+)").r.replaceAllIn(renamed, found =>
        Matcher.quoteReplacement(
          if (theories(found.group(1))) patched(name) + "." + found.group(1) else found.matched).nn)
    }

  private val root_keywords =
    Set("chapter", "session", "sessions", "theories", "options", "description", "directories",
      "document_files", "document_theories", "export_files", "export_classpath", "global_theories")

  private def whole(name: String): String = "(?<![\\w+.-])\"?" + Pattern.quote(name) + "\"?(?![\\w+.-])"

  private def rename_line(line: String, section: String, name: String): String = {
    val renamed = Matcher.quoteReplacement("\"" + patched(name) + "\"")
    section match {
      case "session" =>
        line.replaceAll("(session\\s+)" + whole(name), "$1" + renamed).nn
          .replaceAll("(=\\s*)" + whole(name) + "(\\s*\\+)", "$1" + renamed + "$2").nn
      case "sessions" => line.replaceAll(whole(name), renamed).nn
      case _ => line
    }
  }

  private def root_keyword(line: String): Option[String] =
    """^\s*([a-z_]+)\b""".r.findFirstMatchIn(line).map(_.group(1)).filter(root_keywords)

  /* Rename the session names, parents, `sessions` lists and qualified theory names; build no PDF. */
  def rename_root(root: String, names: List[String], theories: Set[String]): String = {
    var section = ""
    val lines =
      for (line <- root.linesWithSeparators.toList) yield {
        root_keyword(line).foreach(section = _)
        names.foldLeft(line)(rename_line(_, section, _))
      }
    qualify(lines.mkString.replaceAll("\\bdocument\\s*=\\s*\"?pdf\"?", "document = false").nn, names, theories)
  }

  /* The ROOT with theories, quoted, added after the last `theories` section of session. */
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
        if (current == session && section == "theories" && line.trim.nn.nonEmpty) last = i
      }
      if (last < 0) error("No theories for session " + quote(session) + " in ROOT")
      val (before, after) = lines.splitAt(last + 1)
      val end = if (before.last.endsWith("\n")) "" else "\n"
      (before ::: List(end) ::: theories.map(t => "    " + quote(t) + "\n") ::: after).mkString
    }

  /* Copy dir to target and rename its sessions; returns their original names. */
  def copy(dir: Path, target: Path): List[String] = {
    Isabelle_System.rm_tree(target)
    Isabelle_System.copy_dir(dir, target)
    val root_path = target + Sessions.ROOT
    val root = File.read(root_path)
    val names = session_names(root)
    val files = File.find_files(target, _.file_name.endsWith(".thy"))
    val theories = files.map(_.base.implode.stripSuffix(".thy")).toSet
    File.write(root_path, rename_root(root, names, theories))
    for (path <- files) File.write(path, qualify(File.read(path), names, theories))
    names
  }


  /* header edits */

  private def tokens(text: String): List[(Token, Text.Range)] = {
    val toks = Token.explode(Thy_Header.bootstrap_keywords, text)
    val starts = toks.scanLeft(0)(_ + _.source.length)
    toks.zip(starts).map({ case (token, start) => (token, Text.Range(start, start + token.source.length)) })
  }

  private def header(text: String): List[(Token, Text.Range)] =
    tokens(text).takeWhile({ case (token, _) => !token.is_keyword(Thy_Header.BEGIN) })

  /* The ranges of the header's imports, in order. */
  def import_ranges(text: String): List[Text.Range] =
    header(text).dropWhile({ case (token, _) => !token.is_keyword(Thy_Header.IMPORTS) }).drop(1)
      .takeWhile({ case (token, _) => !token.is_keyword(Thy_Header.KEYWORDS) && !token.is_keyword(Thy_Header.ABBREVS) })
      .collect({ case (token, range) if token.is_proper => range })

  /* The text without the imports at these indices, each with the white space before it. */
  def remove_imports(text: String, indices: Set[Int]): String = {
    val toks = header(text)
    val ranges = import_ranges(text)
    def start(range: Text.Range): Int =
      toks.collect({ case (token, before) if !token.is_space && before.stop <= range.start => before.stop })
        .lastOption.getOrElse(range.start)
    indices.toList.sorted.reverse.foldLeft(text) { (edited, i) =>
      val range = ranges(i)
      edited.substring(0, start(range)).nn + edited.substring(range.stop)
    }
  }


  /* build */

  /* A session of the copy after a build: whether it was ok or cancelled before it ran, what each
     theory that finished exports, the seconds its commands took by file, and its errors. */
  sealed case class Built(ok: Boolean, cancelled: Boolean, content: Map[String, Set[String]],
    times: Map[String, Double], elapsed: Double, cpu: Double, errors: List[String])

  /* Only the copy's sessions export theories, which other sessions would see as a change and build
     again; the timing threshold keeps nearly every command's time. */
  def build(options: Options, dirs: List[Path], sessions: List[String], progress: Progress): Map[String, Built] = {
    val extra = List("document=false", "export_theory", "build_timing_threshold=0.001").map(Options.Spec.make)
    val results =
      Build.build(options, selection = Sessions.Selection(sessions = sessions), dirs = dirs, progress = progress,
        augment_options = s => if (sessions.contains(s)) extra else Nil)
    def cancelled = Built(false, true, Map.empty, Map.empty, 0, 0, Nil)
    sessions.map(session => session -> (if (results.cancelled(session)) cancelled else read(results, session))).toMap
  }

  private def read(results: Build.Results, session: String): Built = {
    val store = results.store
    using(store.open_database(session)) { db =>
      val commands = Properties.uncompress(store.read_command_timings(db, session))
      val times =
        commands.groupMapReduce(props => Path.explode(Position.File.get(props)).canonical.implode)(
          Markup.Timing_Properties.Elapsed.get)(_ + _)
      val timing = store.read_session_timing(db, session).ml_timing
      Built(results(session).ok, false, content(store, session), times, timing.elapsed.seconds,
        timing.cpu.seconds, store.read_errors(db, session))
    }
  }

  /* What each theory declares and proves, as a digest per type, constant, axiom, theorem statement,
     class relation and type instance; positions and printed names do not count. */
  def content(store: Store, session: String): Map[String, Set[String]] =
    using(Export.open_session_context0(store, session)) { context =>
      (for (thy <- Export_Theory.theory_names(context)) yield {
        val theory = Export_Theory.read_theory(context.theory(thy), permissive = true)
        def entities[A <: Export_Theory.Content[A]](kind: String, all: List[Export_Theory.Entity[A]],
            content: A => Any): List[String] =
          all.map(entity => kind + " " + entity.name + " " + entity.content.map(content))
        val lines =
          entities("type", theory.types, identity) ::: entities("const", theory.consts, identity) :::
          entities("axiom", theory.axioms, _.prop) ::: entities("thm", theory.thms, _.prop) :::
          theory.classrel.map(_.toString) ::: theory.arities.map(_.toString)
        thy -> lines.map(SHA1.digest(_).toString).toSet
      }).toMap
    }

  /* The sessions the copy needs from elsewhere must be built already, or its builds would build them. */
  def check_built(options: Options, dirs: List[Path], sessions: List[String]): Unit =
    if (sessions.nonEmpty) {
      val results =
        Build.build(options, selection = Sessions.Selection(sessions = sessions), dirs = dirs, build_heap = true,
          no_build = true)
      if (!results.ok) error("Build these first, the copy needs them: " + commas(sessions))
    }

  def clean(options: Options, sessions: List[String]): Unit = {
    val store = Store(options)
    for (session <- sessions) store.clean_output(None, session)
  }
}
