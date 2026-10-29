/* The linter_census tool: where a build's checking time went, read from the command timings that
   isabelle build stored in its log databases. */

package isabelle.isabelle_linter

import isabelle._


object Census {
  /* One stored command timing; build_timing_threshold decides which are stored. */
  sealed case class Timing(session: String, file: String, offset: Int, name: String, seconds: Double) {
    def text: String = Census.text_at(file, offset)
  }

  /* A session's total CPU time and its stored command timings. */
  sealed case class Session_Timings(name: String, cpu: Double, timings: List[Timing])


  /* The sessions that have a log database. */
  def logged_sessions(store: Store): List[String] =
    (for {
      dir <- store.input_dirs
      log = dir + Path.basic("log") if log.is_dir
      file <- File.read_dir(log) if file.endsWith(".db")
    } yield file.stripSuffix(".db")).distinct.sorted

  /* The sessions defined in select_dirs, as with isabelle build -D. */
  def selected(options: Options, dirs: List[Path], select_dirs: List[Path]): List[String] =
    if (select_dirs.isEmpty) Nil
    else Sessions.load_structure(options, dirs = dirs, select_dirs = select_dirs).build_selection(Sessions.Selection())

  def read_session(store: Store, session: String): Session_Timings =
    using(store.open_database(session)) { db =>
      val cpu = store.read_session_timing(db, session).ml_timing.cpu.seconds
      val timings =
        for (props <- Properties.uncompress(store.read_command_timings(db, session)))
        yield {
          val file = Properties.get(props, Markup.FILE).getOrElse("")
          val offset = Properties.get(props, Markup.OFFSET).map(Value.Int.parse).getOrElse(1)
          Timing(session, file, offset, Markup.Name.get(props), Markup.Timing_Properties.Elapsed.get(props))
        }
      Session_Timings(session, cpu, timings)
    }


  /* The command text, from its symbol offset; each file is read once. */

  private val sources = Synchronized(Map.empty[String, Option[Vector[Symbol.Symbol]]])

  def text_at(file: String, offset: Int): String = {
    val symbols =
      sources.change_result { cache =>
        val read = cache.getOrElse(file, {
          val path = Path.explode(file).expand
          if (path.is_file) Some(Symbol.explode(File.read(path)).toVector) else None
        })
        (read, cache + (file -> read))
      }
    symbols match {
      case None => "?"
      case Some(symbols) =>
        val text = symbols.slice(offset - 1, offset + 300).mkString
        Library.trim_line(text.takeWhile(_ != '\n')).take(160)
    }
  }


  /* the report: shares of the stored time, and the slowest steps */

  def share(part: Double, all: Double): String =
    if (all == 0) "-" else Library.format("%.1f%%", 100 * part / all)

  /* A theory outside every heap is checked again by each session that imports it. Keep each
     command once, with its lowest time, which load distorts least. */
  def distinct(sessions: List[Session_Timings]): List[Timing] =
    sessions.flatMap(_.timings).groupBy(timing => (timing.file, timing.offset)).values.map(_.minBy(_.seconds)).toList

  def report(sessions: List[Session_Timings], top: Int, progress: Progress): Unit = {
    val cpu = sessions.map(_.cpu).sum
    val all = sessions.map(_.timings.length).sum
    val timings = distinct(sessions).sortBy(-_.seconds)
    val stored = timings.map(_.seconds).sum

    progress.echo(sessions.length.toString + " sessions, " + Library.format("%.0f", cpu) + " s CPU, " +
      all + " stored commands, " + timings.length + " distinct, " + Library.format("%.0f", stored) + " s (" +
      share(stored, cpu) + " of CPU)")

    progress.echo("\nby command:")
    for ((name, commands) <- timings.groupBy(_.name).toList.sortBy(-_._2.map(_.seconds).sum).take(12)) {
      val seconds = commands.map(_.seconds).sum
      progress.echo(Library.format("  %-14s %7.0f s  %6s of CPU  %5d commands", name, seconds, share(seconds, cpu),
        commands.length))
    }

    progress.echo("\nconcentration:")
    for (k <- List(10, 100, 1000) if k < timings.length) {
      progress.echo("  top " + k + ": " + share(timings.take(k).map(_.seconds).sum, stored) + " of stored time")
    }

    progress.echo("\nslowest:")
    for (timing <- timings.take(top)) {
      progress.echo(Library.format("  %7.2f s  %-24s %s", timing.seconds, timing.session, timing.text))
    }
  }

  def write_tsv(path: Path, sessions: List[Session_Timings]): Unit = {
    val clean = (s: String) => s.replace('\t', ' ').nn
    val lines =
      for (timing <- distinct(sessions).sortBy(timing => (timing.session, timing.file, timing.offset)))
      yield List(timing.session, timing.file, timing.offset.toString, timing.name, timing.seconds.toString,
        clean(timing.text)).mkString("\t")
    File.write(path, ("session\tfile\toffset\tcommand\tseconds\ttext" :: lines).mkString("", "\n", "\n"))
  }


  val census_tool: Isabelle_Tool =
    Isabelle_Tool("linter_census", "where checking time goes, from the build logs", Scala_Project.here,
      { args =>
        val dirs = new scala.collection.mutable.ListBuffer[Path]
        val select_dirs = new scala.collection.mutable.ListBuffer[Path]
        var output: Option[Path] = None
        var top = 30
        var options = Options.init()

        val getopts = Getopts("""
Usage: isabelle linter_census [OPTIONS] [SESSIONS]

  Options are:
    -D DIR       include session directory and select its sessions
    -O FILE      also write every stored command timing to FILE (TSV)
    -d DIR       include session directory
    -n N         show the N slowest commands (default: 30)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Read the command timings that isabelle build stored for SESSIONS and the
  sessions of each -D DIR (default: every session with a log database) and
  show where the time goes. A command checked by several sessions counts
  once. Only commands slower than build_timing_threshold are stored, so build
  with -o build_timing_threshold=0.01 first.
""",
          "D:" -> (arg => select_dirs += Path.explode(arg)),
          "O:" -> (arg => output = Some(Path.explode(arg))),
          "d:" -> (arg => dirs += Path.explode(arg)),
          "n:" -> (arg => top = Value.Int.parse(arg)),
          "o:" -> (arg => options = options + arg))

        val store = Store(options)
        val logged = logged_sessions(store)
        val names = (getopts(args) ::: selected(options, dirs.toList, select_dirs.toList)) match {
          case Nil => logged
          case sessions => sessions.distinct.filter(logged.contains)
        }

        val progress = new Console_Progress()
        val sessions = names.map(read_session(store, _))

        report(sessions, top, progress)
        output.foreach(write_tsv(_, sessions))
      })
}
