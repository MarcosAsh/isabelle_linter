/* linter_census: where checking time goes, read from the build logs */

package isabelle.isabelle_linter

import isabelle._


object Census {
  /* one slow command: build_timing_threshold decides which are stored */
  sealed case class Timing(session: String, file: String, offset: Int, name: String, seconds: Double) {
    def text: String = Census.text_at(file, offset)
  }


  /* the sessions that have a log database */
  def logged_sessions(store: Store): List[String] =
    (for {
      dir <- store.input_dirs
      log = dir + Path.basic("log") if log.is_dir
      file <- File.read_dir(log) if file.endsWith(".db")
    } yield file.stripSuffix(".db")).distinct.sorted

  /* the sessions defined in select_dirs, as isabelle build -D */
  def selected(options: Options, dirs: List[Path], select_dirs: List[Path]): List[String] =
    if (select_dirs.isEmpty) Nil
    else Sessions.load_structure(options, dirs = dirs, select_dirs = select_dirs).build_selection(Sessions.Selection())

  def read_session(store: Store, session: String): (Double, List[Timing]) =
    using(store.open_database(session)) { db =>
      val cpu = store.read_session_timing(db, session).ml_timing.cpu.seconds
      val timings =
        for (props <- Properties.uncompress(store.read_command_timings(db, session)))
        yield {
          val file = Properties.get(props, Markup.FILE).getOrElse("")
          val offset = Properties.get(props, Markup.OFFSET).map(Value.Int.parse).getOrElse(1)
          Timing(session, file, offset, Markup.Name.get(props), Markup.Timing_Properties.Elapsed.get(props))
        }
      (cpu, timings)
    }


  /* the command text, from its symbol offset */

  private val sources = Synchronized(Map.empty[String, Option[Vector[Symbol.Symbol]]])

  def text_at(file: String, offset: Int): String = {
    val symbols =
      sources.change_result { cache =>
        val syms = cache.getOrElse(file, {
          val path = Path.explode(file).expand
          if (path.is_file) Some(Symbol.explode(File.read(path)).toVector) else None
        })
        (syms, cache + (file -> syms))
      }
    symbols match {
      case None => "?"
      case Some(syms) =>
        val text = syms.slice(offset - 1, offset + 300).mkString
        Library.trim_line(text.takeWhile(_ != '\n')).take(160)
    }
  }


  /* the report: shares of the stored time, and the slowest steps */

  def share(part: Double, all: Double): String =
    if (all == 0) "-" else Library.format("%.1f%%", 100 * part / all)

  /* a theory outside every heap is checked again by each session that imports it; keep each
    command once, with its lowest time, the one least distorted by load */
  def distinct(sessions: List[(String, Double, List[Timing])]): List[Timing] =
    sessions.flatMap(_._3).groupBy(t => (t.file, t.offset)).values.map(_.minBy(_.seconds)).toList

  def report(sessions: List[(String, Double, List[Timing])], top: Int, progress: Progress): Unit = {
    val cpu = sessions.map(_._2).sum
    val all = sessions.map(_._3.length).sum
    val timings = distinct(sessions).sortBy(-_.seconds)
    val stored = timings.map(_.seconds).sum

    progress.echo(sessions.length.toString + " sessions, " + Library.format("%.0f", cpu) + " s CPU, " +
      all + " stored commands, " + timings.length + " distinct, " + Library.format("%.0f", stored) + " s (" +
      share(stored, cpu) + " of CPU)")

    progress.echo("\nby command:")
    for ((name, ts) <- timings.groupBy(_.name).toList.sortBy(-_._2.map(_.seconds).sum).take(12)) {
      val t = ts.map(_.seconds).sum
      progress.echo(Library.format("  %-14s %7.0f s  %6s of CPU  %5d commands", name, t, share(t, cpu), ts.length))
    }

    progress.echo("\nconcentration:")
    for (k <- List(10, 100, 1000) if k < timings.length) {
      progress.echo("  top " + k + ": " + share(timings.take(k).map(_.seconds).sum, stored) + " of stored time")
    }

    progress.echo("\nslowest:")
    for (t <- timings.take(top)) {
      progress.echo(Library.format("  %7.2f s  %-24s %s", t.seconds, t.session, t.text))
    }
  }

  def write_tsv(path: Path, sessions: List[(String, Double, List[Timing])]): Unit = {
    val clean = (s: String) => s.replace('\t', ' ').nn
    val lines =
      for (t <- distinct(sessions).sortBy(t => (t.session, t.file, t.offset)))
      yield List(t.session, t.file, t.offset.toString, t.name, t.seconds.toString, clean(t.text)).mkString("\t")
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
          case ss => ss.distinct.filter(logged.contains)
        }

        val progress = new Console_Progress()
        val sessions =
          for (name <- names) yield {
            val (cpu, timings) = read_session(store, name)
            (name, cpu, timings)
          }

        report(sessions, top, progress)
        output.foreach(write_tsv(_, sessions))
      })
}
