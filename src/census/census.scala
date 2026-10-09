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

  def read_session(store: Store, session: String): (Double, List[Timing]) =
    using(store.open_database(session)) { db =>
      val timing = store.read_session_timing(db, session)
      val cpu = Properties.get(timing, "cpu").map(Value.Double.parse).getOrElse(0.0)
      val timings =
        for (props <- Properties.uncompress(store.read_command_timings(db, session)))
        yield {
          val file = Properties.get(props, Markup.FILE).getOrElse("")
          val offset = Properties.get(props, Markup.OFFSET).map(Value.Int.parse).getOrElse(1)
          Timing(session, file, offset, Markup.Name.get(props), Markup.Elapsed.get(props))
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
    if (all == 0) "-" else String.format("%.1f%%", 100 * part / all)

  def report(sessions: List[(String, Double, List[Timing])], top: Int, progress: Progress): Unit = {
    val cpu = sessions.map(_._2).sum
    val timings = sessions.flatMap(_._3).sortBy(-_.seconds)
    val stored = timings.map(_.seconds).sum

    progress.echo(sessions.length + " sessions, " + String.format("%.0f", cpu) + " s CPU, " +
      timings.length + " stored commands, " + String.format("%.0f", stored) + " s (" + share(stored, cpu) + " of CPU)")

    progress.echo("\nby command:")
    for ((name, ts) <- timings.groupBy(_.name).toList.sortBy(-_._2.map(_.seconds).sum).take(12)) {
      val t = ts.map(_.seconds).sum
      progress.echo(String.format("  %-14s %7.0f s  %6s of CPU  %5d commands", name, t, share(t, cpu), ts.length))
    }

    progress.echo("\nconcentration:")
    for (k <- List(10, 100, 1000) if k < timings.length) {
      progress.echo("  top " + k + ": " + share(timings.take(k).map(_.seconds).sum, stored) + " of stored time")
    }

    progress.echo("\nslowest:")
    for (t <- timings.take(top)) {
      progress.echo(String.format("  %7.2f s  %-24s %s", t.seconds, t.session, t.text))
    }
  }

  def write_tsv(path: Path, sessions: List[(String, Double, List[Timing])]): Unit = {
    val clean = (s: String) => s.replace('\t', ' ')
    val lines =
      for ((_, _, ts) <- sessions; t <- ts)
      yield List(t.session, t.file, t.offset.toString, t.name, t.seconds.toString, clean(t.text)).mkString("\t")
    File.write(path, ("session\tfile\toffset\tcommand\tseconds\ttext" :: lines).mkString("", "\n", "\n"))
  }


  val census_tool: Isabelle_Tool =
    Isabelle_Tool("linter_census", "where checking time goes, from the build logs", Scala_Project.here,
      { args =>
        var output: Option[Path] = None
        var top = 30
        var options = Options.init()

        val getopts = Getopts("""
Usage: isabelle linter_census [OPTIONS] [SESSIONS]

  Options are:
    -O FILE      also write every stored command timing to FILE (TSV)
    -n N         show the N slowest commands (default: 30)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Read the command timings that isabelle build stored for SESSIONS (default:
  every session with a log database) and show where the time goes. Only
  commands slower than build_timing_threshold are stored, so build with
  -o build_timing_threshold=0.01 first.
""",
          "O:" -> (arg => output = Some(Path.explode(arg))),
          "n:" -> (arg => top = Value.Int.parse(arg)),
          "o:" -> (arg => options = options + arg))

        val store = Store(options)
        val names = getopts(args) match {
          case Nil => logged_sessions(store)
          case ss => ss
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
