/* linter_retime: time the census's slowest `by` steps again, one at a time */

package isabelle.isabelle_linter

import isabelle._


object Retime {
  /* a census row: offset is in symbols, from 1 */
  sealed case class Row(session: String, file: String, offset: Int, seconds: Double, text: String)

  def read_rows(path: Path): List[Row] =
    for {
      line <- split_lines(File.read(path)).drop(1) if line.nonEmpty
      List(session, file, offset, command, seconds, text) = Library.space_explode('\t', line)
      if command == "by"
    } yield Row(session, file, Value.Int.parse(offset), Value.Double.parse(seconds), text)

  def slowest(rows: List[Row], n: Int): List[Row] = rows.sortBy(-_.seconds).take(n)


  /* the step a row points at */

  def same_file(a: Path, b: Path): Boolean = a.canonical_file == b.canonical_file

  def find_steps(checked: Pide.Checked, rows: List[Row]): List[(Row, Option[(Lemma, Step)])] = {
    val steps = for (lemma <- checked.lemmas if lemma.ok; step <- lemma.steps) yield (lemma, step)
    val index = Synchronized(Map.empty[String, Symbol.Index])
    def decode(lemma: Lemma, offset: Int): Int =
      index.change_result { m =>
        val i = m.getOrElse(lemma.theory.node, Symbol.Index(lemma.text))
        (i.decode(offset), m + (lemma.theory.node -> i))
      }
    for (row <- rows) yield {
      val file = Path.explode(row.file)
      row -> steps.find { case (lemma, step) =>
        same_file(lemma.theory.path, file) && step.cmd.range.start == decode(lemma, row.offset)
      }
    }
  }


  /* each step alone, so the runs do not compete */
  def retime_session(options: Options, session_name: String, rows: List[Row], dirs: List[Path],
      progress: Progress): List[String] =
    Pide.check(options, session_name, dirs, progress, imported = true) { checked =>
      val runs = options.int("retime_runs")
      for ((row, found) <- find_steps(checked, rows)) yield {
        val (verdict, median) =
          found match {
            case None => ("not_found", None)
            case Some((lemma, step)) =>
              val timeout = Time.seconds((row.seconds * options.real("retime_factor")) max 10.0)
              val key = lemma.key + ":" + step.cmd.offset + ":retime"
              val q = Pide.Question(key, lemma.theory, step.goal.command, "linter_times",
                List(runs.toString, step.methods), timeout)
              val answer = Pide.ask(checked.session, List(q), progress)(key)
              answer.long("ms0") match {
                case Some(ms) => ("closes", Some(ms))
                case None => (if (answer.closes) "fails" else answer.verdict, None)
              }
          }
        progress.echo(String.format("retime: %8.2f s -> %s %s", row.seconds,
          median.map(ms => String.format("%.2f s", ms / 1000.0)).getOrElse(verdict), row.text.take(60)))
        List(row.session, row.file, row.offset.toString, row.seconds.toString, verdict,
          median.map(_.toString).getOrElse(""), runs.toString, row.text).mkString("\t")
      }
    }

  /* sessions already in output are skipped, so a long run can resume */
  def retime(options: Options, rows: List[Row], output: Path, dirs: List[Path], progress: Progress): Unit = {
    if (!output.is_file) {
      File.write(output, "session\tfile\toffset\tcensus_s\tverdict\tmedian_ms\truns\ttext\n")
    }
    val done = split_lines(File.read(output)).drop(1).filter(_.nonEmpty).map(_.takeWhile(_ != '\t')).toSet
    val sessions = rows.groupBy(_.session).toList.sortBy(-_._2.map(_.seconds).sum)
    for ((session_name, rs) <- sessions) {
      if (done(session_name)) progress.echo("Skipping " + session_name + ": already timed")
      else {
        progress.echo(session_name + ": " + rs.length + " steps")
        val lines = retime_session(options, session_name, rs, dirs, progress)
        File.append(output, lines.mkString("", "\n", "\n"))
      }
    }
  }


  val retime_tool: Isabelle_Tool =
    Isabelle_Tool("linter_retime", "time the census's slowest `by` steps again, one at a time",
      Scala_Project.here,
      { args =>
        val dirs = new scala.collection.mutable.ListBuffer[Path]
        var input = Path.explode("timings.tsv")
        var n = 200
        var output = Path.explode("retime.tsv")
        var options = Options.init()

        val getopts = Getopts("""
Usage: isabelle linter_retime [OPTIONS]

  Options are:
    -I FILE      census timings (default: timings.tsv, from linter_census -O)
    -O FILE      output file (default: retime.tsv)
    -d DIR       include session directory
    -n N         the N slowest `by` steps (default: 200)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Check each session that holds one of the N slowest `by` steps, then run
  each of those steps retime_runs times, one step at a time, and write the
  median. The build's timings come from a loaded machine; these are the ones
  to report. Sessions already in FILE are skipped, so a run can resume.
""",
          "I:" -> (arg => input = Path.explode(arg)),
          "O:" -> (arg => output = Path.explode(arg)),
          "d:" -> (arg => dirs += Path.explode(arg)),
          "n:" -> (arg => n = Value.Int.parse(arg)),
          "o:" -> (arg => options = options + arg))

        if (getopts(args).nonEmpty) getopts.usage()

        retime(options, slowest(read_rows(input), n), output, dirs.toList, new Console_Progress())
      })
}
