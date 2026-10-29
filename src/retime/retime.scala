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

  def time_step(checked: Pide.Checked, lemma: Lemma, step: Step, runs: Int, timeout: Time,
      progress: Progress): (String, Option[Long], Option[Long], Option[Long], String) = {
    val key = lemma.key + ":" + step.cmd.offset + ":retime"
    val q = Pide.Question(key, lemma.theory, step.goal.command, "linter_times",
      List(runs.toString, step.methods), timeout)
    val answer = Pide.ask(checked.session, List(q), progress)(key)
    answer.long("ms0") match {
      case Some(ms) => ("closes", Some(ms), answer.long("cpu0"), answer.long("gc0"), answer.get("runs0").getOrElse(""))
      case None => (if (answer.closes) "fails" else answer.verdict, None, None, None, "")
    }
  }

  /* datatype_no_proper_subterm: as is, without, cached; in turn on the same state, then counted */
  val variant_fields: List[String] =
    (for (i <- List(0, 1, 2); f <- List("verdict", "ms", "cpu", "gc", "runs")) yield f + i) :::
      List("calls", "hits", "inside_ms", "step_ms", "counted_verdict")

  def time_variants(checked: Pide.Checked, lemma: Lemma, step: Step, runs: Int, timeout: Time,
      progress: Progress): List[String] = {
    val key = lemma.key + ":" + step.cmd.offset + ":variants"
    val total = Time.ms(timeout.ms * (3 * runs + 2))
    val q = Pide.Question(key, lemma.theory, step.goal.command, "linter_simproc_variants",
      List(runs.toString, timeout.ms.toString, step.methods), total)
    val answer = Pide.ask(checked.session, List(q), progress)(key)
    val fields = variant_fields.map(answer.get(_).getOrElse(""))
    if (answer.closes) fields else answer.verdict :: fields.tail
  }

  /* RETIME_WITHOUT set: the variants instead of the plain timing */
  def variants_mode: Boolean = Isabelle_System.getenv("RETIME_WITHOUT").nonEmpty

  def variants_line(checked: Pide.Checked, row: Row, found: Option[(Lemma, Step)], runs: Int, timeout: Time,
      progress: Progress): String = {
    val fields = found match {
      case None => "not_found" :: variant_fields.tail.map(_ => "")
      case Some((lemma, step)) => time_variants(checked, lemma, step, runs, timeout, progress)
    }
    progress.echo("retime: " + fields.mkString(" ") + " " + row.text.take(60))
    ((row.session :: row.file :: row.offset.toString :: row.seconds.toString :: fields) :+ row.text).mkString("\t")
  }

  /* the profile is a tracing message on the step's command; asked alone, it can only be this one's */
  val profile_top = 40

  def profile_step(checked: Pide.Checked, lemma: Lemma, step: Step, timeout: Time,
      progress: Progress): Option[ML_Profiling.Report] = {
    val key = lemma.key + ":" + step.cmd.offset + ":profile"
    val q = Pide.Question(key, lemma.theory, step.goal.command, "linter_profile", List(step.methods), timeout)
    val answer = Pide.ask(checked.session, List(q), progress)(key)
    if (!answer.closes) None
    else {
      val state = checked.session.get_state()
      state.command_results(state.snapshot(lemma.theory).version, step.goal.command).iterator
        .collect({ case (_, Protocol.ML_Profiling(report)) => report.clean_name }).toList.lastOption
    }
  }

  def profile_lines(row: Row, report: ML_Profiling.Report): List[String] = {
    val total = report.total.count
    /* clean names drop the id of each instance, so the same function can come more than once */
    val counts = report.entries.groupMapReduce(_.name)(_.count)(_ + _).toList.sortBy(-_._2)
    for (((name, count), i) <- counts.take(profile_top).zipWithIndex)
    yield List(row.session, row.file, row.offset.toString, i.toString, count.toString, total.toString,
      name.replace('\t', ' ')).mkString("\t")
  }

  /* lines for the timings and, if profile, for the profiles */
  def retime_session(options: Options, session_name: String, rows: List[Row], dirs: List[Path],
      profile: Boolean, progress: Progress): (List[String], List[String]) =
    Pide.check(options, session_name, dirs, progress, imported = true) { checked =>
      val runs = options.int("retime_runs")
      val results =
        for ((row, found) <- find_steps(checked, rows)) yield {
          val timeout = Time.seconds((row.seconds * options.real("retime_factor")) max 10.0)
          if (variants_mode) (variants_line(checked, row, found, runs, timeout, progress), Nil)
          else {
            val (verdict, median, cpu, gc, each) =
              found match {
                case None => ("not_found", None, None, None, "")
                case Some((lemma, step)) => time_step(checked, lemma, step, runs, timeout, progress)
              }
            val profiled =
              for {
                (lemma, step) <- found if profile && verdict == "closes"
                report <- profile_step(checked, lemma, step, timeout, progress)
              } yield profile_lines(row, report)

            progress.echo(String.format("retime: %8.2f s -> %s %s", row.seconds,
              median.map(ms => String.format("%.2f s", ms / 1000.0)).getOrElse(verdict), row.text.take(60)))
            val line =
              List(row.session, row.file, row.offset.toString, row.seconds.toString, verdict,
                List(median, cpu, gc).map(_.map(_.toString).getOrElse("")).mkString("\t"), runs.toString,
                each, row.text).mkString("\t")
            (line, profiled.getOrElse(Nil))
          }
        }
      (results.map(_._1), results.flatMap(_._2))
    }

  /* sessions already in output are skipped, so a long run can resume */
  def retime(options: Options, rows: List[Row], output: Path, profiles: Option[Path], dirs: List[Path],
      progress: Progress): Unit = {
    if (!output.is_file && variants_mode) {
      File.write(output, (List("session", "file", "offset", "census_s") ::: variant_fields ::: List("text"))
        .mkString("", "\t", "\n"))
    }
    if (!output.is_file) {
      File.write(output, "session\tfile\toffset\tcensus_s\tverdict\tmedian_ms\tcpu_ms\tgc_ms\truns\truns_ms\ttext\n")
    }
    for (path <- profiles if !path.is_file) {
      File.write(path, "session\tfile\toffset\trank\tcount\ttotal\tfunction\n")
    }
    val done = split_lines(File.read(output)).drop(1).filter(_.nonEmpty).map(_.takeWhile(_ != '\t')).toSet
    val sessions = rows.groupBy(_.session).toList.sortBy(-_._2.map(_.seconds).sum)
    for ((session_name, rs) <- sessions) {
      if (done(session_name)) progress.echo("Skipping " + session_name + ": already timed")
      else {
        progress.echo(session_name + ": " + rs.length + " steps")
        /* a session that stops (its prover died, say) is not written, so a resumed run retries it */
        try {
          val (lines, profile) = retime_session(options, session_name, rs, dirs, profiles.isDefined, progress)
          for (path <- profiles if profile.nonEmpty) File.append(path, profile.mkString("", "\n", "\n"))
          File.append(output, lines.mkString("", "\n", "\n"))
        }
        catch { case ERROR(msg) => progress.echo_warning("Retime unfinished: " + session_name + "\n" + msg) }
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
        var profiles: Option[Path] = None
        var options = Options.init()

        val getopts = Getopts("""
Usage: isabelle linter_retime [OPTIONS]

  Options are:
    -I FILE      census timings (default: timings.tsv, from linter_census -O)
    -O FILE      output file (default: retime.tsv)
    -P FILE      also profile each step once and write its busiest ML functions to FILE
    -d DIR       include session directory
    -n N         the N slowest `by` steps (default: 200)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Check each session that holds one of the N slowest `by` steps, then run
  each of those steps retime_runs times, one step at a time, and write the
  medians of wall-clock, cpu and gc time (cpu and gc are for the whole
  process, which is fair as only one step runs). The build's timings come from a loaded machine; these are the ones
  to report. Sessions already in FILE are skipped, so a run can resume.
""",
          "I:" -> (arg => input = Path.explode(arg)),
          "O:" -> (arg => output = Path.explode(arg)),
          "P:" -> (arg => profiles = Some(Path.explode(arg))),
          "d:" -> (arg => dirs += Path.explode(arg)),
          "n:" -> (arg => n = Value.Int.parse(arg)),
          "o:" -> (arg => options = options + arg))

        if (getopts(args).nonEmpty) getopts.usage()

        retime(options, slowest(read_rows(input), n), output, profiles, dirs.toList, new Console_Progress())
      })
}
