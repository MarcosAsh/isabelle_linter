/* isabelle_linter: command-line tool */

package isabelle.isabelle_linter

import isabelle._


object Tool {
  val lints: List[Lint] = List(Unused, Faster_Step)

  /* each fix was checked alone: combine edits of disjoint ranges, otherwise one fix per lemma */
  def lemma_fix(fs: List[Finding]): String = {
    val edits = fs.flatMap(_.edit)
    val ranges = edits.map(_._1).sortBy(_.start)
    val disjoint = ranges.zip(ranges.drop(1)).forall({ case (a, b) => a.stop <= b.start })
    if (edits.length == fs.length && disjoint) fs.head.lemma.replace_all(edits) else fs.head.fix.get
  }

  def apply_fixes(findings: List[Finding], progress: Progress): Unit =
    for ((theory, fs) <- findings.filter(_.fix.isDefined).groupBy(_.lemma.theory)) {
      val path = theory.path
      val text = File.read(path)
      val lemmas = fs.groupBy(_.lemma.start).values.toList.sortBy(_.head.lemma.start).reverse
      val fixed =
        lemmas.foldLeft(text) { (t, lfs) =>
          val l = lfs.head.lemma
          if (t.substring(l.start, l.stop) != l.source) error("File changed: " + path)
          t.substring(0, l.start) + lemma_fix(lfs) + t.substring(l.stop)
        }
      File.write(path, fixed)
      progress.echo("Fixed " + lemmas.length + " lemmas (" + fs.length + " findings) in " + path.implode)
    }

  val linter_tool: Isabelle_Tool =
    Isabelle_Tool("linter", "lint an Isabelle session with the prover", Scala_Project.here,
      { args =>
        val dirs = new scala.collection.mutable.ListBuffer[Path]
        var fix = false
        var selected = lints.map(_.name)
        var options = Options.init()

        val getopts = Getopts("""
Usage: isabelle linter [OPTIONS] SESSION

  Options are:
    -F           apply the fixes to the theory files
    -d DIR       include session directory
    -l LINTS     comma-separated lints to run (default: """ + lints.map(_.name).mkString(",") + """;
                 also """ + Unused_Imports.name + """, which builds an edited copy of SESSION)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Check SESSION once in a headless PIDE session, then run the lints, which ask
  the prover about single lemmas.
""",
          "F" -> (_ => fix = true),
          "d:" -> (arg => dirs += Path.explode(arg)),
          "l:" -> (arg => selected = Library.space_explode(',', arg)),
          "o:" -> (arg => options = options + arg))

        val session_name =
          getopts(args) match {
            case List(s) => s
            case _ => getopts.usage()
          }
        val (imports, others) = selected.partition(_ == Unused_Imports.name)
        val run = others.map(n => lints.find(_.name == n).getOrElse(error("Unknown lint " + quote(n))))

        val progress = new Console_Progress()
        if (run.nonEmpty) {
          val findings = Pide.run(options, session_name, run, dirs = dirs.toList, progress = progress)
          for (f <- findings.sortBy(f => (f.lemma.theory.node, f.line))) {
            progress.echo("\n" + f.lemma.theory.path.implode + ":" + f.line + ": [" + f.lint + "] " + f.message)
          }
          progress.echo("\n" + findings.length + " findings")
          if (fix) apply_fixes(findings, progress)
        }
        if (imports.nonEmpty) Unused_Imports.run(options, session_name, dirs.toList, progress, fix)
      })
}

class Tools extends Isabelle_Scala_Tools(Tool.linter_tool, Collect.collect_tool, Census.census_tool, Retime.retime_tool)
