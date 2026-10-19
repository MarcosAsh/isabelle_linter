/* isabelle_linter: command-line tool */

package isabelle.isabelle_linter

import isabelle._


object Tool {
  val lints: List[Lint] = List(Unused, Faster_Step, Diagnostic_Commands)

  /* each fix was checked alone: combine edits of disjoint ranges, otherwise one fix per lemma; an
    edit may reach past its lemma, like a deletion that takes its line with it */
  def lemma_fix(fs: List[Finding]): (Text.Range, String) = {
    val lemma = fs.head.lemma
    val edits = fs.flatMap(_.edit).distinct.sortBy(_._1.start)
    val ranges = edits.map(_._1)
    val disjoint = ranges.zip(ranges.drop(1)).forall({ case (a, b) => a.stop <= b.start })
    if (fs.forall(_.edit.isDefined) && disjoint) {
      val range = Text.Range(ranges.head.start min lemma.start, ranges.last.stop max lemma.stop)
      range -> replace(lemma.text, range, edits)
    }
    else Text.Range(lemma.start, lemma.stop) -> fs.head.fix.get
  }

  /* the text of range with the edits inside it, sorted and disjoint */
  def replace(text: String, range: Text.Range, edits: List[(Text.Range, String)]): String =
    edits.reverse.foldLeft(range.substring(text)) { case (t, (r, s)) =>
      t.substring(0, r.start - range.start) + s + t.substring(r.stop - range.start)
    }

  def apply_fixes(findings: List[Finding], progress: Progress): Unit =
    for ((theory, fs) <- findings.filter(_.fix.isDefined).groupBy(_.lemma.theory)) {
      val path = theory.path
      val text = File.read(path)
      val checked = fs.head.lemma.text
      val lemmas = fs.groupBy(_.lemma.start).values.toList
      val fixed =
        lemmas.map(lemma_fix).sortBy(_._1.start).reverse.foldLeft(text) { case (t, (r, s)) =>
          if (r.substring(t) != r.substring(checked)) error("File changed: " + path)
          t.substring(0, r.start) + s + t.substring(r.stop)
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
    -l LINTS     comma-separated lints to run (default: """ + lints.map(_.name).mkString(",") + """)
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
        val run = selected.map(n => lints.find(_.name == n).getOrElse(error("Unknown lint " + quote(n))))

        val progress = new Console_Progress()
        val findings = Pide.run(options, session_name, run, dirs = dirs.toList, progress = progress)
        for (f <- findings.sortBy(f => (f.lemma.theory.node, f.line))) {
          progress.echo("\n" + f.lemma.theory.path.implode + ":" + f.line + ": [" + f.lint + "] " + f.message)
        }
        progress.echo("\n" + findings.length + " findings")
        if (fix) apply_fixes(findings, progress)
      })
}

class Tools extends Isabelle_Scala_Tools(Tool.linter_tool, Collect.collect_tool, Census.census_tool, Retime.retime_tool,
  Parent.parent_tool)
