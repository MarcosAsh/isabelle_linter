/* The `isabelle linter` tool: run the lints on a session, print the findings and, with -F, write
   the fixes into the theory files. */

package isabelle.isabelle_linter

import isabelle._


object Tool {
  val lints: List[Lint] =
    List(Unused, Faster_Step, Diagnostic_Commands, Simp_Hygiene, Datatype_Plugins, Fun_To_Primrec, Simp_Scope)

  /* simp_hygiene runs by default only where Isabelle counts simp rules. */
  val default_lints: List[Lint] = lints.filter(lint => lint != Simp_Hygiene || Simp_Hygiene.available)

  /* Each fix was checked alone, so the edits of one lemma combine only if their ranges are
     disjoint; otherwise the first fix wins. An edit may reach past its lemma, like a deleted line. */
  def lemma_fix(findings: List[Finding]): (Text.Range, String) = {
    val lemma = findings.head.lemma
    val edits = findings.flatMap(_.edit).distinct.sortBy(_._1.start)
    val ranges = edits.map(_._1)
    val disjoint = ranges.zip(ranges.drop(1)).forall({ case (first, second) => first.stop <= second.start })
    if (findings.forall(_.edit.isDefined) && disjoint) {
      val range = Text.Range(ranges.head.start min lemma.start, ranges.last.stop max lemma.stop)
      range -> Lemma.edit(range.substring(lemma.text), range.start, edits)
    }
    else Text.Range(lemma.start, lemma.stop) -> findings.head.fix.get
  }

  def apply_fixes(findings: List[Finding], progress: Progress): Unit =
    for ((theory, theory_findings) <- findings.filter(_.fix.isDefined).groupBy(_.lemma.theory)) {
      val path = theory.path
      val text = File.read(path)
      val checked = theory_findings.head.lemma.text
      val lemmas = theory_findings.groupBy(_.lemma.start).values.toList
      val fixed =
        lemmas.map(lemma_fix).sortBy(_._1.start).reverse.foldLeft(text) { case (edited, (range, replacement)) =>
          if (range.substring(edited) != range.substring(checked)) error("File changed: " + path)
          edited.substring(0, range.start).nn + replacement + edited.substring(range.stop)
        }
      File.write(path, fixed)
      progress.echo("Fixed " + lemmas.length + " lemmas (" + theory_findings.length + " findings) in " + path.implode)
    }

  val linter_tool: Isabelle_Tool =
    Isabelle_Tool("linter", "lint an Isabelle session with the prover", Scala_Project.here,
      { args =>
        val dirs = new scala.collection.mutable.ListBuffer[Path]
        var fix = false
        var selected = default_lints.map(_.name)
        var options = Options.init()

        val getopts = Getopts("""
Usage: isabelle linter [OPTIONS] SESSION

  Options are:
    -F           apply the fixes to the theory files
    -d DIR       include session directory
    -l LINTS     comma-separated lints to run (default: """ + default_lints.map(_.name).mkString(",") + """;
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
        val run = others.map(name => lints.find(_.name == name).getOrElse(error("Unknown lint " + quote(name))))

        val progress = new Console_Progress()
        if (run.nonEmpty) {
          val findings = Pide.run(options, session_name, run, dirs = dirs.toList, progress = progress)
          for (finding <- findings.sortBy(finding => (finding.lemma.theory.node, finding.line))) {
            progress.echo("\n" + finding.lemma.theory.path.implode + ":" + finding.line + ": [" + finding.lint + "] " +
              finding.message)
          }
          progress.echo("\n" + findings.length + " findings")
          if (fix) apply_fixes(findings, progress)
        }
        if (imports.nonEmpty) Unused_Imports.run(options, session_name, dirs.toList, progress, fix)
      })
}

class Tools extends Isabelle_Scala_Tools(Tool.linter_tool, Collect.collect_tool, Census.census_tool, Retime.retime_tool,
  Parent.parent_tool)
