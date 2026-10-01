/* isabelle_linter: command-line tool */

package isabelle.isabelle_linter

import isabelle._


object Tool {
  val linter_tool: Isabelle_Tool =
    Isabelle_Tool("linter", "lint Isabelle sessions with the prover", Scala_Project.here,
      { args =>
        val dirs = new scala.collection.mutable.ListBuffer[Path]
        var options = Options.init()

        val getopts = Getopts("""
Usage: isabelle linter [OPTIONS] SESSION

  Options are:
    -d DIR       include session directory
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)

  Check SESSION once in a headless PIDE session, time every `by` step, and try
  standard methods on the slow ones (option faster_step_slow, in seconds).
""",
          "d:" -> (arg => dirs += Path.explode(arg)),
          "o:" -> (arg => options = options + arg))

        val session_name =
          getopts(args) match {
            case List(s) => s
            case _ => getopts.usage()
          }

        val progress = new Console_Progress()
        val findings = Pide.run(options, session_name, Faster_Step, dirs = dirs.toList, progress = progress)
        for (f <- findings) {
          progress.echo(f.step.theory.path.implode + ":" + f.step.line + ": " + f.message)
        }
        progress.echo(findings.length.toString + " faster steps found")
      })
}

class Tools extends Isabelle_Scala_Tools(Tool.linter_tool)
