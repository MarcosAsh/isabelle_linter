/* what the definition lints share: naming and timing a definition with and without a fix */

package isabelle.isabelle_linter

import isabelle._


object Definitions {
  /* one edited definition against the original, from a linter_names answer */
  sealed case class Compared(ms: Long, missing: List[String], differ: List[String], reordered: List[String])

  def names_key(lemma: Lemma): String = lemma.key + ":names"

  /* the definition as written, then each edit, run from the state before it */
  def names(lemma: Lemma, edits: List[String], options: Options): Pide.Question =
    Pide.Question(names_key(lemma), lemma.theory, lemma.before.command, "linter_names", lemma.source :: edits,
      Time.seconds(options.real("linter_timeout")))

  /* edit i (from 1), if it ran */
  def compared(a: Pide.Answer, i: Int): Option[Compared] = {
    def words(name: String): List[String] = Library.space_explode(' ', a.get(name + i).getOrElse("")).filter(_.nonEmpty)
    if (!a.get("ok" + i).contains("closes")) None
    else Some(Compared(a.long("ms" + i).getOrElse(0L), words("missing"), words("differ"), words("reordered")))
  }

  /* as written and fixed, alone; each run gets linter_factor times the first (min 1s) */
  def timing(lemma: Lemma, fixed: String, original: Pide.Answer, options: Options): Pide.Question = {
    val budget = (original.ms * options.real("linter_factor")).toLong max 1000L
    Pide.Question(lemma.key + ":time", lemma.theory, lemma.before.command, "linter_runs",
      List(options.int("definition_runs").toString, lemma.source, fixed), Time.ms(budget), serial = true)
  }

  def saves(t: Pide.Answer, options: Options): Boolean =
    t.closes && t.ms2 <= t.ms * (1 - options.real("definition_saving"))
}
