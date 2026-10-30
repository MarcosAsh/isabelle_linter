/* What datatype_plugins and fun_to_primrec share: comparing the names and facts a definition makes
   with and without a fix, and timing both. */

package isabelle.isabelle_linter

import isabelle._


object Definitions {
  /* One edited definition against the original, from a linter_names answer. */
  sealed case class Compared(ms: Long, missing: List[String], differ: List[String], reordered: List[String])

  def names_key(lemma: Lemma): String = lemma.key + ":names"

  /* The definition as written, then each edit, run from the state before it. */
  def names(lemma: Lemma, edits: List[String], options: Options): Pide.Question =
    Pide.Question(names_key(lemma), lemma.theory, lemma.before.command, "linter_names", lemma.source :: edits,
      Time.seconds(options.real("linter_timeout")))

  /* Edit i, counted from 1, if it ran. */
  def compared(answer: Pide.Answer, i: Int): Option[Compared] = {
    def words(name: String): List[String] =
      Library.space_explode(' ', answer.get(name + i).getOrElse("")).filter(_.nonEmpty)
    if (!answer.get("ok" + i).contains("closes")) None
    else Some(Compared(answer.long("ms" + i).getOrElse(0L), words("missing"), words("differ"), words("reordered")))
  }

  /* The definition as written and fixed, alone; each run gets the budget. */
  def timing(lemma: Lemma, fixed: String, original: Pide.Answer, options: Options): Pide.Question =
    Pide.Question(lemma.key + ":time", lemma.theory, lemma.before.command, "linter_runs",
      List(options.int("definition_runs").toString, lemma.source, fixed), Time.ms(Pide.budget(original, options)),
      serial = true)

  def saves(timing: Pide.Answer, options: Options): Boolean =
    timing.closes && timing.ms2 <= timing.ms * (1 - options.real("definition_saving"))
}
