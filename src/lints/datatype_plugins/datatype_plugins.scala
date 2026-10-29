/* The datatype_plugins lint: plugins of a `datatype` whose content nothing later uses, deleted
   with `plugins del:` if that makes the datatype faster. */

package isabelle.isabelle_linter

import isabelle._

import scala.util.matching.Regex


object Datatype_Plugins extends Lint {
  val name = "datatype_plugins"

  /* The plugins to delete, with the medians of the datatype with and without them. */
  sealed case class Fix(delete: List[String], medians: Medians)

  type Result = Either[List[Pide.Question], Option[Fix]]

  val plugins: List[String] = List("code", "extraction", "lifting", "quickcheck", "size", "transfer")

  /* quickcheck is also a command, so it needs quotes. */
  def plugins_del(delete: List[String]): String =
    "plugins del: " + delete.map(plugin => if (plugin == "quickcheck") quote(plugin) else plugin).mkString(" ")

  private val transfer_words = """transfer|lifting|lift_definition|parametric|quotient|\brel_|corec""".r

  /* Later text that may use a plugin's content without naming it. */
  val unnamed_uses: Map[String, Regex] = Map(
    "code" -> """(\b|_)code|\bCode|\b(value|eval|normalization|approximation|derive)\b""".r,
    "extraction" -> """\b(extract|realizers?|realizability)\b|Extraction""".r,
    "lifting" -> transfer_words,
    "quickcheck" -> """[Qq]uickcheck|\b(nitpick|try|random|exhaustive|narrowing|bounded_forall)\b""".r,
    "size" -> """\b(size\w*|\w+_size|lexicographic_order|size_change|measures?|termination|relation)\b""".r,
    "transfer" -> transfer_words)


  /* An options group like `(discs_sels)`, not type arguments like `('a, 'b)`. */
  def options_group(cmd: Cmd): List[Tok] =
    cmd.body match {
      case t :: u :: _ if t.is("(") && (u.is("plugins") || u.is("discs_sels")) => Syntax.take_group(cmd.body, "(", ")")._1
      case _ => Nil
    }

  def has_plugins(cmd: Cmd): Boolean = options_group(cmd).exists(_.is("plugins"))

  def deleting(lemma: Lemma, delete: List[String]): (Text.Range, String) = {
    val cmd = lemma.cmds.head
    val del = plugins_del(delete)
    options_group(cmd) match {
      case paren :: _ => Text.Range(paren.range.stop) -> (del + ", ")
      case Nil => Text.Range(cmd.tokens.head.range.stop) -> (" (" + del + ")")
    }
  }

  def edited(lemma: Lemma, delete: List[String]): String = lemma.replace_all(List(deleting(lemma, delete)))

  /* The type and constructor names of each spec of `t = C1 ... | C2 ... and u = ...`. */
  def names(cmd: Cmd): List[String] = {
    val body = cmd.body.drop(options_group(cmd).length)
    val specs = Syntax.split_and(body.takeWhile(t => !(t.token.is_keyword && (t.is("for") || t.is("where")))))
    specs.flatMap { spec =>
      val (lhs, rhs) = spec.span(!_.is("="))
      lhs.filter(_.token.is_ident).lastOption.map(_.source).toList ::: constructors(rhs.drop(1))
    }.distinct
  }

  /* An alternative is `C args` or `disc: C args`, where C may be a string with a mixfix after it. */
  private def constructors(rhs: List[Tok]): List[String] = {
    def alternatives(toks: List[Tok]): List[List[Tok]] = {
      var depth = 0
      toks.foldRight(List(List.empty[Tok])) { (t, acc) =>
        if (t.is(")")) depth += 1 else if (t.is("(")) depth -= 1
        if (depth == 0 && t.is("|")) Nil :: acc else (t :: acc.head) :: acc.tail
      }.filter(_.nonEmpty)
    }
    alternatives(rhs).flatMap {
      case disc :: colon :: ctor :: _ if colon.is(":") => List(disc.source, ctor.source)
      case ctor :: _ => List(ctor.source)
      case Nil => Nil
    }.map(Library.perhaps_unquote).filter(_.nonEmpty)
  }


  /* Later commands on the type: a nesting datatype needs all plugins, a fun needs size. */
  sealed case class Later(texts: List[String], nested: Boolean, recursion: Boolean)

  def later(lemma: Lemma): Later = {
    val texts = lemma.later
    val mentions = Downstream.words(names(lemma.cmds.head))
    def on_it(commands: Set[String]): Boolean =
      mentions.exists(regex => Downstream.commands(texts, commands).exists(regex.findFirstIn(_).isDefined))
    Later(texts, on_it(Set("datatype", "codatatype")), on_it(Set("fun", "function")))
  }

  def needed(later: Later, plugin: String, missing: List[String]): Option[String] = {
    val named = Downstream.words(missing).flatMap(Downstream.find(later.texts, _))
    val unnamed = Downstream.find(later.texts, unnamed_uses(plugin))
    (named orElse unnamed).map(word => "`" + word + "` later")
      .orElse(if (later.nested) Some("a later datatype uses the type") else None)
      .orElse(if (plugin == "size" && later.recursion) Some("a later `fun` on the type") else None)
  }

  /* Why each plugin must stay; quickcheck's generators are code. */
  def reasons(lemma: Lemma, missing: Map[String, List[String]]): Map[String, String] = {
    val uses = later(lemma)
    val direct =
      missing.toList.flatMap({ case (plugin, names) => needed(uses, plugin, names).map(plugin -> _) }).toMap
    direct.get("quickcheck") match {
      case Some(_) if !direct.contains("code") => direct + ("code" -> "quickcheck needs it")
      case _ => direct
    }
  }

  /* The plugins to delete, and why each other one stays. */
  sealed case class Plan(delete: List[String], kept: Map[String, String])

  def plan(lemma: Lemma, answer: Pide.Answer): Plan = {
    val runs = plugins.zipWithIndex.map({ case (plugin, i) => plugin -> Definitions.compared(answer, i + 1) })
    val failing = runs.collect({ case (plugin, None) => plugin -> "the datatype fails without it" }).toMap
    val missing = runs.collect({ case (plugin, Some(compared)) => plugin -> compared.missing }).toMap
    val kept = failing ++ reasons(lemma, missing)
    Plan(plugins.filterNot(kept.contains), kept)
  }


  /* Per datatype: run it as written and without each plugin alone, then delete those that nothing
     later needs. */
  def check(lemma: Lemma, answers: Pide.Answers, options: Options): Result = {
    val question = Definitions.names(lemma, plugins.map(plugin => edited(lemma, List(plugin))), options)
    answers.get(question.key) match {
      case None => Left(List(question))
      case Some(answer) if !answer.closes => Right(None)
      case Some(answer) =>
        plan(lemma, answer).delete match {
          case Nil => Right(None)
          case delete =>
            val timing = Definitions.timing(lemma, edited(lemma, delete), answer, options)
            answers.get(timing.key) match {
              case None => Left(List(timing))
              case Some(times) => Right(if (Definitions.saves(times, options)) Some(Fix(delete, times.medians)) else None)
            }
        }
    }
  }


  override def targets(checked: Pide.Checked): List[Lemma] =
    checked.definitions.filter(definition =>
      definition.ok && Set("datatype", "codatatype")(definition.cmds.head.name) && !has_plugins(definition.cmds.head))

  def ask(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Pide.Question] =
    lemmas.flatMap(check(_, answers, options).left.getOrElse(Nil))

  def report(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] =
    for {
      lemma <- lemmas
      fix <- check(lemma, answers, options).toOption.flatten.toList
    } yield finding(lemma, fix, answers)

  private def finding(lemma: Lemma, fix: Fix, answers: Pide.Answers): Finding = {
    val edit = deleting(lemma, fix.delete)
    val kept = plan(lemma, answers(Definitions.names_key(lemma))).kept.toList.sortBy(_._1)
    val message =
      "`" + lemma.cmds.head.name + " (" + plugins_del(fix.delete) + ")` takes " + fix.medians.after +
        " ms instead of " + fix.medians.before + " ms (medians, alone)" +
        kept.map({ case (plugin, why) => "\n  keeps " + plugin + ": " + why }).mkString
    Finding(name, lemma, lemma.line, message, Some(lemma.replace_all(List(edit))), Some(edit))
  }
}
