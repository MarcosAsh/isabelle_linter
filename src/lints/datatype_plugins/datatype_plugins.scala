/* datatype_plugins: plugins of a `datatype` whose content nothing later uses */

package isabelle.isabelle_linter

import isabelle._

import scala.util.matching.Regex


object Datatype_Plugins extends Lint {
  val name = "datatype_plugins"

  /* questions to ask, or the plugins to delete with both median times */
  type Result = Either[List[Pide.Question], Option[(List[String], Long, Long)]]

  val plugins: List[String] = List("code", "extraction", "lifting", "quickcheck", "size", "transfer")

  /* quickcheck is also a command, so it needs quotes */
  def plugins_del(ps: List[String]): String =
    "plugins del: " + ps.map(p => if (p == "quickcheck") quote(p) else p).mkString(" ")

  private val transfer_words = """transfer|lifting|lift_definition|parametric|quotient|\brel_|corec""".r

  /* later text that may use a plugin's content without naming it */
  val unnamed_uses: Map[String, Regex] = Map(
    "code" -> """(\b|_)code|\bCode|\b(value|eval|normalization|approximation|derive)\b""".r,
    "extraction" -> """\b(extract|realizers?|realizability)\b|Extraction""".r,
    "lifting" -> transfer_words,
    "quickcheck" -> """[Qq]uickcheck|\b(nitpick|try|random|exhaustive|narrowing|bounded_forall)\b""".r,
    "size" -> """\b(size\w*|\w+_size|lexicographic_order|size_change|measures?|termination|relation)\b""".r,
    "transfer" -> transfer_words)


  /* an options group like `(discs_sels)`, not type arguments like `('a, 'b)` */
  def options_group(cmd: Cmd): List[Tok] =
    cmd.body match {
      case t :: u :: _ if t.is("(") && (u.is("plugins") || u.is("discs_sels")) => Syntax.take_group(cmd.body, "(", ")")._1
      case _ => Nil
    }

  def has_plugins(cmd: Cmd): Boolean = options_group(cmd).exists(_.is("plugins"))

  def deleting(lemma: Lemma, ps: List[String]): (Text.Range, String) = {
    val cmd = lemma.cmds.head
    val del = plugins_del(ps)
    options_group(cmd) match {
      case paren :: _ => Text.Range(paren.range.stop) -> (del + ", ")
      case Nil => Text.Range(cmd.tokens.head.range.stop) -> (" (" + del + ")")
    }
  }

  def edited(lemma: Lemma, ps: List[String]): String = lemma.replace_all(List(deleting(lemma, ps)))

  /* the type and constructor names of each spec of `t = C1 ... | C2 ... and u = ...` */
  def names(cmd: Cmd): List[String] = {
    val body = cmd.body.drop(options_group(cmd).length)
    val specs = Syntax.split_and(body.takeWhile(t => !(t.token.is_keyword && (t.is("for") || t.is("where")))))
    specs.flatMap { spec =>
      val (lhs, rhs) = spec.span(!_.is("="))
      lhs.filter(_.token.is_ident).lastOption.map(_.source).toList ::: constructors(rhs.drop(1))
    }.distinct
  }

  /* `disc: C args`, where C may be a string with a mixfix after it */
  private def constructors(rhs: List[Tok]): List[String] = {
    def alternatives(toks: List[Tok]): List[List[Tok]] = {
      var depth = 0
      toks.foldRight(List(List.empty[Tok])) { (t, acc) =>
        if (t.is(")")) depth += 1 else if (t.is("(")) depth -= 1
        if (depth == 0 && t.is("|")) Nil :: acc else (t :: acc.head) :: acc.tail
      }.filter(_.nonEmpty)
    }
    alternatives(rhs).flatMap {
      case d :: c :: n :: _ if c.is(":") => List(d.source, n.source)
      case n :: _ => List(n.source)
      case Nil => Nil
    }.map(Library.perhaps_unquote).filter(_.nonEmpty)
  }


  /* later commands on the type: a nesting datatype needs all plugins, a fun needs size */
  sealed case class Later(texts: List[String], nested: Boolean, recursion: Boolean)

  def later(lemma: Lemma): Later = {
    val texts = lemma.later
    val mentions = Downstream.words(names(lemma.cmds.head))
    def on_it(commands: Set[String]): Boolean =
      mentions.exists(m => Downstream.commands(texts, commands).exists(m.findFirstIn(_).isDefined))
    Later(texts, on_it(Set("datatype", "codatatype")), on_it(Set("fun", "function")))
  }

  def needed(later: Later, plugin: String, missing: List[String]): Option[String] = {
    val named = Downstream.words(missing).flatMap(Downstream.find(later.texts, _))
    val unnamed = Downstream.find(later.texts, unnamed_uses(plugin))
    (named orElse unnamed).map(w => "`" + w + "` later")
      .orElse(if (later.nested) Some("a later datatype uses the type") else None)
      .orElse(if (plugin == "size" && later.recursion) Some("a later `fun` on the type") else None)
  }

  /* quickcheck's generators are code */
  def reasons(lemma: Lemma, missing: Map[String, List[String]]): Map[String, String] = {
    val l = later(lemma)
    val direct = missing.toList.flatMap({ case (p, ms) => needed(l, p, ms).map(p -> _) }).toMap
    direct.get("quickcheck") match {
      case Some(_) if !direct.contains("code") => direct + ("code" -> "quickcheck needs it")
      case _ => direct
    }
  }

  def plan(lemma: Lemma, answer: Pide.Answer): (List[String], Map[String, String]) = {
    val runs = plugins.zipWithIndex.map({ case (p, i) => p -> Definitions.compared(answer, i + 1) })
    val failing = runs.collect({ case (p, None) => p -> "the datatype fails without it" }).toMap
    val kept = failing ++ reasons(lemma, runs.collect({ case (p, Some(c)) => p -> c.missing }).toMap)
    (plugins.filterNot(kept.contains), kept)
  }


  /* per datatype: as written, without each plugin alone; delete those nothing later needs */

  def check(lemma: Lemma, answers: Pide.Answers, options: Options): Result = {
    val q = Definitions.names(lemma, plugins.map(p => edited(lemma, List(p))), options)
    answers.get(q.key) match {
      case None => Left(List(q))
      case Some(a) if !a.closes => Right(None)
      case Some(a) =>
        plan(lemma, a)._1 match {
          case Nil => Right(None)
          case delete =>
            val t = Definitions.timing(lemma, edited(lemma, delete), a, options)
            answers.get(t.key) match {
              case None => Left(List(t))
              case Some(b) => Right(if (Definitions.saves(b, options)) Some((delete, b.ms, b.ms2)) else None)
            }
        }
    }
  }


  override def targets(checked: Pide.Checked): List[Lemma] =
    checked.definitions.filter(d => d.ok && Set("datatype", "codatatype")(d.cmds.head.name) && !has_plugins(d.cmds.head))

  def ask(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Pide.Question] =
    lemmas.flatMap(check(_, answers, options).left.getOrElse(Nil))

  def report(lemmas: List[Lemma], answers: Pide.Answers, options: Options): List[Finding] =
    for {
      lemma <- lemmas
      (delete, before, after) <- check(lemma, answers, options).toOption.flatten.toList
    } yield finding(lemma, delete, before, after, answers)

  private def finding(lemma: Lemma, delete: List[String], before: Long, after: Long, answers: Pide.Answers): Finding = {
    val edit = deleting(lemma, delete)
    val kept = plan(lemma, answers(Definitions.names_key(lemma)))._2.toList.sortBy(_._1)
    val message =
      "`" + lemma.cmds.head.name + " (" + plugins_del(delete) + ")` takes " + after +
        " ms instead of " + before + " ms (medians, alone)" +
        kept.map({ case (p, why) => "\n  keeps " + p + ": " + why }).mkString
    Finding(name, lemma, lemma.line, message, Some(lemma.replace_all(List(edit))), Some(edit))
  }
}
