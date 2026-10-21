/* isabelle_linter: the theories that may use what a theory defines */

package isabelle.isabelle_linter

import isabelle._

import scala.util.matching.Regex


/* own text and later texts without comments, read lazily */
final class Downstream(own: () => String, read: () => List[String]) {
  lazy val theory: String = own()
  lazy val texts: List[String] = read()
}


object Downstream {
  val none: Downstream = new Downstream(() => "", () => Nil)

  /* per theory: texts of importing theories and of sessions built on it (a superset is safe) */
  def make(structure: Sessions.Structure, session: String, own: List[Path],
      snapshots: Map[Document.Node.Name, Document.Snapshot]): Document.Node.Name => Downstream = {
    lazy val sessions = session_texts(structure, session, own)
    val imports = snapshots.map({ case (name, s) => name -> s.node.header.imports })
    def text(name: Document.Node.Name): String = formal(snapshots(name).node.source)
    name => new Downstream(() => text(name), () => importers(imports, name).map(text) ::: sessions)
  }

  def importers(imports: Map[Document.Node.Name, List[Document.Node.Name]],
      name: Document.Node.Name): List[Document.Node.Name] = {
    @scala.annotation.tailrec
    def close(found: Set[Document.Node.Name]): Set[Document.Node.Name] = {
      val more = imports.collect({ case (n, is) if !found(n) && is.exists(found) => n }).toSet
      if (more.isEmpty) found else close(found ++ more)
    }
    (close(Set(name)) - name).toList
  }

  /* the session's own theories are left out: their order is known */
  def session_texts(structure: Sessions.Structure, session: String, own: List[Path]): List[String] = {
    val later = structure.build_descendants(List(session)).filterNot(_ == session)
    val skip = own.map(_.canonical_file).toSet
    val files =
      later.map(structure(_).dir.canonical_file).distinct
        .flatMap(dir => File.find_files(dir, _.getName.endsWith(".thy")))
    files.map(_.getCanonicalFile).distinct.filterNot(skip).map(f => formal(File.read(f)))
  }


  /* comments and document text blanked, offsets kept: words there use nothing */

  private val opens = List("\\<open>", "\u2039")
  private val closes = List("\\<close>", "\u203a")
  private val document = "(?m)\\A[ \\t]*(chapter|section|subsection|subsubsection|paragraph|text|txt|text_raw)\\s*".r
  private val comment = "\\A\\\\<comment>\\s*".r

  def formal(text: String): String = {
    val out = new StringBuilder
    var i = 0
    def at(ss: List[String]): Option[String] = ss.find(text.startsWith(_, i))
    def line_start: Boolean = i == 0 || text(i - 1) == '\n'

    def balanced(opening: List[String], closing: List[String]): Int = {
      var j = i
      var depth = 0
      while (j < text.length && (depth > 0 || j == i)) {
        opening.find(text.startsWith(_, j)).map(s => { depth += 1; j += s.length })
          .orElse(closing.find(text.startsWith(_, j)).map(s => { depth -= 1; j += s.length }))
          .getOrElse(j += 1)
      }
      j
    }
    def string_end: Int = {
      var j = i + 1
      while (j < text.length && text(j) != '"') j += (if (text(j) == '\\') 2 else 1)
      j + 1 min text.length
    }
    def keep(j: Int): Unit = { out ++= text.substring(i, j); i = j }
    def blank(j: Int): Unit = { out ++= text.substring(i, j).map(c => if (c == '\n') c else ' '); i = j }

    /* a document command or \<comment> with its cartouche */
    def informal: Option[Int] = {
      val rest = text.subSequence(i, text.length)
      val doc = if (line_start) document.findPrefixMatchOf(rest) else None
      val com = if (text.startsWith("\\<comment>", i)) comment.findPrefixMatchOf(rest) else None
      (doc orElse com).map(i + _.end).filter(j => opens.exists(text.startsWith(_, j))).map { j =>
        val k = i
        i = j
        val end = balanced(opens, closes)
        i = k
        end
      }
    }

    while (i < text.length) {
      informal match {
        case Some(j) => blank(j)
        case None =>
          if (text.startsWith("(*", i)) blank(balanced(List("(*"), List("*)")))
          else if (text(i) == '"') keep(string_end)
          else if (at(opens).isDefined) keep(balanced(opens, closes))
          else keep(i + 1)
      }
    }
    out.toString
  }


  /* whole word, or qualified name ending in it */
  def words(names: List[String]): Option[Regex] =
    if (names.isEmpty) None
    else Some(names.distinct.map(Regex.quote).mkString("(?<![\\w'])(", "|", ")(?![\\w'])").r)

  def find(texts: List[String], regex: Regex): Option[String] =
    texts.iterator.flatMap(regex.findFirstIn(_)).nextOption()

  /* command at line start up to the next; enough for a command's own text */
  val command_start: Regex =
    ("(?m)^\\s*(lemma|theorem|corollary|proposition|definition|abbreviation|fun|function|primrec|" +
      "datatype|codatatype|record|termination|inductive|inductive_set|type_synonym|typedef|" +
      "instantiation|instance|locale|context|section|subsection|subsubsection|text|declare|lemmas|" +
      "value|export_code|consts|end|ML|notation|lift_definition|primcorec|corec|fun_cases)\\b").r

  def commands(texts: List[String], names: Set[String]): List[String] =
    for {
      text <- texts
      starts = command_start.findAllMatchIn(text).toList
      (m, next) <- starts.zip(starts.drop(1).map(_.start) :+ text.length)
      if names(m.group(1))
    } yield text.substring(m.start, next)
}
