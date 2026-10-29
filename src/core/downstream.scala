/* The texts that may use what a theory defines: later theories of the session and of sessions
   built on it, with comments blanked, and searches for names in them. */

package isabelle.isabelle_linter

import isabelle._

import scala.util.matching.Regex


/* A theory's own text and the later texts, without comments, read only when a lint needs them. */
final class Downstream(own: () => String, read: () => List[String]) {
  lazy val theory: String = own()
  lazy val texts: List[String] = read()
}


object Downstream {
  val none: Downstream = new Downstream(() => "", () => Nil)

  /* For each theory: the texts of theories that import it and of sessions built on the session.
     A superset is safe, as more text can only make a lint keep more. */
  def make(structure: Sessions.Structure, session: String, own: List[Path],
      snapshots: Map[Document.Node.Name, Document.Snapshot]): Document.Node.Name => Downstream = {
    lazy val sessions = session_texts(structure, session, own)
    val imports = snapshots.map({ case (name, s) => name -> s.node.thy.imports.map(_._1) })
    def text(name: Document.Node.Name): String = formal(snapshots(name).node.source)
    name => new Downstream(() => text(name), () => importers(imports, name).map(text) ::: sessions)
  }

  def importers(imports: Map[Document.Node.Name, List[Document.Node.Name]],
      name: Document.Node.Name): List[Document.Node.Name] = {
    @scala.annotation.tailrec
    def close(found: Set[Document.Node.Name]): Set[Document.Node.Name] = {
      val more = imports.collect({ case (thy, imported) if !found(thy) && imported.exists(found) => thy }).toSet
      if (more.isEmpty) found else close(found ++ more)
    }
    (close(Set(name)) - name).toList
  }

  /* The session's own theories are left out, as their imports say which come later. */
  def session_texts(structure: Sessions.Structure, session: String, own: List[Path]): List[String] = {
    val later = structure.build_descendants(List(session)).filterNot(_ == session)
    val skip = own.map(_.canonical).toSet
    val files =
      later.map(structure(_).dir.canonical).distinct
        .flatMap(dir => File.find_files(dir, _.file_name.endsWith(".thy")))
    files.map(_.canonical).distinct.filterNot(skip).map(f => formal(File.read(f)))
  }


  /* Comments and document text are blanked, keeping offsets: a name there uses nothing. */

  private val opens = List("\\<open>", "\u2039")
  private val closes = List("\\<close>", "\u203a")
  private val document = "(?m)\\A[ \\t]*(chapter|section|subsection|subsubsection|paragraph|text|txt|text_raw)\\s*".r
  private val comment = "\\A\\\\<comment>\\s*".r

  def formal(text: String): String = {
    val out = new StringBuilder
    var i = 0
    def line_start: Boolean = i == 0 || text(i - 1) == '\n'

    /* The end of the nested group that starts at from. */
    def balanced(from: Int, opening: List[String], closing: List[String]): Int = {
      var j = from
      var depth = 0
      while (j < text.length && (depth > 0 || j == from)) {
        (opening.find(text.startsWith(_, j)), closing.find(text.startsWith(_, j))) match {
          case (Some(open), _) => depth += 1; j += open.length
          case (None, Some(close)) => depth -= 1; j += close.length
          case (None, None) => j += 1
        }
      }
      j
    }
    def string_end: Int = {
      var j = i + 1
      while (j < text.length && text(j) != '"') j += (if (text(j) == '\\') 2 else 1)
      j + 1 min text.length
    }
    def keep(j: Int): Unit = { out ++= text.substring(i, j).nn; i = j }
    def blank(j: Int): Unit = { out ++= text.substring(i, j).nn.map(c => if (c == '\n') c else ' '); i = j }

    /* The end of a document command or \<comment> with its cartouche, if one starts here. */
    def informal: Option[Int] = {
      val rest = text.subSequence(i, text.length).nn
      val doc = if (line_start) document.findPrefixMatchOf(rest) else None
      val com = if (text.startsWith("\\<comment>", i)) comment.findPrefixMatchOf(rest) else None
      (doc orElse com).map(i + _.end).filter(j => opens.exists(text.startsWith(_, j)))
        .map(balanced(_, opens, closes))
    }

    while (i < text.length) {
      informal match {
        case Some(j) => blank(j)
        case None =>
          if (text.startsWith("(*", i)) blank(balanced(i, List("(*"), List("*)")))
          else if (text(i) == '"') keep(string_end)
          else if (opens.exists(text.startsWith(_, i))) keep(balanced(i, opens, closes))
          else keep(i + 1)
      }
    }
    out.toString
  }


  /* Any of names as a whole word, or as the end of a qualified name. */
  def words(names: List[String]): Option[Regex] =
    if (names.isEmpty) None
    else Some(names.distinct.map(Regex.quote).mkString("(?<![\\w'])(", "|", ")(?![\\w'])").r)

  def find(texts: List[String], regex: Regex): Option[String] =
    texts.iterator.flatMap(regex.findFirstIn(_)).nextOption()

  /* A command from its keyword at the start of a line up to the next; enough for its own text. */
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
    } yield text.substring(m.start, next).nn
}
