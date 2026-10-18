/* unused_imports: the theory import graph, and what removing imports does to it */

package isabelle.isabelle_linter

import isabelle._

import scala.collection.mutable


/* each theory's imports as written, by long name; an edge is a theory and one of its imports */
final class Theory_Graph(val imports: Map[String, List[String]]) {
  private val cache = mutable.Map.empty[String, Set[String]]

  def imports_of(thy: String): List[String] = imports.getOrElse(thy, Nil)

  /* the theories that thy imports, directly or not */
  def ancestors(thy: String): Set[String] =
    cache.get(thy) match {
      case Some(as) => as
      case None =>
        val as = imports_of(thy).foldLeft(Set.empty[String])((s, a) => s + a ++ ancestors(a))
        cache(thy) = as
        as
    }

  def without(edges: Set[(String, String)]): Theory_Graph =
    new Theory_Graph(imports.map({ case (t, as) => t -> as.filterNot(a => edges((t, a))) }))

  /* the imports of thy that another of its imports already brings in */
  def redundant(thy: String): List[String] = {
    val as = imports_of(thy)
    as.filter(a => as.exists(b => b != a && ancestors(b)(a)))
  }

  /* the theories of nodes whose ancestors differ in other */
  def changed(other: Theory_Graph, nodes: Iterable[String]): Set[String] =
    nodes.filter(t => ancestors(t) != other.ancestors(t)).toSet

  /* the heaviest chain of imports within nodes: its weight and its theories, from the top */
  def critical_path(nodes: Set[String], weight: String => Double): (Double, List[String]) = {
    val memo = mutable.Map.empty[String, (Double, List[String])]
    def path(t: String): (Double, List[String]) =
      memo.get(t) match {
        case Some(p) => p
        case None =>
          val below = imports_of(t).filter(nodes).map(path)
          val (w, ts) = if (below.isEmpty) (0.0, Nil) else below.maxBy(_._1)
          val p = (w + weight(t), t :: ts)
          memo(t) = p
          p
      }
    if (nodes.isEmpty) (0.0, Nil) else nodes.toList.sorted.map(path).maxBy(_._1)
  }
}
