/* The theory import graph of unused_imports, and what removing imports does to it. */

package isabelle.isabelle_linter

import isabelle._

import scala.collection.mutable


/* Each theory's imports as written, by long name; an edge is a theory and one of its imports. */
final class Theory_Graph(val imports: Map[String, List[String]]) {
  private val cache = mutable.Map.empty[String, Set[String]]

  def imports_of(thy: String): List[String] = imports.getOrElse(thy, Nil)

  /* The theories that thy imports, directly or not. */
  def ancestors(thy: String): Set[String] =
    cache.get(thy) match {
      case Some(found) => found
      case None =>
        val found = imports_of(thy).foldLeft(Set.empty[String])((all, imported) => all + imported ++ ancestors(imported))
        cache(thy) = found
        found
    }

  def without(edges: Set[(String, String)]): Theory_Graph =
    new Theory_Graph(imports.map({ case (thy, imported) => thy -> imported.filterNot(i => edges((thy, i))) }))

  /* The imports of thy that another of its imports already brings in. */
  def redundant(thy: String): List[String] = {
    val imported = imports_of(thy)
    imported.filter(theory => imported.exists(other => other != theory && ancestors(other)(theory)))
  }

  /* The theories of nodes whose ancestors differ in other. */
  def changed(other: Theory_Graph, nodes: Iterable[String]): Set[String] =
    nodes.filter(thy => ancestors(thy) != other.ancestors(thy)).toSet

  /* The heaviest chain of imports within nodes: its weight and its theories, from the top. */
  def critical_path(nodes: Set[String], weight: String => Double): (Double, List[String]) = {
    val memo = mutable.Map.empty[String, (Double, List[String])]
    def path(thy: String): (Double, List[String]) =
      memo.get(thy) match {
        case Some(found) => found
        case None =>
          val below = imports_of(thy).filter(nodes).map(path)
          val (below_weight, below_path) = if (below.isEmpty) (0.0, Nil) else below.maxBy(_._1)
          val found = (below_weight + weight(thy), thy :: below_path)
          memo(thy) = found
          found
      }
    if (nodes.isEmpty) (0.0, Nil) else nodes.toList.sorted.map(path).maxBy(_._1)
  }
}
