/**
  * From the paper by Jason Hemann
  *  
  * I've tried to stay true to the names in the original, sometimes
  * being more explicit or tweaking to avoid naming clashes.
  *  
  * Departures from the paper:
  * A substitution is represented by a Map rather than an association list.
  *
  */

trait MicroKanren {
  case class $tream[T](ts: T*)
  // A State is a pair of a substitution and nonNegative Integer
  case class State(substitution: Map[LVar, Any], counter: Int)
  case class LVar(index: Int)

  type Goal = State => $tream[State]

  // Four primitive goal constructors
  def callFresh(f: LVar => Goal): Goal
  def ===(u: Any, v: Any): Goal
  def disj(g1: Goal, g2: Goal): Goal
  def conj(g1: Goal, g2: Goal): Goal

  def emptyState = State(Map.empty, 0)
}

object ukanren extends MicroKanren {
  def callFresh(f: LVar => Goal): Goal = ???
  def ===(u: Any, v: Any): Goal = ???
  def disj(g1: Goal, g2: Goal): Goal = ???
  def conj(g1: Goal, g2: Goal): Goal = ???
}
