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
  sealed trait $tream[+T]
  case class $Cons[+T](head: T, tail: $tream[T]) extends $tream[T]
  case object $Nil extends $tream[Nothing]

  type Term = Any
  case class LVar(index: Int)
  type Substitution = Map[LVar, Term]
  case class State(substitution: Substitution, counter: Int)
  type Goal = State => $tream[State]

  // Four primitive goal constructors
  def callFresh(f: LVar => Goal): Goal
  def ===(u: Term, v: Term): Goal
  def disj(g1: Goal, g2: Goal): Goal
  def conj(g1: Goal, g2: Goal): Goal

  def emptyState = State(Map.empty, 0)

  // Search for a variable's value in a substitution
  def walk(u: Term, s: Substitution): Term = u match {
    case v: LVar => s.get(v).fold(u)(walk(_, s))
    case _ => u
  }

  def extS(x: LVar, v: Term, s: Substitution): Substitution = s + (x -> v)
}

object ukanren extends MicroKanren {
  def callFresh(f: LVar => Goal): Goal = {
    case State(s,c) => f(LVar(c))(State(s, c+1))
  }

  def ===(u: Term, v: Term): Goal = { case State(s, c) =>
    unify(u, v, s).map(newSub => unit(State(newSub, c))).getOrElse(mzero)
  }

  def unit(state: State): $tream[State] = $Cons(state, $Nil)
  def mzero: $tream[State] = $Nil

  def disj(g1: Goal, g2: Goal): Goal = state => mplus(g1(state), g2(state))
  def conj(g1: Goal, g2: Goal): Goal = state => bind(g1(state), g2)

  def unify(u: Term, v: Term, s: Substitution): Option[Substitution] =
    (walk(u, s), walk(v, s)) match {
      case (u, v) if u == v => Some(s)
      case (u: LVar, v) => Some(extS(u, v, s))
      case (u, v: LVar) => Some(extS(v, u, s))
      case (us: Seq[_], vs: Seq[_]) =>
        (us zip vs).foldLeft(Option(s)){case (acc, (u, v)) =>
          acc.flatMap(s => unify(u, v, s))
        }
      case _ => None
    }

  def mplus($1: $tream[State], $2: $tream[State]): $tream[State] = $1 match {
    case $Nil => $2
    case $Cons(h, t) => $Cons(h, mplus(t, $2))
  }
  def bind($: $tream[State], g: Goal): $tream[State] = $ match {
    case $Nil => mzero
    case $Cons(h, t) => mplus(g(h), bind(t, g))
  }
}
