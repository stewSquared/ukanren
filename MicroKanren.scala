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
  case class ImmatureStream[+T](proc: () => $tream[T]) extends $tream[T]
  case object $Nil extends $tream[Nothing]

  case class LVar(index: Int)
  type Term = Any
  type Substitution = Map[LVar, Term]
  case class State(substitution: Substitution, counter: Int)
  type Goal = State => $tream[State]

  def callFresh(f: LVar => Goal): Goal = {
    case State(s,c) => f(LVar(c))(State(s, c+1))
  }

  def ===(u: Term, v: Term): Goal = { case State(s, c) =>
    unify(u, v, s).map(newSub => unit(State(newSub, c))).getOrElse(mzero)
  }

  def unit(state: State): $tream[State] = $Cons(state, $Nil)

  val mzero: $tream[State] = $Nil

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

  def walk(u: Term, s: Substitution): Term = u match {
    case v: LVar => s.get(v).fold(u)(walk(_, s))
    case _ => u
  }

  def extS(x: LVar, v: Term, s: Substitution): Substitution = s + (x -> v)

  def disj(g1: Goal, g2: => Goal): Goal = state => mplus(g1(state), g2(state))

  def mplus($1: $tream[State], $2: $tream[State]): $tream[State] = $1 match {
    case $Nil => $2
    case ImmatureStream(imm) => immature(mplus($2, imm()))
    case $Cons(h, t) => $Cons(h, mplus(t, $2))
  }

  def conj(g1: Goal, g2: => Goal): Goal = state => bind(g1(state), g2)

  def bind($: $tream[State], g: Goal): $tream[State] = $ match {
    case $Nil => mzero
    case ImmatureStream(imm) => immature(bind(imm(), g))
    case $Cons(h, t) => mplus(g(h), bind(t, g))
  }

  def immature[T]($: => $tream[T]) = ImmatureStream(() => $)
}

object ukanren extends MicroKanren {
  val emptyState = State(Map.empty, 0)

  // Inverse eta delay. Pronounced "Snooze"
  // TODO? Use the type system to decide when to do this implicitly
  def Zzz(g: Goal): State => ImmatureStream[State] = state => immature(g(state))

  def pull[T]($: $tream[T]): Stream[T] = $ match {
    case $Nil => Stream.empty
    case ImmatureStream(imm) => pull(imm())
    case $Cons(h, t) => h #:: pull(t)
  }
}
