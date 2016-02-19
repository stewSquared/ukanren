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

trait Core {
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

  def unify(u: Term, v: Term): Goal = { case State(s, c) =>
    unify(u, v, s).map(newSub => unit(State(newSub, c))).getOrElse(mzero)
  }
  def ===(u: Term, v: Term) = unify(u,v)

  def unit(state: State): $tream[State] = $Cons(state, $Nil)

  val mzero: $tream[State] = $Nil

  val succeed: Goal = state => unit(state)

  val fail: Goal = state => mzero

  val emptyState = State(Map.empty, 0)

  def unify(u: Term, v: Term, s: Substitution): Option[Substitution] =
    (walk(u, s), walk(v, s)) match {
      case (u, v) if u == v => Some(s)
      case (u: LVar, v) => Some(s + (u -> v))
      case (u, v: LVar) => Some(s + (v -> u))
      case (us: Seq[_], vs: Seq[_]) if us.length == vs.length =>
        (us zip vs).foldLeft(Option(s)){ case (acc, (u, v)) =>
          acc.flatMap(s => unify(u, v, s))
        }
      case _ => None
    }

  def walk(u: Term, s: Substitution): Term = u match {
    case v: LVar => s.get(v).fold(u)(walk(_, s))
    case _ => u
  }

  def disj(g1: => Goal, g2: => Goal): Goal = state => mplus(g1(state), g2(state))

  def mplus($1: $tream[State], $2: $tream[State]): $tream[State] = $1 match {
    case $Nil => $2
    case ImmatureStream(imm) => immature(mplus($2, imm()))
    case $Cons(h, t) => $Cons(h, mplus($2, t))
  }

  def conj(g1: => Goal, g2: => Goal): Goal = state => bind(g1(state), g2)

  def bind($: $tream[State], g: Goal): $tream[State] = $ match {
    case $Nil => mzero
    case ImmatureStream(imm) => immature(bind(imm(), g))
    case $Cons(h, t) => mplus(g(h), bind(t, g))
  }

  def immature[T]($: => $tream[T]) = ImmatureStream(() => $)

  // Inverse eta delay. Pronounced "Snooze"
  // TODO? Use the type system to decide when to do this implicitly
  def Zzz(g: Goal): State => ImmatureStream[State] = state => immature(g(state))

  def pull[T]($: $tream[T]): Stream[T] = $ match {
    case $Nil => Stream.empty
    case ImmatureStream(imm) => pull(imm())
    case $Cons(h, t) => h #:: pull(t)
  }
}

trait Interface extends Core {
  implicit class ByName[T](value: => T) {
    def apply(): T = value
  }

  implicit class TermOps(t: Term) {
    def ===(t2: Term): Goal = unify(t, t2)
  }

  implicit class GoalOps(g: Goal) {
    def |||(g2: Goal): Goal = disj(Zzz(g), Zzz(g2))
    def &&&(g2: Goal): Goal = conj(Zzz(g), Zzz(g2))
  }

  def disj_*(goals: ByName[Goal]*): Goal =
    goals.headOption.fold(fail)(head =>
      disj(Zzz(head()), disj_*(goals.tail: _*)))

  def conj_*(goals: ByName[Goal]*): Goal =
    goals.headOption.fold(succeed)(head =>
      conj(Zzz(head()), conj_*(goals.tail: _*)))

  def fresh(f: () => Goal): Goal = f()

  def fresh(f: (LVar) => Goal): Goal =
    callFresh(f)

  def fresh(f: (LVar, LVar) => Goal): Goal =
    callFresh(q =>
      callFresh(r => f(q,r)))

  // TODO: This is mechanical enough to be a macro
  def fresh(f: (LVar, LVar, LVar) => Goal): Goal =
    callFresh(q =>
      callFresh(r =>
        callFresh(s => f(q,r,s))))

  def reify(lvars: LVar*)(state: State): String = {
    def freshIndices(terms: Seq[Term]): Seq[Int] = terms.flatMap{
      case LVar(index) => Seq(index)
      case vs: Seq[_] => freshIndices(vs)
      case _ => Seq()
    }

    val values = lvars.map(walk(_, state.substitution))

    val (reindexed: Map[Int, Int], _) = freshIndices(values)
      .foldLeft[(Map[Int, Int], Int)](Map.empty, 0) {
      case ((indices, count), lvar) =>
        if (indices contains lvar) (indices, count)
        else (indices + (lvar -> count), count + 1)
    }

    def stringify(terms: Seq[Term]): Seq[String] = terms.map {
      case LVar(index) => "_" + reindexed(index)
      case vs: Seq[_] => stringify(vs).toString
      case value => value.toString
    }

    stringify(values).mkString("(", ", ", ")")
  }

  def run_*(f: () => Goal): Stream[String] =
    pull(fresh(f)(emptyState)).map(reify())

  def run_*(f: (LVar) => Goal): Stream[String] =
    pull(fresh(f)(emptyState)).map(reify(LVar(0)))

  def run_*(f: (LVar, LVar) => Goal): Stream[String] =
    pull(fresh(f)(emptyState)).map(reify(LVar(0), LVar(1)))

  def run_*(f: (LVar, LVar, LVar) => Goal): Stream[String] =
    pull(fresh(f)(emptyState)).map(reify(LVar(0), LVar(1), LVar(2)))
}

object ukanren extends Interface with Core
