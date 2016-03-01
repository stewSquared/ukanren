/**
  * From the paper by Jason Hemann
  *  
  * I've tried to stay true to the names in the original, sometimes
  * being more explicit or tweaking to avoid naming clashes.
  * TODO: Rename everything to avoid `$` symbol.
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

  sealed trait LList {
    def ::(h: Term) = LCons(h, this)
  }

  case class LCons(head: Term, tail: LList) extends LList {
    override def toString = head+"::"+tail
  }

  case class LVar(index: Int) extends LList {
    override def toString = "_"+index
  }

  protected def lcons(head: Term, tail: Term): Term = tail match {
    case s: Seq[_] => head +: s
    case l: LList => LCons(head, l)
  }

  type Term = Any
  type Substitution = Map[LVar, Term]
  case class State(substitution: Substitution, counter: Int)
  type Goal = State => $tream[State]

  val succeed: Goal = state => unit(state)
  val fail: Goal = state => mzero
  val emptyState = State(Map.empty, 0)

  protected def callFresh(f: LVar => Goal): Goal = {
    case State(s,c) => f(LVar(c))(State(s, c+1))
  }

  def unit(state: State): $tream[State] = $Cons(state, $Nil)
  val mzero: $tream[State] = $Nil

  def unify(u: Term, v: Term): Goal = { case State(s, c) =>
    unify(u, v, s).map(newSub => unit(State(newSub, c))).getOrElse(mzero)
  }

  protected def unify(u: Term, v: Term, s: Substitution): Option[Substitution] =
    (walk(u, s), walk(v, s)) match {
      case (u, v) if u == v => Some(s)
      case (u: LVar, v) => Some(s + (u -> v))
      case (u, v: LVar) => Some(s + (v -> u))
      case (us: Seq[_], vs: LCons) if us.nonEmpty =>
        unify(us.head, vs.head, s).flatMap(unify(us.tail, vs.tail, _))
      case (us: LCons, vs: Seq[_]) if vs.nonEmpty =>
        unify(us.head, vs.head, s).flatMap(unify(us.tail, vs.tail, _))
      case (us: LCons, vs: LCons) =>
        unify(us.head, vs.head, s).flatMap(unify(us.tail, vs.tail, _))
      case (us: Seq[_], vs: Seq[_]) if us.nonEmpty && vs.nonEmpty =>
        unify(us.head, vs.head, s).flatMap(unify(us.tail, vs.tail, _))
      case _ => None
    }

  def walk(u: Term, s: Substitution): Term = u match {
    case v: LVar => s.get(v).fold(u)(walk(_, s))
    case _ => u
  }

  // The returned result is alway a fresh LVar or ground value
  // ie., a returned LVar is never bound
  // TODO: This property should be tested.
  def walk_*(v: Term, s: Substitution): Term = walk(v, s) match {
    case vs: Seq[_] => vs.map(walk_*(_, s))
    case LCons(h, t) => lcons(walk_*(h, s), walk_*(t, s)) //Document: Why not construct LCons
    case v => v
  }

  protected def disj(g1: => Goal, g2: => Goal): Goal = state => mplus(g1(state), g2(state))

  def mplus($1: $tream[State], $2: $tream[State]): $tream[State] = $1 match {
    case $Nil => $2
    case ImmatureStream(imm) => immature(mplus($2, imm()))
    case $Cons(h, t) => $Cons(h, mplus($2, t))
  }

  protected def conj(g1: => Goal, g2: => Goal): Goal = state => bind(g1(state), g2)

  def bind($: $tream[State], g: Goal): $tream[State] = $ match {
    case $Nil => mzero
    case ImmatureStream(imm) => immature(bind(imm(), g))
    case $Cons(h, t) => mplus(g(h), bind(t, g))
  }

  protected def immature[T]($: => $tream[T]) = ImmatureStream(() => $)

  // Inverse eta delay. Pronounced "Snooze"
  // TODO? Use the type system to decide when to do this implicitly
  protected def Zzz(g: Goal): State => ImmatureStream[State] = state => immature(g(state))

  def pull[T]($: $tream[T]): Stream[T] = $ match {
    case $Nil => Stream.empty
    case ImmatureStream(imm) => pull(imm())
    case $Cons(h, t) => h #:: pull(t)
  }
}

trait UserInterface extends Core {self: Reification =>
  implicit class ByName[T](value: => T) {
    def apply(): T = value
  }

  implicit class TermOps(t: Term) {
    def ===(t2: Term): Goal = unify(t, t2)
  }

  implicit class GoalOps(g: Goal) {
    def ||(g2: Goal): Goal = disj(Zzz(g), Zzz(g2))
    def &&(g2: Goal): Goal = conj(Zzz(g), Zzz(g2))
  }

  def any(goals: ByName[Goal]*): Goal =
    goals.headOption.fold(fail)(head =>
      disj(Zzz(head()), any(goals.tail: _*)))

  def all(goals: ByName[Goal]*): Goal =
    goals.headOption.fold(succeed)(head =>
      conj(Zzz(head()), all(goals.tail: _*)))

  def exists(f: () => Goal): Goal = f()
  def exists(f: (LVar) => Goal): Goal = callFresh(f) 
  def exists(f: (LVar, LVar) => Goal): Goal = callFresh(q => exists(f(q,_)))
  def exists(f: (LVar, LVar, LVar) => Goal): Goal = callFresh(q => exists(f(q,_,_)))
  def exists(f: (LVar, LVar, LVar, LVar) => Goal): Goal = callFresh(q => exists(f(q,_,_,_)))
  def exists(f: (LVar, LVar, LVar, LVar, LVar) => Goal): Goal = callFresh(q => exists(f(q,_,_,_,_)))
  def exists(f: (LVar, LVar, LVar, LVar, LVar, LVar) => Goal): Goal = callFresh(q => exists(f(q,_,_,_,_,_)))

  protected def reify(lvars: LVar*)(state: State): Seq[Term] = {
    def uniqueInOrder[T](items: Seq[T]): Seq[T] = items
      .zipWithIndex
      .groupBy(_._1)
      .toList
      .sortBy{case (item, indices) => indices.map(_._2).min}
      .map(_._1)

    def freshIndices(term: Term): Seq[Int] = term match {
      case LVar(index) => Seq(index)
      case LCons(h, t) => freshIndices(h) ++ freshIndices(t)
      case vs: Seq[_] => vs.flatMap(freshIndices)
      case _ => Seq()
    }

    val walkedValues = lvars.map(walk_*(_, state.substitution))
    val newId: Map[Int, Int] = uniqueInOrder(walkedValues.flatMap(freshIndices))
      .zipWithIndex.toMap

    // ideally, reindexVars would preserve type info
    def reindexVars(term: Term): Term = term match {
      case LVar(id) => LVar(newId(id))
      case LCons(h, t) => lcons(reindexVars(h), reindexVars(t))
      case vs: Seq[_] => vs.map(reindexVars)
      case x => x
    }

    walkedValues.map(reindexVars)
  }
}

trait ListRelations extends UserInterface { self: Reification =>
  def conso(head: Term, tail: Term, out: Term): Goal = lcons(head, tail) === out
  
  def heado(head: Term, all: Term): Goal =
    exists(tail => (conso(head, tail, all)))

  def tailo(tail: Term, all: Term): Goal =
    exists(head => (conso(head, tail, all)))

  def emptyo(l: Term): Goal = l === Nil

  def listo(l: Term): Goal = any(
    emptyo(l),
    exists((h, t) =>
      conso(h, t, l) && listo(t)))

  def appendo(a: Term, b: Term, result: Term): Goal = any(
    (emptyo(a) && (result === b)),
    exists((h, t, tb) => all(
      conso(h, t, a),
      conso(h, tb, result),
      appendo(t, b, tb))))

  def membero(elem: Term, list: Term): Goal =
    exists((head, tail) => all(
      conso(head, tail, list),
      (elem === head) || membero(elem, tail)))

  def rembero(elem: Term, list: Term, rest: Term): Goal = any(
    conso(elem, rest, list),
    exists((h, t, recur) => all(
      conso(h, t, list),
      conso(h, recur, rest),
      rembero(elem, t, recur))))

  // Can SO if lists are not ground and conj'd with something
  def permuto(listX: Term, listY: Term): Goal =
    sameLengtho(listX, listY) && any(
      emptyo(listX) && emptyo(listY),
      exists((x, xs, ys) => all(
        conso(x, xs, listX),
        rembero(x, listY, ys),
        permuto(xs, ys))))

  def sameLengtho(xlist: Term, ylist: Term): Goal = any(
    emptyo(xlist) && emptyo(ylist),
    exists((xtail, ytail) => all(
      tailo(xtail, xlist),
      tailo(ytail, ylist),
      sameLengtho(xtail, ytail))))

  def samePoso(xlist: Term, ylist: Term, x: Term, y: Term): Goal = any(
    heado(x, xlist) && heado(y, ylist),
    exists((xtail, ytail) => all(
      tailo(xtail, xlist),
      tailo(ytail, ylist),
      samePoso(xtail, ytail, x, y))))
}

trait Reification extends UserInterface

trait StringReification extends Reification {
  def reifyS(lvars: LVar*)(state: State): String =
    reify(lvars: _*)(state).mkString("(", ", ", ")")

  def run(f: () => Goal): Stream[String] =
    pull(exists(f)(emptyState)).map(reifyS())

  def run(f: (LVar) => Goal): Stream[String] =
    pull(exists(f)(emptyState)).map(reifyS(LVar(0)))

  def run(f: (LVar, LVar) => Goal): Stream[String] =
    pull(exists(f)(emptyState)).map(reifyS(LVar(0), LVar(1)))

  def run(f: (LVar, LVar, LVar) => Goal): Stream[String] =
    pull(exists(f)(emptyState)).map(reifyS(LVar(0), LVar(1), LVar(2)))
}

trait ConcreteReification extends Reification {
  def reifyC[T](lvar: LVar)(state: State): Either[LVar, T] =
    reify(lvar)(state).head match {
      case l: LVar => Left(l)
      case t: Term => Right(t.asInstanceOf[T])
    }

  def reifyCNested[F[_] <: Seq[_],T](lvar: LVar)(state: State): Either[LVar, F[Either[LVar, T]]] = {
    def toEitherLVarT(t: Any): Either[LVar, T] = t match {
        case l: LVar => Left(l)
        case t: Term => Right(t.asInstanceOf[T])
    }

    reify(lvar)(state).head match {
      case l: LVar => Left(l)
      case ls: F[_] => Right(
        ls.map(t => toEitherLVarT(t))
          .asInstanceOf[F[Either[LVar, T]]])
    }
  }

  def run[T](f: (LVar) => Goal): Stream[Either[LVar, T]] =
    pull(exists(f)(emptyState)).map(reifyC[T](LVar(0)))

  def run[F[_] <: Seq[_], T](f: (LVar) => Goal)(implicit d: DummyImplicit)
      : Stream[Either[LVar, F[Either[LVar, T]]]] =
    pull(exists(f)(emptyState)).map(reifyCNested[F, T](LVar(0)))
}

trait DynamicReification extends Reification with ListRelations {
  val Seq(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9) = 0 to 9 map LVar

  def reifyD()(state: State): Unit = ()

  def reifyD(q: LVar)(state: State): Term =
    reify(q)(state).head

  def reifyD(q: LVar, r: LVar)(state: State): (Term, Term) =
    reify(q, r)(state) match { case Seq(a, b) => (a, b) }

  def reifyD(q: LVar, r: LVar, s: LVar)(state: State): (Term, Term, Term) =
    reify(q, r, s)(state) match { case Seq(a, b, c) => (a, b, c) }

  def reifyD(q: LVar, r: LVar, s: LVar, t: LVar)(state: State): (Term, Term, Term, Term) =
    reify(q, r, s, t)(state) match { case Seq(a, b, c, d) => (a, b, c, d) }

  def reifyD(q: LVar, r: LVar, s: LVar, t: LVar, u: LVar)(state: State) =
    reify(q, r, s, t, u)(state) match { case Seq(a, b, c, d, e) => (a, b, c, d, e) }

  def reifyD(q: LVar, r: LVar, s: LVar, t: LVar, u: LVar, v: LVar)(state: State) =
    reify(q, r, s, t, u, v)(state) match { case Seq(a, b, c, d, e, f) => (a, b, c, d, e, f) }

  def run(f: () => Goal): Stream[Term] =
    pull(exists(f)(emptyState)).map(reifyD())

  def run(f: (LVar) => Goal): Stream[Term] =
    pull(exists(f)(emptyState)).map(reifyD(_0))

  def run(f: (LVar, LVar) => Goal): Stream[Term] =
    pull(exists(f)(emptyState)).map(reifyD(_0, _1))

  def run(f: (LVar, LVar, LVar) => Goal): Stream[Term] =
    pull(exists(f)(emptyState)).map(reifyD(_0, _1, _2))

  def run(f: (LVar, LVar, LVar, LVar) => Goal): Stream[Term] =
    pull(exists(f)(emptyState)).map(reifyD(_0, _1, _2, _3))

  def run(f: (LVar, LVar, LVar, LVar, LVar) => Goal): Stream[Term] =
    pull(exists(f)(emptyState)).map(reifyD(_0, _1, _2, _3, _4))

  def run(f: (LVar, LVar, LVar, LVar, LVar, LVar) => Goal): Stream[Term] =
    pull(exists(f)(emptyState)).map(reifyD(_0, _1, _2, _3, _4, _5))
}

object ukanrenString extends Core with StringReification
object ukanrenConcrete extends Core with ConcreteReification
object ukanren extends Core with DynamicReification
