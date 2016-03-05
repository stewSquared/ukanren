import ukanren._

object examples {
  def basics = List(
    run(q => (q === 3)), // Stream(3)
    run(q => (q === 3) || (q === 4)), // Stream(3,4)
    run(q => (q === 3) && (q === 4)), // Stream()
    run(q => fail), // Stream()
    run(q => succeed), // Stream(_0)
    run((q, r) => succeed), // Stream((_0,_1))
    run((q, r) => q === r), // Stream((_0,_0))
    run((q, r, s) => all((q === 1), (r === 2), (s === 3))), // Stream(1, 2, 3)
    run((q, r, s) => any((q === 'Q'), (r === 'R'), (s === 'S')))
      //Stream((Q,_0,_1), (_0,R,_1), (_0,_1,S))
  )

  def append[T](la: List[T], lb: List[T]): List[T] =
    if (la.isEmpty) lb
    else {
      val a::as = la
      val rec = append(as, lb)
      a::rec
    }

  def appendo(la: Term, lb: Term, out: Term): Goal = any(
    (emptyo(la) && (out === lb)),
    exists((a, as, rec) => all(
      a::as === la,
      appendo(as, lb, rec),
      a::rec === out)))

  val start = (1 to 5).toList
  val end = (6 to 10).toList
  val full = (1 to 10).toList

  def functionalAppend = append(start, end) // == full

  def appendoForward = run(appendo(start, end, _)) // == Stream(full)

  def appendoBackward = run(appendo(_, _, full))
  /* Stream(
    (List(),List(1, 2, 3, 4, 5, 6, 7, 8, 9, 10)),
    (List(1),List(2, 3, 4, 5, 6, 7, 8, 9, 10)),
    (List(1, 2),List(3, 4, 5, 6, 7, 8, 9, 10)),
    (List(1, 2, 3),List(4, 5, 6, 7, 8, 9, 10)),
    (List(1, 2, 3, 4),List(5, 6, 7, 8, 9, 10)),
    (List(1, 2, 3, 4, 5),List(6, 7, 8, 9, 10)),
    (List(1, 2, 3, 4, 5, 6),List(7, 8, 9, 10)),
    (List(1, 2, 3, 4, 5, 6, 7),List(8, 9, 10)),
    (List(1, 2, 3, 4, 5, 6, 7, 8),List(9, 10)),
    (List(1, 2, 3, 4, 5, 6, 7, 8, 9),List(10)),
    (List(1, 2, 3, 4, 5, 6, 7, 8, 9, 10),List())
  ) */

  def appendoExpanding = run(q =>
    exists(appendo(start, _, q)) && exists(appendo(_, end, q))
  ) take 10
  /* == Stream(
    List(1, 2, 3, 4, 5, 6, 7, 8, 9, 10),
    List(1, 2, 3, 4, 5, _0, 6, 7, 8, 9, 10),
    List(1, 2, 3, 4, 5, _0, _1, 6, 7, 8, 9, 10),
    List(1, 2, 3, 4, 5, _0, _1, _2, 6, 7, 8, 9, 10),
    List(1, 2, 3, 4, 5, _0, _1, _2, _3, 6, 7, 8, 9, 10),
    List(1, 2, 3, 4, 5, _0, _1, _2, _3, _4, 6, 7, 8, 9, 10),
    List(1, 2, 3, 4, 5, _0, _1, _2, _3, _4, _5, 6, 7, 8, 9, 10),
    List(1, 2, 3, 4, 5, _0, _1, _2, _3, _4, _5, _6, 6, 7, 8, 9, 10),
    List(1, 2, 3, 4, 5, _0, _1, _2, _3, _4, _5, _6, _7, 6, 7, 8, 9, 10),
    List(1, 2, 3, 4, 5, _0, _1, _2, _3, _4, _5, _6, _7, _8, 6, 7, 8, 9, 10)) */
}

object Intro extends App {
  val fathers = List("Moore", "Downing", "Hall", "Barnacle", "Parker")

  def ans = run((lornaFather, daughters, yachts) => {
    def sires(f: Term, d: Term): Goal = samePoso(fathers, daughters, f, d)
    def owns(f: Term, y: Term): Goal = samePoso(fathers, yachts, f, y)

    all(
      sires("Moore", "Mary"),
      sameLengtho(fathers, yachts),
      sameLengtho(fathers, daughters),
      owns("Barnacle", "Gabrielle"),
      owns("Moore", "Lorna"),
      owns("Hall", "Rosalind"),
      owns("Downing", "Melissa"),
      sires("Barnacle", "Melissa"),
      exists((gf, pd) => all(
        sires(gf, "Gabrielle"),
        sires("Parker", pd),
        owns(gf, pd))),
      permuto(yachts, daughters),
      sires(lornaFather, "Lorna"))
  })

  def display(ans: Any): Unit = ans match {
    case (lornaFather, daughters, yachts) => {
      println(f"$lornaFather%-9s$daughters%s")
      println(f"         $yachts%s")
    }
    case ans => println(ans)
  }

  ans take 10 foreach display
}
