import utest._
import utest.ExecutionContext.RunNow

object MicroKanrenCoreSuite extends TestSuite with Core {
  val tests = TestSuite {
    def run(g: Goal) = pull(g(emptyState))

    // The following returns a stable substitution. ie., this function
    // is idempotent.  This is a necessary normalization because
    // technically different Substitutions could behave the same way.
    def walked(s: Substitution): Substitution =
      s.keys.map(u => u -> walk_*(u, s)).toMap

    val Seq(_0, _1, _2) = 0 to 2 map LVar

    "example ukanren queries from Hemann Paper"-{
      assert(
        callFresh(q => unify(q, 5))(emptyState) ==
          $Cons(State(Map(LVar(0) -> 5), 1), $Nil))

      def ab: Goal = conj(
        callFresh(a => unify(a,7)),
        callFresh(b => disj(
          unify(b,5),
          unify(b,6))))

      assert(ab(emptyState) ==
        $Cons(State(Map(LVar(0) -> 7, LVar(1) -> 5), 2),
          $Cons(State(Map(LVar(0) -> 7, LVar(1) -> 6), 2), $Nil)))
    }

    "Infinite streams"-{
      def fives(x: LVar): Goal = disj(unify(x, 5), Zzz(fives(x)))
      def fivesLeft(x: LVar): Goal = disj(Zzz(fivesLeft(x)), unify(x, 5))
      def sixes(x: LVar): Goal = disj(unify(x, 6), Zzz(fives(x)))
      def fivesAndSixes = callFresh(x => disj(fives(x), sixes(x)))

      "Infinite disj"-{
        val $Cons(fst, ImmatureStream(imm0)) = callFresh(fives)(emptyState)
        val $Cons(snd, ImmatureStream(imm1)) = imm0()
        val $Cons(trd, ImmatureStream(imm2)) = imm1()
        assert(fst == snd)
        assert(snd == trd)

        assert(pull(callFresh(fives)(emptyState)).take(5).toList ==
          pull(callFresh(fivesLeft)(emptyState)).take(5).toList)
      }

      "Infinite conj"-{
        def recurseRight(x: LVar): Goal = conj(fail, Zzz(recurseRight(x)))
        def recurseLeft(x: LVar): Goal = conj(Zzz(recurseLeft(x)), fail)

        assert(pull(callFresh(recurseRight)(emptyState)).isEmpty)

        // The following causes a StackOverflow. This is difficult to fix.
        // Apparently, fair conjunction is a problem even for core.logic
        //assert(pull(callFresh(recurseLeft)(emptyState)).isEmpty)
      }

      "Interleaving streams"-{
        assert(
          pull(fivesAndSixes(emptyState))
            .take(5).flatMap(_.substitution.values)
            .toSet == Set(5,6))
      }
    }

    "Unification of atoms"-{
      assert(run(callFresh(_ => unify(1, 1))).nonEmpty)
      assert(run(callFresh(_ => unify(0, 1))).isEmpty)
      assert(State(Map(_0 -> 1), 1) == run(callFresh(q => unify(q, 1))).head)
      assert(run(callFresh(q => conj(unify(q, 0), unify(q, 1)))).isEmpty)

      assert(Map(_0 -> 0, _1 -> 0) ==
        walked(run(callFresh(q => callFresh(r =>
          conj(unify(q, r), unify(q, 0))))).head.substitution))
    }

    "Unification of lists"-{
      assert(run(callFresh(_ => unify(List(0), List(0, 1)))).isEmpty)

      assert(State(Map(_0 -> 0), 1) ==
        run(callFresh(q => unify(List(q, 1), List(0, 1)))).head)

      assert(State(Map(_0 -> 0, _1 -> 1), 2) ==
        run(callFresh(q =>
          callFresh(r => unify(List(q, 1), List(0, r))))).head)

      assert(State(Map(_0 -> List(0, _1)), 2) ==
        run(callFresh(q =>
          callFresh(r => unify(q, List(0, r))))).head)

      assert(Map(_0 -> List(0), _1 -> 0, _2 -> 0) ==
        walked((run(callFresh(q => callFresh(r => callFresh(s =>
          conj(conj(unify(q, List(r)), unify(q, List(0))),
            unify(q, List(s))))))).head.substitution)))
    }

    "Unifying data structures"-{
      val basicSeq = callFresh(q => unify(Vector(1, 2, 3), Vector(1, 2, q)))
      assert(3 ==
        pull(basicSeq(emptyState)).head.substitution(LVar(0)).asInstanceOf[Int])

      val lengthMismatch = callFresh(q => unify(List(1,2), List(1,2,3)))
      assert(pull(lengthMismatch(emptyState)).isEmpty)

      val emptyList = callFresh(q => unify(List.empty[Int], List.empty[Int]))
      assert(pull(emptyList(emptyState)).nonEmpty)

      // TODO: Tuples. Shapeless?
    }

    "Circular substitution"-{
      // Note: this test is implementation-specific: LVar index could change
      def circ(v: LVar) =
        callFresh(a => //LVar(0)
          callFresh(b => //LVar(1)
            callFresh(c => //LVar(2)
              conj(unify(a,b),
                conj(unify(b,c),
                  conj(unify(c,a), unify(v, 3)))))))

      val lvars = 0 to 2 map LVar

      for {
        lvar <- lvars
        sub <- lvars.map(v => pull(circ(v)(emptyState)).head.substitution)
      } assert(walk(lvar, sub) == 3)
    }
  }
}

object MicroKanrenSuite extends TestSuite {
  val tests = TestSuite {
    "string reification"-{
      import ukanrenString._

      val Seq(q, r, s) = (0 to 2) map LVar

      assert(reifyS(q, r, s)(
        State(Map(q -> 1, s -> 2, r -> 0), 3)
      ) == "(1, 0, 2)")

      assert(run_*(q => succeed) == Stream("(_0)"))
      assert(run_*((q, r) => succeed) == Stream("(_0, _1)"))
      assert(run_*((q, r) => q === r) == Stream("(_0, _0)"))
      assert(run_*((q, r) => r === q) == Stream("(_0, _0)"))
      assert(run_*((q, r, s) => q === r) == Stream("(_0, _0, _1)"))
      assert(run_*((q, r, s) => q === s) == Stream("(_0, _1, _0)"))
      assert(run_*((q, r, s) => r === s) == Stream("(_0, _1, _1)"))

      assert(Stream("(List(_0, _1))") ==
        run_*(q => fresh((x, y) => (q === List(x, y)))))

      assert(Stream("(_0, List(_1, _2), _3)") ==
        run_*((l, q, r) => fresh((w, x, y) => (q === List(x, y)))))

      assert(Stream("(List(0), 0)") ==
        run_*((q, r) => (q === List(r)) &&& (q === List(0))))

      assert(Stream("(List(_0, _1, _2), _1)") ==
        run_*((q, r) => fresh((x, y, z) => q === List(z, r, x))))

      assert(Stream("(List(_0, _1), _2)") ==
        run_*((q, r) => fresh((x, y, z) => q === List(y, z))))

      assert(Stream("(_0, List(_1, _2))") ==
        run_*((q, r) => fresh((x, y, z) => r === List(y, z))))
    }

    "concrete reification"-{
      import ukanrenConcrete._

      assert(run_*[Int](q => q === 4) ==
        Stream[Either[LVar, Int]](Right(4)))

      assert(run_*[Int](q => succeed) ==
        Stream[Either[LVar, Int]](Left(LVar(0))))

      assert(run_*[List[Int]](q => q === List(4)) ==
        Stream[Either[LVar, List[Int]]](Right(List(4))))

      assert(run_*[List, Int](q => q === List(4)) ==
        Stream[Either[LVar, List[Either[LVar, Int]]]](Right(List(Right(4)))))

      assert(run_*[List, Int](q => fresh(r => q === List(1, r, 3))) ==
        Stream[Either[LVar, List[Either[LVar, Int]]]](
          Right(List(Right(1), Left(LVar(0)), Right(3)))))
    }

    import ukanren._

    "variadic conj/disj"-{
      assert(run_*(() => disj_*(fail, fail, fail)).isEmpty)
      assert(run_*(() => conj_*(succeed, succeed)).nonEmpty)

      val multiconj = fresh((q,r,s) =>
        conj_*((q === 3), (r === 4), (s === q)))

      assert(pull(multiconj(emptyState)).toList ==
        List(State(Map(LVar(0) -> 3, LVar(1) -> 4, LVar(2) -> 3),3)))

      def threes(x: LVar): Goal = disj_*(threes(x), (x === 3), threes(x))
      assert(run_*(threes _).take(3) == Stream(3, 3, 3))

      def notThrees(x: LVar): Goal = conj_*((x === 3), (x === 4), notThrees(x))
      assert(run_*(notThrees _).isEmpty)
    }

    "variaic fresh"-{
      val g2 = fresh((q,r) => conj_*(
        (3 === q), (r === 4)))

      assert(
        pull(g2(emptyState)).toList == List(
          State(Map(LVar(0) -> 3, LVar(1) -> 4),2)))

      val g3 = fresh((q,r,s) => conj_*(
        (0 === r),
        (q === s),
        (s === r)))

      assert(pull(g3(emptyState)).toList == List(
        State(Map(LVar(1) -> 0, LVar(0) -> LVar(2), LVar(2) -> 0),3)))
    }

    "Nested binding"-{
      val (x, y) = (LVar(0), LVar(1))

      assert(State(Map(x -> 1, y -> 3), 2) ==
        pull(fresh((x, y) => (List(x, 2, 3) === List(1, 2, y)))(emptyState)).head
      )

      assert(State(Map(x -> (List(1, y, 3))), 2) ==
        pull(fresh((x, y) => (x === List(1, y, 3)))(emptyState)).head
      )
    }

    "run_* interface"-{
      assert(run_*(() => fail) == Stream())
      assert(run_*(() => succeed) == Stream((): Unit))
      assert(run_*((q, r, s) => (r === s)) == Stream((_0, _1, _1)))
    }

    "syntax examples"-{
      def teacup(x: LVar) =
        ('tea === x) ||| ('cup === x)

      assert(run_*(x => teacup(x)) == Stream(('tea), ('cup)))
    }

    "lcons"-{
      assert(Stream((_0)) ==
        run_*(q => conso(0, List(1, 2, 3), List(0, 1, 2, 3))))

      assert(Stream((0, 1, 2)) ==
        run_*((q, r, s) => conso(q, List(r, 2, 3), List(0, 1, s, 3))))

      assert(Stream(List(1, 2, 3)) ==
        run_*(q => conso(0, q, List(0, 1, 2, 3))))

      assert(Stream(List(0, 1, 2, 3)) ==
        run_*(q => conso(0, List(1, 2, 3), q)))

      assert(run_*((q, r) => conso(0, q, r)) == Stream((_0, 0::_0)))
      assert(run_*((q, r) => conso(q, List(1), r)) == Stream((_0, List(_0, 1))))
      assert(run_*((q, r) => conso(q, r, List(1))) == Stream((1, List())))
      assert(run_*(conso _) == Stream((_0, _1, _0::_1)))

      assert(Stream((_0::_1::_2)) ==
        run_*(out =>
          fresh((q, r, s) =>
            fresh(l =>
              conso(r, s, l) &&& conso(q, l, out)))))

      assert(Stream((_0, _1, _0::_1)) ==
        run_*((a, d, l) =>
          fresh((a2, d2) =>
            conso(a, d, l) &&& conso(a2, d2, l))))
    }
      
    "other list operations"-{
      assert(Stream(
        (List("first", "last")),
        (List("first", _0, "last")),
        (List("first", _0, _1, "last")),
        (List("first", _0, _1, _2, "last"))
      ) ==
        run_*(result  =>
          fresh((listA, listB, tailA) => conj_*(
            conso("first", tailA, listA),
            listB === List("last"),
            appendo(listA, listB, result)))
        ).take(4))

      assert(run_*(q => heado(q, 1 to 10)) == Stream(1))

      assert(run_*(q => rembero(q, List(1, 2), List(1))) == Stream(2))
      assert(run_*(q => rembero(q, List(1, 2), List(2))) == Stream(1))
      assert(run_*(q => rembero(2, q, List(1))) == Stream(List(2, 1), List(1, 2)))
      assert(run_*(q => rembero(1, List(1, 2), q)) == Stream(List(2)))
      assert(run_*(q => rembero(2, List(1, 2), q)) == Stream(List(1)))

      assert(run_*(q => rembero(3, q, List(1, 2))) ==
        Stream(List(3, 1, 2), List(1, 3, 2), List(1, 2, 3)))

      assert(run_*(q => membero(3, q)).take(3)
        == Stream((3::_0), (_0::3::_1), (_0::_1::3::_2)))
      assert(run_*(q => membero(q, List(1, 2, 3))) == Stream(1, 2, 3))
      assert(run_*(q => membero(2, List(1, q, 3))) == Stream(2))
      assert(run_*(q => membero(1, List(1, q, 3))).toSet == Set(1, _0))

      assert(run_*(q => permuto(q, 1 to 4)).toSet
        == (1 to 4).permutations.toSet)

      assert(run_*(q => permuto(q, List(1))) == Stream(List(1)))
      assert(run_*(q => permuto(List(1), q)) == Stream(List(1)))
    }
  }
}
