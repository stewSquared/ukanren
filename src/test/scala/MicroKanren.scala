import utest._
import utest.ExecutionContext.RunNow
import ukanren._

object MicroKanrenSuite extends TestSuite {
  val tests = TestSuite {
    def run(g: Goal) = pull(g(emptyState))

    "First example uKanren query"-{
      assert(
        callFresh(q => ===(q, 5))(emptyState) ==
          $Cons(State(Map(LVar(0) -> 5), 1), $Nil))
    }

    "Second example uKanren query"-{
      def ab: Goal = conj(
        callFresh(a => ===(a,7)),
        callFresh(b => disj(
          ===(b,5),
          ===(b,6))))

      assert(ab(emptyState) ==
        $Cons(State(Map(LVar(0) -> 7, LVar(1) -> 5), 2),
          $Cons(State(Map(LVar(0) -> 7, LVar(1) -> 6), 2), $Nil)))
    }

    def fives(x: LVar): Goal = disj(===(x, 5), Zzz(fives(x)))
    def fivesLeft(x: LVar): Goal = disj(Zzz(fivesLeft(x)), ===(x, 5))
    def sixes(x: LVar): Goal = disj(===(x, 6), Zzz(fives(x)))
    def fivesAndSixes = callFresh(x => disj(fives(x), sixes(x)))

    "Infinite streams"-{
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

    "Unifying data structures"-{
      val basicSeq = callFresh(q => ===(Vector(1, 2, 3), Vector(1, 2, q)))
      assert(3 ==
        pull(basicSeq(emptyState)).head.substitution(LVar(0)).asInstanceOf[Int])

      val lengthMismatch = callFresh(q => ===(List(1,2), List(1,2,3)))
      assert(pull(lengthMismatch(emptyState)).isEmpty)

      val emptyList = callFresh(q => ===(List.empty[Int], List.empty[Int]))
      assert(pull(emptyList(emptyState)).nonEmpty)

      // TODO: Tuples. Shapeless?
    }

    "Circular substitution"-{
      // Note: this test is implementation-specific: LVar index could change
      def circ(v: LVar) =
        callFresh(a => //LVar(0)
          callFresh(b => //LVar(1)
            callFresh(c => //LVar(2)
              conj(===(a,b),
                conj(===(b,c),
                  conj(===(c,a), ===(v, 3)))))))

      val lvars = 0 to 2 map LVar

      for {
        lvar <- lvars
        sub <- lvars.map(v => pull(circ(v)(emptyState)).head.substitution)
      } assert(walk(lvar, sub) == 3)
    }

    "Repeated binding"-{
      val g = callFresh(q => conj(===(q, 3), ===(q, 4)))
      assert(pull(g(emptyState)).isEmpty)
    }

    "variadic conj/disj"-{
      assert(pull(callFresh(_ => disj_*(fail, fail, fail))(emptyState)).isEmpty)
      assert(pull(callFresh(_ => conj_*(succeed, succeed))(emptyState)).nonEmpty)

      val multiconj =
        callFresh(q =>
          callFresh(r =>
            callFresh(s => conj_*(
              ===(q, 3),
              ===(r, 4),
              ===(s, q)))))

      assert(pull(multiconj(emptyState)).toList ==
        List(State(Map(LVar(0) -> 3, LVar(1) -> 4, LVar(2) -> 3),3)))

      // Look, no Zzz!
      def threes(x: LVar): Goal = disj_*(threes(x), ===(x, 3), threes(x))
      assert(pull(callFresh(threes)(emptyState)).take(3).head ==
        State(Map(LVar(0) -> 3),1))

      def notThrees(x: LVar): Goal = conj_*(===(x, 3), ===(x, 4), notThrees(x))
      assert(pull(callFresh(notThrees)(emptyState)).isEmpty)
    }

    "variaic fresh"-{
      val g2 = fresh((q,r) => conj_*(
        ===(3,q), ===(r,4)))

      assert(
        pull(g2(emptyState)).toList == List(
          State(Map(LVar(0) -> 3, LVar(1) -> 4),2)))

      val g3 = fresh((q,r,s) => conj_*(
        ===(0,r),
        ===(q,s),
        ===(s,r)))

      assert(pull(g3(emptyState)).toList == List(
        State(Map(LVar(1) -> 0, LVar(0) -> LVar(2), LVar(2) -> 0),3)))
    }

    "reification"-{
      val Seq(q, r, s) = (0 to 2) map LVar

      assert(reify(q, r, s)(
        State(Map(q -> 1, s -> 2, r -> 0), 3)
      ) == "(1, 0, 2)")

      assert(run(fresh(q => succeed)).map(reify(q)).head == "(_0)")
      assert(run(fresh((q, r) => succeed)).map(reify(q, r)).head == "(_0, _1)")
      assert(run(fresh((q, r) => ===(q, r))).map(reify(q, r)).head == "(_0, _0)")
      assert(run(fresh((q, r) => ===(r, q))).map(reify(q, r)).head == "(_0, _0)")
      assert(run(fresh((q, r, s) => ===(q, r))).map(reify(q, r, s)).head == "(_0, _0, _1)")
      assert(run(fresh((q, r, s) => ===(q, s))).map(reify(q, r, s)).head == "(_0, _1, _0)")
      assert(run(fresh((q, r, s) => ===(r, s))).map(reify(q, r, s)).head == "(_0, _1, _1)")
      assert(run(succeed).map(reify()).head == "()")
    }

    "run_* interface"-{
      assert(run_*(() => fail) == Stream())
      assert(run_*(() => succeed) == Stream("()"))
      assert(run_*((q, r, s) => ===(r, s)) == Stream("(_0, _1, _1)"))
    }
  }
}
