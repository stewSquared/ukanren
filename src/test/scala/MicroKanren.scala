/*

"A goal pursued in a given state can succeed or fail"

"The result of a uKanren program is a stream of satisying states"

"A goal constructed from disj returns a non-empty stream if either of
its two arguments is successful"

"A Goals constructed from conj returns a non-empty stream if the
second argument can be achieved in the stream created by the first"

 */

import utest._
import utest.ExecutionContext.RunNow
import ukanren._

object MicroKanrenSuite extends TestSuite {
  val tests = TestSuite {
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

    "Infinite streams"-{
      def fives(x: LVar): Goal = disj(===(x, 5), Zzz(fives(x)))
      val $Cons(fst, ImmatureStream(imm0)) = callFresh(fives)(emptyState)
      val $Cons(snd, ImmatureStream(imm1)) = imm0()
      val $Cons(trd, ImmatureStream(imm2)) = imm1()
      assert(fst == snd)
      assert(snd == trd)
    }
  }
}
