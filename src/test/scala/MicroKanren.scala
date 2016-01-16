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

    def fives(x: LVar): Goal = disj(===(x, 5), Zzz(fives(x)))
    def fivesLeft(x: LVar): Goal = disj(Zzz(fivesLeft(x)), ===(x, 5))
    def sixes(x: LVar): Goal = disj(===(x, 6), Zzz(fives(x)))
    def fivesAndSixes = callFresh(x => disj(fives(x), sixes(x)))

    def allIntegersAreEqual(x: LVar) = {
      def nextInt(n: Int) = if (n > 0) -n else -n+1
      def equalTo(n: Int): Goal = conj(===(x, n), Zzz(equalTo(nextInt(n))))
      equalTo(0)
    }

    "Infinite streams"-{
      val $Cons(fst, ImmatureStream(imm0)) = callFresh(fives)(emptyState)
      val $Cons(snd, ImmatureStream(imm1)) = imm0()
      val $Cons(trd, ImmatureStream(imm2)) = imm1()
      assert(fst == snd)
      assert(snd == trd)
    }

    "Left-handed infinite stream"-{
      assert(pull(callFresh(fives)(emptyState)).take(5).toList ==
        pull(callFresh(fivesLeft)(emptyState)).take(5).toList)

      def falseRecursiveConjLeft(x: LVar): Goal =
        conj(Zzz(falseRecursiveConjLeft(x)), fail)

      callFresh(falseRecursiveConjLeft)(emptyState)
    }

    "Infinite conj"-{
      assert(pull(callFresh(allIntegersAreEqual)(emptyState)).isEmpty)
    }

    "Interleaving streams"-{
      assert(
        pull(fivesAndSixes(emptyState))
          .take(5).flatMap(_.substitution.values)
          .toSet == Set(5,6))
    }
  }
}
