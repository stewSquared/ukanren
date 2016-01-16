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

    "Illustrate finite stream flaw"-{
      def fives(x: LVar): Goal = disj(===(x, 5), fives(x))
      // Stack Overflow Error:
      // callFresh(fives)(emptyState)
    }
  }
}
