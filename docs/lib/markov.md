# `Markov`

"If something cannot go on forever, it will stop." -- Herb Stein

Markov's principle states that a computation that does not run forever
will terminate.  Although many intuitionists eschew Markov's principle,
it is constructive in the sense that there exists an algorithm that
produces evidence that the computation terminates.  Namely: run the
computation until it terminates.

In Istari, Markov's principle is implemented by a rule
(`markovsPrinciple`), but a lemma puts it in convenient form:

    markov_halts : forall (i : level) (a : U i) (m : partial a) .
                      not (not (Partial.halts m)) -> Partial.halts m

Another common way of expressing Markov's principle involves searching
for a number that satisfies a predicate.  This is a corollary of the
preceding lemma.

    markov_search : forall (lv : level) (P : nat -> U lv) .
                       (forall (i : nat) . Decidable.decidable (P i))
                       -> not (forall (i : nat) . not (P i))
                       -> exists (i : nat) . P i
