# Istari rules in explicit form

Conventions:

- A rule is written `[conclusion] >> [premise] ... [premise]`.
  When a rule has no premises, the `>>` is omitted.

- The argument `n` is the length of the context `G2`, in rules where
  `G2` appears.

- Omitted extracts in the conclusion are taken to be `()`.  Omitted
  extracts in premises are unused.

Note that no effort was made to keep the set of rules minimal.  Many
rules that would follow from other rules are nonetheless included for
the sake of convenience or performance.  Since (nearly) all the rules
are verified, there is no robustness advantage to minimizing the set
of rules.

Rules are given here in the official form, using de Bruijn indices.
Human-readable rules, using explicit variables, are given
[here](rules-db.html).


### Contents

[Structural](#structural)<br>
[Reduction](#reduction)<br>
[Dependent functions](#dependent-functions)<br>
[Functions](#functions)<br>
[T-Functions](#t-functions)<br>
[K-Functions](#k-functions)<br>
[Intersection types](#intersection-types)<br>
[Parametric functions](#parametric-functions)<br>
[Guarded types](#guarded-types)<br>
[Strong sums](#strong-sums)<br>
[Products](#products)<br>
[Semi-dependent products](#semi-dependent-products)<br>
[Union types](#union-types)<br>
[Coguarded types](#coguarded-types)<br>
[Disjoint sums](#disjoint-sums)<br>
[Future modality](#future-modality)<br>
[Future functions](#future-functions)<br>
[Future intersect](#future-intersect)<br>
[Future parametric](#future-parametric)<br>
[Recursive types](#recursive-types)<br>
[Inductive types](#inductive-types)<br>
[Void](#void)<br>
[Unit](#unit)<br>
[Bool](#bool)<br>
[Natural numbers](#natural-numbers)<br>
[Universes](#universes)<br>
[Kinds](#kinds)<br>
[Levels](#levels)<br>
[Equality](#equality)<br>
[Typing](#typing)<br>
[Type equality](#type-equality)<br>
[Type formation](#type-formation)<br>
[Subtyping](#subtyping)<br>
[Subset types](#subset-types)<br>
[Intensional subset types](#intensional-subset-types)<br>
[Squash](#squash)<br>
[Intensional squash](#intensional-squash)<br>
[Quotient types](#quotient-types)<br>
[Impredicative universals](#impredicative-universals)<br>
[Impredicative polymorphism](#impredicative-polymorphism)<br>
[Impredicative existentials](#impredicative-existentials)<br>
[Miscellaneous](#miscellaneous)<br>
[Syntactic equality](#syntactic-equality)<br>
[Partial types](#partial-types)<br>
[Let hypotheses](#let-hypotheses)<br>
[Integers](#integers)<br>
[Rewriting](#rewriting)<br>


### Structural

- `hypothesis n`

      G1, A, G2 |- A[^n+1] ext n

- `hypothesisOf n`

      G1, A, G2 |- of A[^n+1] n

- `hypothesisEq n`

      G1, A, G2 |- eq A[^n+1] n n

- `hypothesisOfTp n`

      G1, type, G2 |- istp n

- `hypothesisEqTp n`

      G1, type, G2 |- eqtp n n

- `weaken m n` 

      G1, G2, G3[^n] |- A[under_m (^n)] ext M[under_m (^n)]
      >>
      G1, G3 |- A ext M
      (where m = length(G3) and n = length(G2))

- `exchange l m n` 

      G1, G2, G3[^n], G4[s] |- A[under_l (s)] ext M[under_l (s)]
      >>
      G1, G3, G2[^m], G4 |- A ext M
      (where l = length(G4), m = length(G3), n = length(G2), 
       s = m ... m+n-1 . 0 ... m-1 . ^m+n)


### Reduction

- `reduce red`

      G |- C ext M
      >>
      G |- D ext M
      (where red reduces C to D)

- `unreduce C red`

      G |- D ext M
      >>
      G |- C ext M
      (where red reduces C to D)

- `reduceAt i C M red`

      G |- C[under_i (M . id)] ext P
      >>
      G |- C[under_i (N . id)] ext P
      (where red reduces M to N)

- `unreduceAt i C M red`

      G |- C[under_i (N . id)] ext P
      >>
      G |- C[under_i (M . id)] ext P
      (where red reduces M to N)

- `reduceHyp n red`

      G1, C, G2 |- C ext M
      >>
      G1, D, G2 |- C ext M
      (where red reduces C to D)

- `unreduceHyp n C red`

      G1, D, G2 |- C ext M
      >>
      G1, C, G2 |- C ext M
      (where red reduces C to D)

- `reduceHypAt n i H M red`

      G1, H[under_i (M . id)], G2 |- C ext P
      >>
      G1, H[under_i (N . id)], G2 |- C ext P
      (where red reduces M to N)

- `unreduceHypAt n i H M red`

      G1, H[under_i (N . id)], G2 |- C ext P
      >>
      G1, H[under_i (M . id)], G2 |- C ext P
      (where red reduces M to N)

- `whnfConcl`

      G |- C ext M
      >>
      G |- D ext M
      (where the weak-head normal form of C is D)

- `whnfHyp n`

      G1, H, G2 |- C ext M
      >>
      G1, H', G2 |- C ext M
      (where the weak-head normal form of H is H')

- `whnfHardConcl`

      G |- C ext M
      >>
      G |- D ext M
      (where the hard weak-head normal form of C is D)

- `whnfHardHyp n`

      G1, H, G2 |- C ext M
      >>
      G1, H', G2 |- C ext M
      (where the hard weak-head normal form of H is H')

- `normalizeConcl`

      G |- C ext M
      >>
      G |- D ext M
      (where the normal form of C is D)

- `normalizeHyp n`

      G1, H, G2 |- C ext M
      >>
      G1, H', G2 |- C ext M
      (where the normal form of H is H')

- `whnfConclAt path`

      G |- C ext M
      >>
      G |- C' ext M
      (where C' is obtained from C by weak-head normalizing a subterm determined by path)

- `whnfHypAt n path`

      G1, H, G2 |- C ext M
      >>
      G1, H', G2 |- C' ext M
      (where H' is obtained from H by weak-head normalizing a subterm determined by path)


### Dependent functions

- `forallForm A B`

      G |- istp (forall A (fn . B))
      >>
      G |- istp A
      G, A |- istp B

- `forallEq A A' B B'`

      G |- eqtp (forall A (fn . B)) (forall A' (fn . B'))
      >>
      G |- eqtp A A'
      G, A |- eqtp B B'

- `forallFormUniv A B I`

      G |- of (univ I) (forall A (fn . B))
      >>
      G |- of (univ I) A
      G, A |- of (univ I[^1]) B

- `forallEqUniv A A' B B' I`

      G |- eq (univ I) (forall A (fn . B)) (forall A' (fn . B'))
      >>
      G |- eq (univ I) A A'
      G, A |- eq (univ I[^1]) B B'

- `forallSub A A' B B'`

      G |- subtype (forall A (fn . B)) (forall A' (fn . B'))
      >>
      G |- subtype A' A
      G, A' |- subtype B B'
      G, A |- istp B

- `forallIntroOf A B M`

      G |- of (forall A (fn . B)) (fn . M)
      >>
      G |- istp A
      G, A |- of B M

- `forallIntroEq A B M N`

      G |- eq (forall A (fn . B)) (fn . M) (fn . N)
      >>
      G |- istp A
      G, A |- eq B M N

- `forallIntro A B`

      G |- forall A (fn . B) ext fn . M
      >>
      G |- istp A
      G, A |- B ext M

- `forallElimOf A B M P`

      G |- of B[P . id] (M P)
      >>
      G |- of (forall A (fn . B)) M
      G |- of A P

- `forallElimEq A B M N P Q`

      G |- eq B[P . id] (M P) (N Q)
      >>
      G |- eq (forall A (fn . B)) M N
      G |- eq A P Q

- `forallElim A B P`

      G |- B[P . id] ext M P
      >>
      G |- forall A (fn . B) ext M
      G |- of A P

- `forallEta A B M`

      G |- eq (forall A (fn . B)) M (fn . M[^1] 0)
      >>
      G |- of (forall A (fn . B)) M

- `forallExt A B M N`

      G |- eq (forall A (fn . B)) M N
      >>
      G |- of (forall A (fn . B)) M
      G |- of (forall A (fn . B)) N
      G, A |- eq B (M[^1] 0) (N[^1] 0)

- `forallExt' A A' A'' B B' B'' M N`

      G |- eq (forall A (fn . B)) M N
      >>
      G |- istp A
      G |- of (forall A' (fn . B')) M
      G |- of (forall A'' (fn . B'')) N
      G, A |- eq B (M[^1] 0) (N[^1] 0)

- `forallOfExt A A' B B' M`

      G |- of (forall A (fn . B)) M
      >>
      G |- istp A
      G |- of (forall A' (fn . B')) M
      G, A |- of B (M[^1] 0)

- `forallFormInv1 A B`

      G |- istp A
      >>
      G |- istp (forall A (fn . B))

- `forallFormInv2 A B M`

      G |- istp B[M . id]
      >>
      G |- istp (forall A (fn . B))
      G |- of A M


### Functions

- `arrowForm A B`

      G |- istp (arrow A B)
      >>
      G |- istp A
      G, A |- istp B[^1]

- `arrowEq A A' B B'`

      G |- eqtp (arrow A B) (arrow A' B')
      >>
      G |- eqtp A A'
      G, A |- eqtp B[^1] B'[^1]

- `arrowFormUniv A B I`

      G |- of (univ I) (arrow A B)
      >>
      G |- of (univ I) A
      G, A |- of (univ I[^1]) B[^1]

- `arrowEqUniv A A' B B' I`

      G |- eq (univ I) (arrow A B) (arrow A' B')
      >>
      G |- eq (univ I) A A'
      G, A |- eq (univ I[^1]) B[^1] B'[^1]

- `arrowForallEq A A' B B'`

      G |- eqtp (arrow A B) (forall A' (fn . B'))
      >>
      G |- eqtp A A'
      G, A |- eqtp B[^1] B'

- `arrowForallEqUniv A A' B B' I`

      G |- eq (univ I) (arrow A B) (forall A' (fn . B'))
      >>
      G |- eq (univ I) A A'
      G, A |- eq (univ I[^1]) B[^1] B'

- `arrowSub A A' B B'`

      G |- subtype (arrow A B) (arrow A' B')
      >>
      G |- subtype A' A
      G |- subtype B B'

- `arrowForallSub A A' B B'`

      G |- subtype (arrow A B) (forall A' (fn . B'))
      >>
      G |- subtype A' A
      G, A' |- subtype B[^1] B'
      G |- istp B

- `forallArrowSub A A' B B'`

      G |- subtype (forall A (fn . B)) (arrow A' B')
      >>
      G |- subtype A' A
      G, A' |- subtype B B'[^1]
      G, A |- istp B

- `arrowIntroOf A B M`

      G |- of (arrow A B) (fn . M)
      >>
      G |- istp A
      G, A |- of B[^1] M

- `arrowIntroEq A B M N`

      G |- eq (arrow A B) (fn . M) (fn . N)
      >>
      G |- istp A
      G, A |- eq B[^1] M N

- `arrowIntro A B`

      G |- arrow A B ext fn . M
      >>
      G |- istp A
      G, A |- B[^1] ext M

- `arrowElimOf A B M P`

      G |- of B (M P)
      >>
      G |- of (arrow A B) M
      G |- of A P

- `arrowElimEq A B M N P Q`

      G |- eq B (M P) (N Q)
      >>
      G |- eq (arrow A B) M N
      G |- eq A P Q

- `arrowElim A B`

      G |- B ext M P
      >>
      G |- arrow A B ext M
      G |- A ext P

- `arrowEta A B M`

      G |- eq (arrow A B) M (fn . M[^1] 0)
      >>
      G |- of (arrow A B) M

- `arrowExt A B M N`

      G |- eq (arrow A B) M N
      >>
      G |- of (arrow A B) M
      G |- of (arrow A B) N
      G, A |- eq B[^1] (M[^1] 0) (N[^1] 0)

- `arrowExt' A A' A'' B B' B'' M N`

      G |- eq (arrow A B) M N
      >>
      G |- istp A
      G |- of (forall A' (fn . B')) M
      G |- of (forall A'' (fn . B'')) N
      G, A |- eq B[^1] (M[^1] 0) (N[^1] 0)

- `arrowOfExt A A' B B' M`

      G |- of (arrow A B) M
      >>
      G |- istp A
      G |- of (forall A' (fn . B')) M
      G, A |- of B[^1] (M[^1] 0)

- `arrowFormInv1 A B`

      G |- istp A
      >>
      G |- istp (arrow A B)

- `arrowFormInv2 A B M`

      G |- istp B
      >>
      G |- istp (arrow A B)
      G |- of A M


### T-Functions

- `tarrowKind A I K`

      G |- of (kind I) (tarrow A K)
      >>
      G |- of (univ I) A
      G |- of (kind I) K

- `tarrowKindEq A A' I K K'`

      G |- eq (kind I) (tarrow A K) (tarrow A' K')
      >>
      G |- eq (univ I) A A'
      G |- eq (kind I) K K'

- `tarrowForm A B`

      G |- istp (tarrow A B)
      >>
      G |- istp A
      G |- istp B

- `tarrowEq A A' B B'`

      G |- eqtp (tarrow A B) (tarrow A' B')
      >>
      G |- eqtp A A'
      G |- eqtp B B'

- `tarrowFormUniv A B I`

      G |- of (univ I) (tarrow A B)
      >>
      G |- of (univ I) A
      G |- of (univ I) B

- `tarrowEqUniv A A' B B' I`

      G |- eq (univ I) (tarrow A B) (tarrow A' B')
      >>
      G |- eq (univ I) A A'
      G |- eq (univ I) B B'

- `tarrowArrowEq A A' B B'`

      G |- eqtp (tarrow A B) (arrow A' B')
      >>
      G |- eqtp A A'
      G |- eqtp B B'

- `tarrowArrowEqUniv A A' B B' I`

      G |- eq (univ I) (tarrow A B) (arrow A' B')
      >>
      G |- eq (univ I) A A'
      G |- eq (univ I) B B'

- `tarrowForallEq A A' B B'`

      G |- eqtp (tarrow A B) (forall A' (fn . B'))
      >>
      G |- eqtp A A'
      G, A |- eqtp B[^1] B'
      G |- istp B

- `tarrowForallEqUniv A A' B B' I`

      G |- eq (univ I) (tarrow A B) (forall A' (fn . B'))
      >>
      G |- eq (univ I) A A'
      G, A |- eq (univ I[^1]) B[^1] B'
      G |- of (univ I) B

- `tarrowIntroOf A B M`

      G |- of (tarrow A B) (fn . M)
      >>
      G |- istp A
      G |- istp B
      G, A |- of B[^1] M

- `tarrowIntroEq A B M N`

      G |- eq (tarrow A B) (fn . M) (fn . N)
      >>
      G |- istp A
      G |- istp B
      G, A |- eq B[^1] M N

- `tarrowIntro A B`

      G |- tarrow A B ext fn . M
      >>
      G |- istp A
      G |- istp B
      G, A |- B[^1] ext M

- `tarrowElimOf A B M P`

      G |- of B (M P)
      >>
      G |- of (tarrow A B) M
      G |- of A P

- `tarrowElimEq A B M N P Q`

      G |- eq B (M P) (N Q)
      >>
      G |- eq (tarrow A B) M N
      G |- eq A P Q

- `tarrowElim A B`

      G |- B ext M P
      >>
      G |- tarrow A B ext M
      G |- A ext P

- `tarrowEta A B M`

      G |- eq (tarrow A B) M (fn . M[^1] 0)
      >>
      G |- of (tarrow A B) M

- `tarrowExt A B M N`

      G |- eq (tarrow A B) M N
      >>
      G |- istp B
      G |- of (tarrow A B) M
      G |- of (tarrow A B) N
      G, A |- eq B[^1] (M[^1] 0) (N[^1] 0)

- `tarrowOfExt A A' B B' M`

      G |- of (tarrow A B) M
      >>
      G |- istp A
      G |- istp B
      G |- of (forall A' (fn . B')) M
      G, A |- of B[^1] (M[^1] 0)


### K-Functions

- `karrowKind I K L`

      G |- of (kind I) (karrow K L)
      >>
      G |- of (kind I) K
      G |- of (kind I) L

- `karrowKindEq I K K' L L'`

      G |- eq (kind I) (karrow K L) (karrow K' L')
      >>
      G |- eq (kind I) K K'
      G |- eq (kind I) L L'

- `karrowForm A B`

      G |- istp (karrow A B)
      >>
      G |- istp A
      G |- istp B

- `karrowEq A A' B B'`

      G |- eqtp (karrow A B) (karrow A' B')
      >>
      G |- eqtp A A'
      G |- eqtp B B'

- `karrowFormUniv A B I`

      G |- of (univ I) (karrow A B)
      >>
      G |- of (univ I) A
      G |- of (univ I) B

- `karrowEqUniv A A' B B' I`

      G |- eq (univ I) (karrow A B) (karrow A' B')
      >>
      G |- eq (univ I) A A'
      G |- eq (univ I) B B'

- `karrowArrowEq A A' B B'`

      G |- eqtp (karrow A B) (arrow A' B')
      >>
      G |- eqtp A A'
      G |- eqtp B B'

- `karrowArrowEqUniv A A' B B' I`

      G |- eq (univ I) (karrow A B) (arrow A' B')
      >>
      G |- eq (univ I) A A'
      G |- eq (univ I) B B'

- `karrowForallEq A A' B B'`

      G |- eqtp (karrow A B) (forall A' (fn . B'))
      >>
      G |- eqtp A A'
      G, A |- eqtp B[^1] B'
      G |- istp B

- `karrowForallEqUniv A A' B B' I`

      G |- eq (univ I) (karrow A B) (forall A' (fn . B'))
      >>
      G |- eq (univ I) A A'
      G, A |- eq (univ I[^1]) B[^1] B'
      G |- of (univ I) B

- `karrowIntroOf A B M`

      G |- of (karrow A B) (fn . M)
      >>
      G |- istp A
      G |- istp B
      G, A |- of B[^1] M

- `karrowIntroEq A B M N`

      G |- eq (karrow A B) (fn . M) (fn . N)
      >>
      G |- istp A
      G |- istp B
      G, A |- eq B[^1] M N

- `karrowIntro A B`

      G |- karrow A B ext fn . M
      >>
      G |- istp A
      G |- istp B
      G, A |- B[^1] ext M

- `karrowElimOf A B M P`

      G |- of B (M P)
      >>
      G |- of (karrow A B) M
      G |- of A P

- `karrowElimEq A B M N P Q`

      G |- eq B (M P) (N Q)
      >>
      G |- eq (karrow A B) M N
      G |- eq A P Q

- `karrowElim A B`

      G |- B ext M P
      >>
      G |- karrow A B ext M
      G |- A ext P

- `karrowEta A B M`

      G |- eq (karrow A B) M (fn . M[^1] 0)
      >>
      G |- of (karrow A B) M

- `karrowExt A B M N`

      G |- eq (karrow A B) M N
      >>
      G |- istp B
      G |- of (karrow A B) M
      G |- of (karrow A B) N
      G, A |- eq B[^1] (M[^1] 0) (N[^1] 0)

- `karrowOfExt A A' B B' M`

      G |- of (karrow A B) M
      >>
      G |- istp A
      G |- istp B
      G |- of (forall A' (fn . B')) M
      G, A |- of B[^1] (M[^1] 0)


### Intersection types

- `intersectForm A B`

      G |- istp (intersect A (fn . B))
      >>
      G |- istp A
      G, A |- istp B

- `intersectEq A A' B B'`

      G |- eqtp (intersect A (fn . B)) (intersect A' (fn . B'))
      >>
      G |- eqtp A A'
      G, A |- eqtp B B'

- `intersectFormUniv A B I`

      G |- of (univ I) (intersect A (fn . B))
      >>
      G |- of (univ I) A
      G, A |- of (univ I[^1]) B

- `intersectEqUniv A A' B B' I`

      G |- eq (univ I) (intersect A (fn . B)) (intersect A' (fn . B'))
      >>
      G |- eq (univ I) A A'
      G, A |- eq (univ I[^1]) B B'

- `intersectSub A A' B B'`

      G |- subtype (intersect A (fn . B)) (intersect A' (fn . B'))
      >>
      G |- subtype A' A
      G, A' |- subtype B B'
      G, A |- istp B

- `intersectIntroOf A B M`

      G |- of (intersect A (fn . B)) M
      >>
      G |- istp A
      G, A |- of B M[^1]

- `intersectIntroEq A B M N`

      G |- eq (intersect A (fn . B)) M N
      >>
      G |- istp A
      G, A |- eq B M[^1] N[^1]

- `intersectIntro A B`

      G |- intersect A (fn . B) ext M[() . id]
      >>
      G |- istp A
      G, (hidden) A |- B ext M

- `intersectElimOf A B M P`

      G |- of B[P . id] M
      >>
      G |- of (intersect A (fn . B)) M
      G |- of A P

- `intersectElimEq A B M N P`

      G |- eq B[P . id] M N
      >>
      G |- eq (intersect A (fn . B)) M N
      G |- of A P

- `intersectElim A B P`

      G |- B[P . id] ext M
      >>
      G |- intersect A (fn . B) ext M
      G |- of A P

- `intersectFormInv1 A B`

      G |- istp A
      >>
      G |- istp (intersect A (fn . B))

- `intersectFormInv2 A B M`

      G |- istp B[M . id]
      >>
      G |- istp (intersect A (fn . B))
      G |- of A M


### Parametric functions

- `parametricForm A B`

      G |- istp (parametric A (fn . B))
      >>
      G |- istp A
      G, A |- istp B

- `parametricEq A A' B B'`

      G |- eqtp (parametric A (fn . B)) (parametric A' (fn . B'))
      >>
      G |- eqtp A A'
      G, A |- eqtp B B'

- `parametricFormUniv A B I`

      G |- of (univ I) (parametric A (fn . B))
      >>
      G |- of (univ I) A
      G, A |- of (univ I[^1]) B

- `parametricEqUniv A A' B B' I`

      G |- eq (univ I) (parametric A (fn . B)) (parametric A' (fn . B'))
      >>
      G |- eq (univ I) A A'
      G, A |- eq (univ I[^1]) B B'

- `parametricSub A A' B B'`

      G |- subtype (parametric A (fn . B)) (parametric A' (fn . B'))
      >>
      G |- subtype A' A
      G, A' |- subtype B B'
      G, A |- istp B

- `parametricForallSub A A' B B'`

      G |- subtype (parametric A (fn . B)) (forall A' (fn . B'))
      >>
      G |- subtype A' A
      G, A' |- subtype B B'
      G, A |- istp B

- `parametricIntroOf A B M`

      G |- of (parametric A (fn . B)) (fn . M)
      >>
      G |- istp A
      G |- irrelevant (fn . M)
      G, A |- of B M

- `parametricIntroEq A B M N`

      G |- eq (parametric A (fn . B)) (fn . M) (fn . N)
      >>
      G |- istp A
      G |- irrelevant (fn . M)
      G |- irrelevant (fn . N)
      G, A |- eq B M N

- `parametricIntro A B`

      G |- parametric A (fn . B) ext fn . M
      >>
      G |- istp A
      G, (hidden) A |- B ext M

- `parametricIntroOfForall A B M`

      G |- of (parametric A (fn . B)) M
      >>
      G |- of (forall A (fn . B)) M
      G |- irrelevant (fn . M[^1] 0)

- `parametricElimOf A B M P`

      G |- of B[P . id] (paramapp M P)
      >>
      G |- of (parametric A (fn . B)) M
      G |- of A P

- `parametricElimEq A B M N P Q`

      G |- eq B[P . id] (paramapp M P) (paramapp N Q)
      >>
      G |- eq (parametric A (fn . B)) M N
      G |- eq A P Q

- `parametricElim A B P`

      G |- B[P . id] ext paramapp M P
      >>
      G |- parametric A (fn . B) ext M
      G |- of A P

- `parametricElim' A B P`

      G |- B[P . id] ext paramapp M unavailable
      >>
      G |- parametric A (fn . B) ext M
      G |- of A P

- `parametricBeta M N`

      G |- sequal (paramapp (fn . M) N) M[N . id]
      >>
      G |- irrelevant (fn . M)

- `parametricEta A B M`

      G |- eq (parametric A (fn . B)) M (fn . paramapp M[^1] 0)
      >>
      G |- of (parametric A (fn . B)) M

- `parametricExt A B M N`

      G |- eq (parametric A (fn . B)) M N
      >>
      G |- of (parametric A (fn . B)) M
      G |- of (parametric A (fn . B)) N
      G, A |- eq B (paramapp M[^1] 0) (paramapp N[^1] 0)

- `parametricExt' A A' A'' B B' B'' M N`

      G |- eq (parametric A (fn . B)) M N
      >>
      G |- istp A
      G |- of (parametric A' (fn . B')) M
      G |- of (parametric A'' (fn . B'')) N
      G, A |- eq B (paramapp M[^1] 0) (paramapp N[^1] 0)

- `parametricOfExt A A' B B' M`

      G |- of (parametric A (fn . B)) M
      >>
      G |- istp A
      G |- of (parametric A' (fn . B')) M
      G, A |- of B (paramapp M[^1] 0)

- `parametricFormInv1 A B`

      G |- istp A
      >>
      G |- istp (parametric A (fn . B))

- `parametricFormInv2 A B M`

      G |- istp B[M . id]
      >>
      G |- istp (parametric A (fn . B))
      G |- of A M

- `parametricElimIrrelevant M P Q`

      G |- sequal (paramapp M P) (paramapp M Q)

- `irrelevance M`

      G |- irrelevant (fn . M)
      >>
      G, nonsense |- sequal M M[unavailable . ^1]


### Guarded types

- `guardForm A B`

      G |- istp (guard A B)
      >>
      G |- istp A
      G, A |- istp B[^1]

- `guardEq A A' B B'`

      G |- eqtp (guard A B) (guard A' B')
      >>
      G |- iff A A'
      G, A |- eqtp B[^1] B'[^1]

- `guardFormUniv A B I`

      G |- of (univ I) (guard A B)
      >>
      G |- of (univ I) A
      G, A |- of (univ I[^1]) B[^1]

- `guardEqUniv A A' B B' I`

      G |- eq (univ I) (guard A B) (guard A' B')
      >>
      G |- of (univ I) A
      G |- of (univ I) A'
      G |- iff A A'
      G, A |- eq (univ I[^1]) B[^1] B'[^1]

- `guardIntroOf A B M`

      G |- of (guard A B) M
      >>
      G |- istp A
      G, A |- of B[^1] M[^1]

- `guardIntroEq A B M N`

      G |- eq (guard A B) M N
      >>
      G |- istp A
      G, A |- eq B[^1] M[^1] N[^1]

- `guardIntro A B`

      G |- guard A B ext M[() . id]
      >>
      G |- istp A
      G, (hidden) A |- B[^1] ext M

- `guardElimOf A B M`

      G |- of B M
      >>
      G |- of (guard A B) M
      G |- A

- `guardElimEq A B M N`

      G |- eq B M N
      >>
      G |- eq (guard A B) M N
      G |- A

- `guardElim A B`

      G |- B ext M
      >>
      G |- guard A B ext M
      G |- A

- `guardSatEq A B`

      G |- eqtp B (guard A B)
      >>
      G |- istp B
      G |- A

- `guardSub A A' B B'`

      G |- subtype (guard A B) (guard A' B')
      >>
      G |- arrow A' A
      G |- istp A
      G, A' |- subtype B[^1] B'[^1]
      G, A |- istp B[^1]

- `guardSubIntro A B C`

      G |- subtype C (guard A B)
      >>
      G |- istp A
      G, A |- subtype C[^1] B[^1]
      G |- istp C


### Strong sums

- `existsForm A B`

      G |- istp (exists A (fn . B))
      >>
      G |- istp A
      G, A |- istp B

- `existsEq A A' B B'`

      G |- eqtp (exists A (fn . B)) (exists A' (fn . B'))
      >>
      G |- eqtp A A'
      G, A |- eqtp B B'

- `existsFormUniv A B I`

      G |- of (univ I) (exists A (fn . B))
      >>
      G |- of (univ I) A
      G, A |- of (univ I[^1]) B

- `existsEqUniv A A' B B' I`

      G |- eq (univ I) (exists A (fn . B)) (exists A' (fn . B'))
      >>
      G |- eq (univ I) A A'
      G, A |- eq (univ I[^1]) B B'

- `existsSub A A' B B'`

      G |- subtype (exists A (fn . B)) (exists A' (fn . B'))
      >>
      G |- subtype A A'
      G, A |- subtype B B'
      G, A' |- istp B'

- `existsIntroOf A B M N`

      G |- of (exists A (fn . B)) (M , N)
      >>
      G, A |- istp B
      G |- of A M
      G |- of B[M . id] N

- `existsIntroEq A B M M' N N'`

      G |- eq (exists A (fn . B)) (M , N) (M' , N')
      >>
      G, A |- istp B
      G |- eq A M M'
      G |- eq B[M . id] N N'

- `existsIntro A B M`

      G |- exists A (fn . B) ext (M , N)
      >>
      G, A |- istp B
      G |- of A M
      G |- B[M . id] ext N

- `existsElim1Of A B M`

      G |- of A (M #1)
      >>
      G |- of (exists A (fn . B)) M

- `existsElim1Eq A B M N`

      G |- eq A (M #1) (N #1)
      >>
      G |- eq (exists A (fn . B)) M N

- `existsElim1 A B`

      G |- A ext M #1
      >>
      G |- exists A (fn . B) ext M

- `existsElim2Of A B M`

      G |- of B[M #1 . id] (M #2)
      >>
      G |- of (exists A (fn . B)) M

- `existsElim2Eq A B M N`

      G |- eq B[M #1 . id] (M #2) (N #2)
      >>
      G |- eq (exists A (fn . B)) M N

- `existsEta A B M`

      G |- eq (exists A (fn . B)) M (M #1 , M #2)
      >>
      G |- of (exists A (fn . B)) M

- `existsExt A B M N`

      G |- eq (exists A (fn . B)) M N
      >>
      G |- of (exists A (fn . B)) M
      G |- of (exists A (fn . B)) N
      G |- eq A (M #1) (N #1)
      G |- eq B[M #1 . id] (M #2) (N #2)

- `existsLeft n A B C`

      G1, (exists A (fn . B)), G2 |- C ext M[under_n (0 #2 . 0 #1 . ^1)]
      >>
      G1, A, B, G2[(1 , 0) . ^2] |- C[under_n ((1 , 0) . ^2)] ext M

- `existsFormInv1 A B`

      G |- istp A
      >>
      G |- istp (exists A (fn . B))

- `existsFormInv2 A B M`

      G |- istp B[M . id]
      >>
      G |- istp (exists A (fn . B))
      G |- of A M

- `existsFormInv2Eq A B M N`

      G |- eqtp B[M . id] B[N . id]
      >>
      G |- istp (exists A (fn . B))
      G |- eq A M N


### Products

- `prodKind I K L`

      G |- of (kind I) (prod K L)
      >>
      G |- of (kind I) K
      G |- of (kind I) L

- `prodKindEq I K K' L L'`

      G |- eq (kind I) (prod K L) (prod K' L')
      >>
      G |- eq (kind I) K K'
      G |- eq (kind I) L L'

- `prodForm A B`

      G |- istp (prod A B)
      >>
      G |- istp A
      G |- istp B

- `prodEq A A' B B'`

      G |- eqtp (prod A B) (prod A' B')
      >>
      G |- eqtp A A'
      G |- eqtp B B'

- `prodFormUniv A B I`

      G |- of (univ I) (prod A B)
      >>
      G |- of (univ I) A
      G |- of (univ I) B

- `prodEqUniv A A' B B' I`

      G |- eq (univ I) (prod A B) (prod A' B')
      >>
      G |- eq (univ I) A A'
      G |- eq (univ I) B B'

- `prodExistsEq A A' B B'`

      G |- eqtp (prod A B) (exists A' (fn . B'[^1]))
      >>
      G |- eqtp A A'
      G |- eqtp B B'

- `prodExistsEqUniv A A' B B' I`

      G |- eq (univ I) (prod A B) (exists A' (fn . B'[^1]))
      >>
      G |- eq (univ I) A A'
      G |- eq (univ I) B B'

- `prodSub A A' B B'`

      G |- subtype (prod A B) (prod A' B')
      >>
      G |- subtype A A'
      G |- subtype B B'

- `prodExistsSub A A' B B'`

      G |- subtype (prod A B) (exists A' (fn . B'))
      >>
      G |- subtype A A'
      G, A |- subtype B[^1] B'
      G |- istp B
      G, A' |- istp B'

- `existsProdSub A A' B B'`

      G |- subtype (exists A (fn . B)) (prod A' B')
      >>
      G |- subtype A A'
      G, A |- subtype B B'[^1]
      G |- istp B'

- `prodIntroOf A B M N`

      G |- of (prod A B) (M , N)
      >>
      G |- of A M
      G |- of B N

- `prodIntroEq A B M M' N N'`

      G |- eq (prod A B) (M , N) (M' , N')
      >>
      G |- eq A M M'
      G |- eq B N N'

- `prodIntro A B`

      G |- prod A B ext (M , N)
      >>
      G |- A ext M
      G |- B ext N

- `prodElim1Of A B M`

      G |- of A (M #1)
      >>
      G |- of (prod A B) M

- `prodElim1Eq A B M N`

      G |- eq A (M #1) (N #1)
      >>
      G |- eq (prod A B) M N

- `prodElim1 A B`

      G |- A ext M #1
      >>
      G |- prod A B ext M

- `prodElim2Of A B M`

      G |- of B (M #2)
      >>
      G |- of (prod A B) M

- `prodElim2Eq A B M N`

      G |- eq B (M #2) (N #2)
      >>
      G |- eq (prod A B) M N

- `prodElim2 A B`

      G |- B ext M #2
      >>
      G |- prod A B ext M

- `prodEta A B M`

      G |- eq (prod A B) M (M #1 , M #2)
      >>
      G |- of (prod A B) M

- `prodExt A B M N`

      G |- eq (prod A B) M N
      >>
      G |- of (prod A B) M
      G |- of (prod A B) N
      G |- eq A (M #1) (N #1)
      G |- eq B (M #2) (N #2)

- `prodLeft n A B C`

      G1, (prod A B), G2 |- C ext M[under_n (0 #2 . 0 #1 . ^1)]
      >>
      G1, A, B[^1], G2[(1 , 0) . ^2] |- C[under_n ((1 , 0) . ^2)] ext M

- `prodFormInv1 A B`

      G |- istp A
      >>
      G |- istp (prod A B)

- `prodFormInv2 A B`

      G |- istp B
      >>
      G |- istp (prod A B)
      G |- A


### Semi-dependent products

- `dprodForm A B`

      G |- istp (dprod A B)
      >>
      G |- istp A
      G, A |- istp B[^1]

- `dprodEq A A' B B'`

      G |- eqtp (dprod A B) (dprod A' B')
      >>
      G |- eqtp A A'
      G, A |- eqtp B[^1] B'[^1]

- `dprodFormUniv A B I`

      G |- of (univ I) (dprod A B)
      >>
      G |- of (univ I) A
      G, A |- of (univ I[^1]) B[^1]

- `dprodEqUniv A A' B B' I`

      G |- eq (univ I) (dprod A B) (dprod A' B')
      >>
      G |- eq (univ I) A A'
      G, A |- eq (univ I[^1]) B[^1] B'[^1]

- `dprodExistsEq A A' B B'`

      G |- eqtp (dprod A B) (exists A' (fn . B'))
      >>
      G |- eqtp A A'
      G, A |- eqtp B[^1] B'

- `dprodExistsEqUniv A A' B B' I`

      G |- eq (univ I) (dprod A B) (exists A' (fn . B'))
      >>
      G |- eq (univ I) A A'
      G, A |- eq (univ I[^1]) B[^1] B'

- `prodDprodEq A A' B B'`

      G |- eqtp (prod A B) (dprod A' B')
      >>
      G |- eqtp A A'
      G |- eqtp B B'

- `prodDprodEqUniv A A' B B' I`

      G |- eq (univ I) (prod A B) (dprod A' B')
      >>
      G |- eq (univ I) A A'
      G |- eq (univ I) B B'

- `dprodSub A A' B B'`

      G |- subtype (dprod A B) (dprod A' B')
      >>
      G |- subtype A A'
      G, A |- subtype B[^1] B'[^1]
      G, A' |- istp B'[^1]

- `dprodExistsSub A A' B B'`

      G |- subtype (dprod A B) (exists A' (fn . B'))
      >>
      G |- subtype A A'
      G, A |- subtype B[^1] B'
      G, A' |- istp B'

- `existsDprodSub A A' B B'`

      G |- subtype (exists A (fn . B)) (dprod A' B')
      >>
      G |- subtype A A'
      G, A |- subtype B B'[^1]
      G, A' |- istp B'[^1]

- `dprodProdSub A A' B B'`

      G |- subtype (dprod A B) (prod A' B')
      >>
      G |- subtype A A'
      G, A |- subtype B[^1] B'[^1]
      G |- istp B'

- `prodDprodSub A A' B B'`

      G |- subtype (prod A B) (dprod A' B')
      >>
      G |- subtype A A'
      G, A |- subtype B[^1] B'[^1]
      G |- istp B
      G, A' |- istp B'[^1]

- `dprodIntroOf A B M N`

      G |- of (dprod A B) (M , N)
      >>
      G |- of A M
      G |- of B N

- `dprodIntroEq A B M M' N N'`

      G |- eq (dprod A B) (M , N) (M' , N')
      >>
      G |- eq A M M'
      G |- eq B N N'

- `dprodIntro A B`

      G |- dprod A B ext (M , N)
      >>
      G |- A ext M
      G |- B ext N

- `dprodElim1Of A B M`

      G |- of A (M #1)
      >>
      G |- of (dprod A B) M

- `dprodElim1Eq A B M N`

      G |- eq A (M #1) (N #1)
      >>
      G |- eq (dprod A B) M N

- `dprodElim1 A B`

      G |- A ext M #1
      >>
      G |- dprod A B ext M

- `dprodElim2Of A B M`

      G |- of B (M #2)
      >>
      G |- of (dprod A B) M

- `dprodElim2Eq A B M N`

      G |- eq B (M #2) (N #2)
      >>
      G |- eq (dprod A B) M N

- `dprodElim2 A B`

      G |- B ext M #2
      >>
      G |- dprod A B ext M

- `dprodEta A B M`

      G |- eq (dprod A B) M (M #1 , M #2)
      >>
      G |- of (dprod A B) M

- `dprodExt A B M N`

      G |- eq (dprod A B) M N
      >>
      G |- of (dprod A B) M
      G |- of (dprod A B) N
      G |- eq A (M #1) (N #1)
      G |- eq B (M #2) (N #2)

- `dprodLeft n A B C`

      G1, (dprod A B), G2 |- C ext M[under_n (0 #2 . 0 #1 . ^1)]
      >>
      G1, A, B[^1], G2[(1 , 0) . ^2] |- C[under_n ((1 , 0) . ^2)] ext M

- `dprodFormInv1 A B`

      G |- istp A
      >>
      G |- istp (dprod A B)

- `dprodFormInv2 A B M`

      G |- istp B
      >>
      G |- istp (dprod A B)
      G |- of A M


### Union Types

- `unionForm A B`

      G |- istp (union A (fn . B))
      >>
      G |- istp A
      G, A |- istp B

- `unionEq A A' B B'`

      G |- eqtp (union A (fn . B)) (union A' (fn . B'))
      >>
      G |- eqtp A A'
      G, A |- eqtp B B'

- `unionFormUniv A B I`

      G |- of (univ I) (union A (fn . B))
      >>
      G |- of (univ I) A
      G, A |- of (univ I[^1]) B

- `unionEqUniv A A' B B' I`

      G |- eq (univ I) (union A (fn . B)) (union A' (fn . B'))
      >>
      G |- eq (univ I) A A'
      G, A |- eq (univ I[^1]) B B'

- `unionSub A A' B B'`

      G |- subtype (union A (fn . B)) (union A' (fn . B'))
      >>
      G |- subtype A A'
      G, A |- subtype B B'
      G, A' |- istp B'

- `unionIntroOf A B M N`

      G |- of (union A (fn . B)) N
      >>
      G, A |- istp B
      G |- of A M
      G |- of B[M . id] N

- `unionIntroEq A B M N N'`

      G |- eq (union A (fn . B)) N N'
      >>
      G, A |- istp B
      G |- of A M
      G |- eq B[M . id] N N'

- `unionIntro A B M`

      G |- union A (fn . B) ext N
      >>
      G, A |- istp B
      G |- of A M
      G |- B[M . id] ext N

- `unionElimOf A B C M P`

      G |- of C P[M . id]
      >>
      G, A, B |- of C[^2] P[0 . ^2]
      G |- of (union A (fn . B)) M

- `unionElimEq A B C M N P Q`

      G |- eq C P[M . id] Q[N . id]
      >>
      G, A, B |- eq C[^2] P[0 . ^2] Q[0 . ^2]
      G |- eq (union A (fn . B)) M N

- `unionElim A B C M`

      G |- C ext P[M . () . id]
      >>
      G, (hidden) A, B |- C[^2] ext P
      G |- of (union A (fn . B)) M

- `unionElimOfDep A B C M P`

      G |- of C[M . id] P[M . id]
      >>
      G, A, B |- of C[0 . ^2] P[0 . ^2]
      G |- of (union A (fn . B)) M

- `unionElimEqDep A B C M N P Q`

      G |- eq C[M . id] P[M . id] Q[N . id]
      >>
      G, A, B |- eq C[0 . ^2] P[0 . ^2] Q[0 . ^2]
      G |- eq (union A (fn . B)) M N

- `unionElimDep A B C M`

      G |- C[M . id] ext P[M . () . id]
      >>
      G, (hidden) A, B |- C[0 . ^2] ext P
      G |- of (union A (fn . B)) M

- `unionElimIstype A B C M`

      G |- istp C[M . id]
      >>
      G, A, B |- istp C[0 . ^2]
      G |- of (union A (fn . B)) M

- `unionElimEqtype A B C D M N`

      G |- eqtp C[M . id] D[N . id]
      >>
      G, A, B |- eqtp C[0 . ^2] D[0 . ^2]
      G |- eq (union A (fn . B)) M N


### Coguarded types

- `coguardForm A B`

      G |- istp (coguard A B)
      >>
      G |- istp A
      G, A |- istp B[^1]

- `coguardEq A A' B B'`

      G |- eqtp (coguard A B) (coguard A' B')
      >>
      G |- iff A A'
      G, A |- eqtp B[^1] B'[^1]

- `coguardFormUniv A B I`

      G |- of (univ I) (coguard A B)
      >>
      G |- of (univ I) A
      G, A |- of (univ I[^1]) B[^1]

- `coguardEqUniv A A' B B' I`

      G |- eq (univ I) (coguard A B) (coguard A' B')
      >>
      G |- of (univ I) A
      G |- of (univ I) A'
      G |- iff A A'
      G, A |- eq (univ I[^1]) B[^1] B'[^1]

- `coguardIntroEq A B M N`

      G |- eq (coguard A B) M N
      >>
      G |- A
      G |- eq B M N

- `coguardIntroOf A B M`

      G |- of (coguard A B) M
      >>
      G |- A
      G |- of B M

- `coguardIntroOfSquash A B M`

      G |- of (coguard A B) M
      >>
      G |- istp A
      G |- squash A
      G |- of B M

- `coguardIntro A B`

      G |- coguard A B ext M
      >>
      G |- A
      G |- B ext M

- `coguardElim1 A B`

      G |- squash A
      >>
      G |- istp A
      G |- coguard A B

- `coguardElim2Eq A B M N`

      G |- eq B M N
      >>
      G |- eq (coguard A B) M N

- `coguardElim2Of A B M`

      G |- of B M
      >>
      G |- of (coguard A B) M

- `coguardElim2 A B`

      G |- B ext M
      >>
      G |- coguard A B ext M

- `coguardLeft n A B C`

      G1, (coguard A B), G2 |- C ext M[under_n (() . id)]
      >>
      G1 |- istp A
      G1, B, (hidden) A[^1], G2[^1] |- C[under_n (^1)] ext M

- `coguardSatEq A B`

      G |- eqtp B (coguard A B)
      >>
      G |- istp B
      G |- A

- `coguardSub A A' B B'`

      G |- subtype (coguard A B) (coguard A' B')
      >>
      G |- arrow A A'
      G |- istp A'
      G, A |- subtype B[^1] B'[^1]
      G, A' |- istp B'[^1]

- `coguardSubElim A B C`

      G |- subtype (coguard A B) C
      >>
      G |- istp A
      G, A |- subtype B[^1] C[^1]
      G |- istp C


### Disjoint sums

- `sumForm A B`

      G |- istp (sum A B)
      >>
      G |- istp A
      G |- istp B

- `sumEq A A' B B'`

      G |- eqtp (sum A B) (sum A' B')
      >>
      G |- eqtp A A'
      G |- eqtp B B'

- `sumFormUniv A B I`

      G |- of (univ I) (sum A B)
      >>
      G |- of (univ I) A
      G |- of (univ I) B

- `sumEqUniv A A' B B' I`

      G |- eq (univ I) (sum A B) (sum A' B')
      >>
      G |- eq (univ I) A A'
      G |- eq (univ I) B B'

- `sumSub A A' B B'`

      G |- subtype (sum A B) (sum A' B')
      >>
      G |- subtype A A'
      G |- subtype B B'

- `sumIntro1Of A B M`

      G |- of (sum A B) (inl M)
      >>
      G |- istp B
      G |- of A M

- `sumIntro1Eq A B M N`

      G |- eq (sum A B) (inl M) (inl N)
      >>
      G |- istp B
      G |- eq A M N

- `sumIntro1 A B`

      G |- sum A B ext inl M
      >>
      G |- istp B
      G |- A ext M

- `sumIntro2Of A B M`

      G |- of (sum A B) (inr M)
      >>
      G |- istp A
      G |- of B M

- `sumIntro2Eq A B M N`

      G |- eq (sum A B) (inr M) (inr N)
      >>
      G |- istp A
      G |- eq B M N

- `sumIntro2 A B`

      G |- sum A B ext inr M
      >>
      G |- istp A
      G |- B ext M

- `sumElimOf A B C M P R`

      G |- of C[M . id] (sum_case M (fn . P) (fn . R))
      >>
      G |- of (sum A B) M
      G, A |- of C[inl 0 . ^1] P
      G, B |- of C[inr 0 . ^1] R

- `sumElimOfNondep A B C M P R`

      G |- of C (sum_case M (fn . P) (fn . R))
      >>
      G |- of (sum A B) M
      G, A |- of C[^1] P
      G, B |- of C[^1] R

- `sumElimEq A B C M N P Q R S`

      G |- eq C[M . id] (sum_case M (fn . P) (fn . R)) (sum_case N (fn . Q) (fn . S))
      >>
      G |- eq (sum A B) M N
      G, A |- eq C[inl 0 . ^1] P Q
      G, B |- eq C[inr 0 . ^1] R S

- `sumElim A B C M`

      G |- C[M . id] ext sum_case M (fn . P) (fn . R)
      >>
      G |- of (sum A B) M
      G, A |- C[inl 0 . ^1] ext P
      G, B |- C[inr 0 . ^1] ext R

- `sumElimNondep A B C`

      G |- C ext sum_case M (fn . P) (fn . R)
      >>
      G |- sum A B ext M
      G, A |- C[^1] ext P
      G, B |- C[^1] ext R

- `sumElimIstype A B C E M`

      G |- istp (sum_case M (fn . C) (fn . E))
      >>
      G |- of (sum A B) M
      G, A |- istp C
      G, B |- istp E

- `sumElimEqtype A B C D E F M N`

      G |- eqtp (sum_case M (fn . C) (fn . E)) (sum_case N (fn . D) (fn . F))
      >>
      G |- eq (sum A B) M N
      G, A |- eqtp C D
      G, B |- eqtp E F

- `sumLeft n A B C`

      G1, (sum A B), G2 |- C ext sum_case n (fn . M[1 .. n . 0 . ^n+1]) (fn . N[1 .. n . 0 . ^n+1])
      >>
      G1, A, G2[inl 0 . ^1] |- C[under_n (inl 0 . ^1)] ext M
      G1, B, G2[inr 0 . ^1] |- C[under_n (inr 0 . ^1)] ext N

- `sumContradiction A B C M N`

      G |- C
      >>
      G |- eq (sum A B) (inl M) (inr N)

- `sumInjection1 A B M N`

      G |- eq A M N
      >>
      G |- eq (sum A B) (inl M) (inl N)

- `sumInjection2 A B M N`

      G |- eq B M N
      >>
      G |- eq (sum A B) (inr M) (inr N)

- `sum_caseType`

      G |- of (intersect level (fn . intersect (univ 0) (fn . intersect (univ 1) (fn . intersect (univ 2) (fn . arrow (sum 2 1) (arrow (arrow 2 0) (arrow (arrow 1 0) 0))))))) sum_case

- `sumFormInv1 A B`

      G |- istp A
      >>
      G |- istp (sum A B)

- `sumFormInv2 A B`

      G |- istp B
      >>
      G |- istp (sum A B)


### Future modality

- `futureKind I K`

      G |- of (kind I) (future K)
      >>
      G |- of level I
      promote(G) |- of (kind I) K

- `futureKindEq I K L`

      G |- eq (kind I) (future K) (future L)
      >>
      G |- of level I
      promote(G) |- eq (kind I) K L

- `futureForm A`

      G |- istp (future A)
      >>
      promote(G) |- istp A

- `futureEq A B`

      G |- eqtp (future A) (future B)
      >>
      promote(G) |- eqtp A B

- `futureFormUniv A I`

      G |- of (univ I) (future A)
      >>
      G |- of level I
      promote(G) |- of (univ I) A

- `futureEqUniv A B I`

      G |- eq (univ I) (future A) (future B)
      >>
      G |- of level I
      promote(G) |- eq (univ I) A B

- `futureSub A B`

      G |- subtype (future A) (future B)
      >>
      promote(G) |- subtype A B

- `futureIntroOf A M`

      G |- of (future A) (next M)
      >>
      promote(G) |- of A M

- `futureIntroEq A M N`

      G |- eq (future A) (next M) (next N)
      >>
      promote(G) |- eq A M N

- `futureIntro A`

      G |- future A ext next M
      >>
      promote(G) |- A ext M

- `futureElimOf A B M P`

      G |- of B[M #prev . id] P[M #prev . id]
      >>
      promote(G) |- istp A
      G |- of (future A) M
      G, (later) A |- of B P

- `futureElimOfLetnext A B M P`

      G |- of B[M #prev . id] (letnext M (fn . P))
      >>
      promote(G) |- istp A
      G |- of (future A) M
      G, (later) A |- of B P

- `futureElimOfLetnextNondep A B M P`

      G |- of B (letnext M (fn . P))
      >>
      promote(G) |- istp A
      G |- of (future A) M
      G, (later) A |- of B[^1] P

- `futureElimEq A B M N P Q`

      G |- eq B[M #prev . id] P[M #prev . id] Q[N #prev . id]
      >>
      promote(G) |- istp A
      G |- eq (future A) M N
      G, (later) A |- eq B P Q

- `futureElim A B M`

      G |- B[M #prev . id] ext P[M #prev . id]
      >>
      promote(G) |- istp A
      G |- of (future A) M
      G, (later) A |- B ext P

- `futureElimIstype A B M`

      G |- istp B[M #prev . id]
      >>
      promote(G) |- istp A
      G |- of (future A) M
      G, (later) A |- istp B

- `futureElimIstypeLetnext A B M`

      G |- istp (letnext M (fn . B))
      >>
      promote(G) |- istp A
      G |- of (future A) M
      G, (later) A |- istp B

- `futureElimEqtype A B C M N`

      G |- eqtp B[M #prev . id] C[N #prev . id]
      >>
      promote(G) |- istp A
      G |- eq (future A) M N
      G, (later) A |- eqtp B C

- `futureEta A M`

      G |- eq (future A) M (next (M #prev))
      >>
      G |- of (future A) M

- `futureExt A M N`

      G |- eq (future A) M N
      >>
      G |- of (future A) M
      G |- of (future A) N
      promote(G) |- eq A (M #prev) (N #prev)

- `futureLeft n A B`

      G1, (future A), G2 |- B ext M[under_n (0 #prev . ^1)]
      >>
      promote(G1) |- istp A
      G1, (later) A, G2[next 0 . ^1] |- B[under_n (next 0 . ^1)] ext M

- `futureLeftHidden n A B`

      G1, (hidden) (future A), G2 |- B ext M[under_n (() . ^1)]
      >>
      promote(G1) |- istp A
      G1, (later hidden) A, G2[next 0 . ^1] |- B[under_n (next 0 . ^1)] ext M

- `futureInjection A M N`

      G |- future (eq A M N) ext next ()
      >>
      promote(G) |- istp A
      G |- eq (future A) (next M) (next N)

- `squashFutureSwap A`

      G |- squash (future A)
      >>
      promote(G) |- istp A
      G |- future (squash A)

- `isquashFutureSwap A`

      G |- isquash (future A)
      >>
      promote(G) |- istp A
      G |- future (isquash A)

- `futureSquashSwap A`

      G |- future (squash A) ext next ()
      >>
      promote(G) |- istp A
      G |- squash (future A)

- `futureIsquashSwap A`

      G |- future (isquash A) ext next ()
      >>
      promote(G) |- istp A
      G |- isquash (future A)


### Future functions

- `forallfutForm A B`

      G |- istp (forallfut A (fn . B))
      >>
      promote(G) |- istp A
      G, (later) A |- istp B

- `forallfutEq A A' B B'`

      G |- eqtp (forallfut A (fn . B)) (forallfut A' (fn . B'))
      >>
      promote(G) |- eqtp A A'
      G, (later) A |- eqtp B B'

- `forallfutFormUniv A B I`

      G |- of (univ I) (forallfut A (fn . B))
      >>
      G |- of level I
      promote(G) |- of (univ I) A
      G, (later) A |- of (univ I[^1]) B

- `forallfutEqUniv A A' B B' I`

      G |- eq (univ I) (forallfut A (fn . B)) (forallfut A' (fn . B'))
      >>
      G |- of level I
      promote(G) |- eq (univ I) A A'
      G, (later) A |- eq (univ I[^1]) B B'

- `forallfutSub A A' B B'`

      G |- subtype (forallfut A (fn . B)) (forallfut A' (fn . B'))
      >>
      promote(G) |- subtype A' A
      G, (later) A' |- subtype B B'
      G, (later) A |- istp B

- `forallfutForallVoidSub A B B'`

      G |- subtype (forallfut A (fn . B)) (forall void (fn . B'))
      >>
      promote(G) |- istp A
      G, (later) A |- istp B

- `forallfutIntroOf A B M`

      G |- of (forallfut A (fn . B)) (fn . M)
      >>
      promote(G) |- istp A
      G, (later) A |- of B M

- `forallfutIntroEq A B M N`

      G |- eq (forallfut A (fn . B)) (fn . M) (fn . N)
      >>
      promote(G) |- istp A
      G, (later) A |- eq B M N

- `forallfutIntro A B`

      G |- forallfut A (fn . B) ext fn . M
      >>
      promote(G) |- istp A
      G, (later) A |- B ext M

- `forallfutElimOf A B M P`

      G |- of B[P . id] (M P)
      >>
      G |- of (forallfut A (fn . B)) M
      promote(G) |- of A P

- `forallfutElimEq A B M N P Q`

      G |- eq B[P . id] (M P) (N Q)
      >>
      G |- eq (forallfut A (fn . B)) M N
      promote(G) |- eq A P Q

- `forallfutElim A B P`

      G |- B[P . id] ext M P
      >>
      G |- forallfut A (fn . B) ext M
      promote(G) |- of A P

- `forallfutExt A B M N`

      G |- eq (forallfut A (fn . B)) M N
      >>
      promote(G) |- istp A
      G |- of (forallfut A (fn . B)) M
      G |- of (forallfut A (fn . B)) N
      G, (later) A |- eq B (M[^1] 0) (N[^1] 0)

- `forallfutExt' A A' A'' B B' B'' M N`

      G |- eq (forallfut A (fn . B)) M N
      >>
      promote(G) |- istp A
      G |- of (forall A' (fn . B')) M
      G |- of (forall A'' (fn . B'')) N
      G, (later) A |- eq B (M[^1] 0) (N[^1] 0)

- `forallfutOfExt A A' B B' M`

      G |- of (forallfut A (fn . B)) M
      >>
      promote(G) |- istp A
      G |- of (forall A' (fn . B')) M
      G, (later) A |- of B (M[^1] 0)


### Future intersect

- `intersectfutForm A B`

      G |- istp (intersectfut A (fn . B))
      >>
      promote(G) |- istp A
      G, (later) A |- istp B

- `intersectfutEq A A' B B'`

      G |- eqtp (intersectfut A (fn . B)) (intersectfut A' (fn . B'))
      >>
      promote(G) |- eqtp A A'
      G, (later) A |- eqtp B B'

- `intersectfutFormUniv A B I`

      G |- of (univ I) (intersectfut A (fn . B))
      >>
      G |- of level I
      promote(G) |- of (univ I) A
      G, (later) A |- of (univ I[^1]) B

- `intersectfutEqUniv A A' B B' I`

      G |- eq (univ I) (intersectfut A (fn . B)) (intersectfut A' (fn . B'))
      >>
      G |- of level I
      promote(G) |- eq (univ I) A A'
      G, (later) A |- eq (univ I[^1]) B B'

- `intersectfutSub A A' B B'`

      G |- subtype (intersectfut A (fn . B)) (intersectfut A' (fn . B'))
      >>
      promote(G) |- subtype A' A
      G, (later) A' |- subtype B B'
      G, (later) A |- istp B

- `intersectfutIntroOf A B M`

      G |- of (intersectfut A (fn . B)) M
      >>
      promote(G) |- istp A
      G, (later) A |- of B M[^1]

- `intersectfutIntroEq A B M N`

      G |- eq (intersectfut A (fn . B)) M N
      >>
      promote(G) |- istp A
      G, (later) A |- eq B M[^1] N[^1]

- `intersectfutIntro A B`

      G |- intersectfut A (fn . B) ext M[() . id]
      >>
      promote(G) |- istp A
      G, (later hidden) A |- B ext M

- `intersectfutElimOf A B M P`

      G |- of B[P . id] M
      >>
      G |- of (intersectfut A (fn . B)) M
      promote(G) |- of A P

- `intersectfutElimEq A B M N P`

      G |- eq B[P . id] M N
      >>
      G |- eq (intersectfut A (fn . B)) M N
      promote(G) |- of A P

- `intersectfutElim A B P`

      G |- B[P . id] ext M
      >>
      G |- intersectfut A (fn . B) ext M
      promote(G) |- of A P


### Future parametric

- `parametricfutForm A B`

      G |- istp (parametricfut A (fn . B))
      >>
      promote(G) |- istp A
      G, (later) A |- istp B

- `parametricfutEq A A' B B'`

      G |- eqtp (parametricfut A (fn . B)) (parametricfut A' (fn . B'))
      >>
      promote(G) |- eqtp A A'
      G, (later) A |- eqtp B B'

- `parametricfutFormUniv A B I`

      G |- of (univ I) (parametricfut A (fn . B))
      >>
      G |- of level I
      promote(G) |- of (univ I) A
      G, (later) A |- of (univ I[^1]) B

- `parametricfutEqUniv A A' B B' I`

      G |- eq (univ I) (parametricfut A (fn . B)) (parametricfut A' (fn . B'))
      >>
      G |- of level I
      promote(G) |- eq (univ I) A A'
      G, (later) A |- eq (univ I[^1]) B B'

- `parametricfutSub A A' B B'`

      G |- subtype (parametricfut A (fn . B)) (parametricfut A' (fn . B'))
      >>
      promote(G) |- subtype A' A
      G, (later) A' |- subtype B B'
      G, (later) A |- istp B

- `parametricfutIntroOf A B M`

      G |- of (parametricfut A (fn . B)) (fn . M)
      >>
      promote(G) |- istp A
      G |- irrelevant (fn . M)
      G, (later) A |- of B M

- `parametricfutIntroEq A B M N`

      G |- eq (parametricfut A (fn . B)) (fn . M) (fn . N)
      >>
      promote(G) |- istp A
      G |- irrelevant (fn . M)
      G |- irrelevant (fn . N)
      G, (later) A |- eq B M N

- `parametricfutIntro A B`

      G |- parametricfut A (fn . B) ext fn . M
      >>
      promote(G) |- istp A
      G, (later hidden) A |- B ext M

- `parametricfutElimOf A B M P`

      G |- of B[P . id] (paramapp M P)
      >>
      G |- of (parametricfut A (fn . B)) M
      promote(G) |- of A P

- `parametricfutElimEq A B M N P Q`

      G |- eq B[P . id] (paramapp M P) (paramapp N Q)
      >>
      G |- eq (parametricfut A (fn . B)) M N
      promote(G) |- eq A P Q

- `parametricfutElim A B P`

      G |- B[P . id] ext paramapp M P
      >>
      G |- parametricfut A (fn . B) ext M
      promote(G) |- of A P

- `parametricfutElim' A B P`

      G |- B[P . id] ext paramapp M unavailable
      >>
      G |- parametricfut A (fn . B) ext M
      promote(G) |- of A P

- `parametricfutExt A B M N`

      G |- eq (parametricfut A (fn . B)) M N
      >>
      promote(G) |- istp A
      G |- of (parametricfut A (fn . B)) M
      G |- of (parametricfut A (fn . B)) N
      G, (later) A |- eq B (paramapp M[^1] 0) (paramapp N[^1] 0)

- `parametricfutExt' A A' A'' B B' B'' M N`

      G |- eq (parametricfut A (fn . B)) M N
      >>
      promote(G) |- istp A
      G |- of (parametric A' (fn . B')) M
      G |- of (parametric A'' (fn . B'')) N
      G, (later) A |- eq B (paramapp M[^1] 0) (paramapp N[^1] 0)

- `parametricfutOfExt A A' B B' M`

      G |- of (parametricfut A (fn . B)) M
      >>
      promote(G) |- istp A
      G |- of (parametric A' (fn . B')) M
      G, (later) A |- of B (paramapp M[^1] 0)


### Recursive types

- `recKind I K`

      G |- of (kind I) (rec (fn . K))
      >>
      G |- of level I
      G, (later) (kind I) |- of (kind I[^1]) K

- `recKindEq I K L`

      G |- eq (kind I) (rec (fn . K)) (rec (fn . L))
      >>
      G |- of level I
      G, (later) (kind I) |- eq (kind I[^1]) K L

- `recForm A`

      G |- istp (rec (fn . A))
      >>
      G, (later) type |- istp A

- `recEq A B`

      G |- eqtp (rec (fn . A)) (rec (fn . B))
      >>
      G, (later) type |- eqtp A B

- `recFormUniv A I`

      G |- of (univ I) (rec (fn . A))
      >>
      G |- of level I
      G, (later) (univ I) |- of (univ I[^1]) A

- `recEqUniv A B I`

      G |- eq (univ I) (rec (fn . A)) (rec (fn . B))
      >>
      G |- of level I
      G, (later) (univ I) |- eq (univ I[^1]) A B

- `recUnroll A`

      G |- eqtp (rec (fn . A)) A[rec (fn . A) . id]
      >>
      G, (later) type |- istp A

- `recUnrollUniv A I`

      G |- eq (univ I) (rec (fn . A)) A[rec (fn . A) . id]
      >>
      G |- of level I
      G, (later) (univ I) |- of (univ I[^1]) A

- `recBisimilar A B`

      G |- eqtp B (rec (fn . A))
      >>
      G, (later) type |- istp A
      G |- eqtp B A[B . id]


### Inductive types

- `muForm A`

      G |- istp (mu (fn . A))
      >>
      G, type |- istp A
      G |- positive (fn . A)

- `muEq A B`

      G |- eqtp (mu (fn . A)) (mu (fn . B))
      >>
      G, type |- eqtp A B
      G |- positive (fn . A)
      G |- positive (fn . B)

- `muFormUniv A I`

      G |- of (univ I) (mu (fn . A))
      >>
      G |- of level I
      G, (univ I) |- of (univ I[^1]) A
      G |- positive (fn . A)

- `muEqUniv A B I`

      G |- eq (univ I) (mu (fn . A)) (mu (fn . B))
      >>
      G |- of level I
      G, (univ I) |- eq (univ I[^1]) A B
      G |- positive (fn . A)
      G |- positive (fn . B)

- `muUnroll A`

      G |- eeqtp (mu (fn . A)) A[mu (fn . A) . id] ext (() , ())
      >>
      G, type |- istp A
      G |- positive (fn . A)

- `muUnrollUniv A I`

      G |- eeqtp (mu (fn . A)) A[mu (fn . A) . id] ext (() , ())
      >>
      G |- of level I
      G, (univ I) |- of (univ I[^1]) A
      G |- positive (fn . A)

- `muInd A B M`

      G |- B[M . id] ext fix (fn . fn . N[1 . () . 0 . () . ^2]) M
      >>
      G, type |- istp A
      G |- positive (fn . A)
      G, (hidden) type, A, (subtype 1 (mu (fn . A[0 . ^3]))), (forall 2 (fn . B[0 . ^4])) |- B[2 . ^4] ext N
      G |- of (mu (fn . A)) M

- `muIndUniv A B I M`

      G |- B[M . id] ext fix (fn . fn . N[1 . () . 0 . () . ^2] #1) M
      >>
      G |- of level I
      G, (univ I) |- of (univ I[^1]) A
      G |- positive (fn . A)
      G, (hidden) (univ I), A, (subtype 1 (mu (fn . A[0 . ^3]))), (forall 2 (fn . B[0 . ^4])) |- prod B[2 . ^4] (of (univ I[^4]) B[2 . ^4]) ext N
      G |- of (mu (fn . A)) M

- `checkPositive`

  Proves valid goals of the form:

      G |- positive (fn . A)

- `checkNegative`

  Proves valid goals of the form:

      G |- negative (fn . A)


### Void

- `voidForm`

      G |- istp void

- `voidEq`

      G |- eqtp void void

- `voidFormUniv I`

      G |- of (univ I) void
      >>
      G |- of level I

- `voidEqUniv I`

      G |- eq (univ I) void void
      >>
      G |- of level I

- `voidElim A`

      G |- A
      >>
      G |- void

- `voidSub A`

      G |- subtype void A
      >>
      G |- istp A

- `abortType`

      G |- of (intersect level (fn . intersect (univ 0) (fn . arrow void 0))) abort


### Unit

- `unitKind I`

      G |- of (kind I) unit
      >>
      G |- of level I

- `unitKindEq I`

      G |- eq (kind I) unit unit
      >>
      G |- of level I

- `unitForm`

      G |- istp unit

- `unitEq`

      G |- eqtp unit unit

- `unitFormUniv I`

      G |- of (univ I) unit
      >>
      G |- of level I

- `unitEqUniv I`

      G |- eq (univ I) unit unit
      >>
      G |- of level I

- `unitIntroOf`

      G |- of unit ()

- `unitIntro`

      G |- unit

- `unitExt M N`

      G |- eq unit M N
      >>
      G |- of unit M
      G |- of unit N

- `unitLeft n B`

      G1, unit, G2 |- B ext M[under_n (^1)]
      >>
      G1, G2[() . id] |- B[under_n (() . id)] ext M


### Bool

- `boolForm`

      G |- istp bool

- `boolEq`

      G |- eqtp bool bool

- `boolFormUniv I`

      G |- of (univ I) bool
      >>
      G |- of level I

- `boolEqUniv I`

      G |- eq (univ I) bool bool
      >>
      G |- of level I

- `boolIntro1Of`

      G |- of bool true

- `boolIntro2Of`

      G |- of bool false

- `boolElimOf A M P R`

      G |- of A[M . id] (ite M P R)
      >>
      G |- of bool M
      G |- of A[true . id] P
      G |- of A[false . id] R

- `boolElimOfNondep A M P R`

      G |- of A (ite M P R)
      >>
      G |- of bool M
      G |- of A P
      G |- of A R

- `boolElimEq A M N P Q R S`

      G |- eq A[M . id] (ite M P R) (ite N Q S)
      >>
      G |- eq bool M N
      G |- eq A[true . id] P Q
      G |- eq A[false . id] R S

- `boolElim A M`

      G |- A[M . id] ext ite M P R
      >>
      G |- of bool M
      G |- A[true . id] ext P
      G |- A[false . id] ext R

- `boolElimIstype A C M`

      G |- istp (ite M A C)
      >>
      G |- of bool M
      G |- istp A
      G |- istp C

- `boolElimEqtype A B C D M N`

      G |- eqtp (ite M A C) (ite N B D)
      >>
      G |- eq bool M N
      G |- eqtp A B
      G |- eqtp C D

- `boolLeft n A`

      G1, bool, G2 |- A ext ite 0+n M[under_n (^1)] N[under_n (^1)]
      >>
      G1, G2[true . id] |- A[under_n (true . id)] ext M
      G1, G2[false . id] |- A[under_n (false . id)] ext N

- `boolContradiction A`

      G |- A
      >>
      G |- eq bool true false

- `iteType`

      G |- of (intersect level (fn . intersect (univ 0) (fn . arrow bool (arrow 0 (arrow 0 0))))) ite


### Natural numbers

- `natForm`

      G |- istp nat

- `natEq`

      G |- eqtp nat nat

- `natFormUniv I`

      G |- of (univ I) nat
      >>
      G |- of level I

- `natEqUniv I`

      G |- eq (univ I) nat nat
      >>
      G |- of level I

- `natElimEq A M N P Q R S`

      G |- eq A[M . id] (natcase M P (fn . R)) (natcase N Q (fn . S))
      >>
      G |- eq nat M N
      G |- eq A[zero . id] P Q
      G, nat |- eq A[succ 0 . ^1] R S

- `natElimEqtype A B C D M N`

      G |- eqtp (natcase M A (fn . C)) (natcase N B (fn . D))
      >>
      G |- eq nat M N
      G |- eqtp A B
      G, nat |- eqtp C D

- `natUnroll`

      G |- eeqtp nat (sum unit nat) ext (() , ())

- `natContradiction A M`

      G |- A
      >>
      G |- eq nat zero (succ M)

- `natInjection M N`

      G |- eq nat M N
      >>
      G |- eq nat (succ M) (succ N)

- `zeroType`

      G |- of nat zero

- `succType`

      G |- of (arrow nat nat) succ


### Universes

- `univKind I J`

      G |- of (kind I) (univ J)
      >>
      G |- eq level J I

- `univKindEq I J K`

      G |- eq (kind I) (univ J) (univ K)
      >>
      G |- eq level J K
      G |- eq level J I

- `univForm I`

      G |- istp (univ I)
      >>
      G |- of level I

- `univEq I J`

      G |- eqtp (univ I) (univ J)
      >>
      G |- eq level I J

- `univFormUniv I J`

      G |- of (univ I) (univ J)
      >>
      G |- lleq (lsucc J) I

- `univFormUnivSucc I`

      G |- of (univ (lsucc I)) (univ I)
      >>
      G |- of level I

- `univEqUniv I J K`

      G |- eq (univ I) (univ J) (univ K)
      >>
      G |- eq level J K
      G |- lleq (lsucc J) I

- `univCumulativeOf A I J`

      G |- of (univ J) A
      >>
      G |- of (univ I) A
      G |- lleq I J

- `univCumulativeEq A B I J`

      G |- eq (univ J) A B
      >>
      G |- eq (univ I) A B
      G |- lleq I J

- `univCumulativeSuccOf A I`

      G |- of (univ (lsucc I)) A
      >>
      G |- of (univ I) A

- `univSub I J`

      G |- subtype (univ I) (univ J)
      >>
      G |- lleq I J

- `univForgetOf A I`

      G |- istp A
      >>
      G |- of (univ I) A

- `univForgetEq A B I`

      G |- eqtp A B
      >>
      G |- eq (univ I) A B

- `univIntroEqtype A B I`

      G |- eq (univ I) A B
      >>
      G |- eqtp A B
      G |- of (univ I) A
      G |- of (univ I) B

- `univFormInv I`

      G |- of level I
      >>
      G |- istp (univ I)


### Kinds

- `kindForm I`

      G |- istp (kind I)
      >>
      G |- of level I

- `kindEq I J`

      G |- eqtp (kind I) (kind J)
      >>
      G |- eq level I J

- `kindFormUniv I K`

      G |- of (univ K) (kind I)
      >>
      G |- lleq (lsucc (lsucc I)) K

- `kindEqUniv I J K`

      G |- eq (univ K) (kind I) (kind J)
      >>
      G |- eq level I J
      G |- lleq (lsucc (lsucc I)) K

- `kindForgetOf A I`

      G |- of (univ (lsucc I)) A
      >>
      G |- of (kind I) A

- `kindForgetEq A B I`

      G |- eq (univ (lsucc I)) A B
      >>
      G |- eq (kind I) A B

- `kindUnivSub I J`

      G |- subtype (kind I) (univ J)
      >>
      G |- lleq (lsucc I) J


### Levels

- `levelForm`

      G |- istp level

- `levelEq`

      G |- eqtp level level

- `levelFormUniv I`

      G |- of (univ I) level
      >>
      G |- of level I

- `levelEqUniv I`

      G |- eq (univ I) level level
      >>
      G |- of level I

- `lleqForm I J`

      G |- istp (lleq I J)
      >>
      G |- of level I
      G |- of level J

- `lleqEq I I' J J'`

      G |- eqtp (lleq I J) (lleq I' J')
      >>
      G |- eq level I I'
      G |- eq level J J'

- `lleqFormUniv I J K`

      G |- of (univ K) (lleq I J)
      >>
      G |- of level I
      G |- of level J
      G |- of level K

- `lleqEqUniv I I' J J' K`

      G |- eq (univ K) (lleq I J) (lleq I' J')
      >>
      G |- eq level I I'
      G |- eq level J J'
      G |- of level K

- `lzeroLevel`

      G |- of level lzero

- `lsuccLevel M`

      G |- of level (lsucc M)
      >>
      G |- of level M

- `lsuccEq M N`

      G |- eq level (lsucc M) (lsucc N)
      >>
      G |- eq level M N

- `lmaxLevel M N`

      G |- of level (lmax M N)
      >>
      G |- of level M
      G |- of level N

- `lmaxEq M M' N N'`

      G |- eq level (lmax M N) (lmax M' N')
      >>
      G |- eq level M M'
      G |- eq level N N'

- `lleqRefl M`

      G |- lleq M M
      >>
      G |- of level M

- `lleqTrans M N P`

      G |- lleq M P
      >>
      G |- lleq M N
      G |- lleq N P

- `lleqZero M`

      G |- lleq lzero M
      >>
      G |- of level M

- `lleqSucc M N`

      G |- lleq (lsucc M) (lsucc N)
      >>
      G |- lleq M N

- `lleqIncrease M N`

      G |- lleq M (lsucc N)
      >>
      G |- lleq M N

- `lleqMaxL M N P`

      G |- lleq (lmax M N) P
      >>
      G |- lleq M P
      G |- lleq N P

- `lleqMaxR1 M N P`

      G |- lleq M (lmax N P)
      >>
      G |- lleq M N
      G |- of level P

- `lleqMaxR2 M N P`

      G |- lleq M (lmax N P)
      >>
      G |- lleq M P
      G |- of level N

- `lleqResp M M' N N'`

      G |- lleq M N
      >>
      G |- eq level M' M
      G |- eq level N' N
      G |- lleq M' N'

- `lsuccMaxDistTrans M N P`

      G |- eq level M (lsucc (lmax N P))
      >>
      G |- eq level M (lmax (lsucc N) (lsucc P))

- `lzeroType`

      G |- of level lzero

- `lsuccType`

      G |- of (arrow level level) lsucc

- `lmaxType`

      G |- of (arrow level (arrow level level)) lmax


### Equality

- `eqForm A M P`

      G |- istp (eq A M P)
      >>
      G |- of A M
      G |- of A P

- `eqEq A B M N P Q`

      G |- eqtp (eq A M P) (eq B N Q)
      >>
      G |- eqtp A B
      G |- eq A M N
      G |- eq A P Q

- `eqFormUniv A I M P`

      G |- of (univ I) (eq A M P)
      >>
      G |- of (univ I) A
      G |- of A M
      G |- of A P

- `eqEqUniv A B I M N P Q`

      G |- eq (univ I) (eq A M P) (eq B N Q)
      >>
      G |- eq (univ I) A B
      G |- eq A M N
      G |- eq A P Q

- `eqIntro A M N`

      G |- of (eq A M N) ()
      >>
      G |- eq A M N

- `eqElim A M N P`

      G |- eq A M N
      >>
      G |- of (eq A M N) P

- `eqTrivialize A M N`

      G |- eq A M N
      >>
      G |- eq A M N

- `eqExt A M N P Q`

      G |- eq (eq A M N) P Q
      >>
      G |- of (eq A M N) P
      G |- of (eq A M N) Q

- `eqLeft n A B P Q`

      G1, (eq A P Q), G2 |- B ext M[under_n (^1)]
      >>
      G1, G2[() . id] |- B[under_n (() . id)] ext M

- `eqRefl A M`

      G |- eq A M M
      >>
      G |- of A M

- `eqSymm A M N`

      G |- eq A M N
      >>
      G |- eq A N M

- `eqTrans A M N P`

      G |- eq A M P
      >>
      G |- eq A M N
      G |- eq A N P

- `eqFormInv1 A M N`

      G |- istp A
      >>
      G |- istp (eq A M N)

- `eqFormInv2 A M N`

      G |- of A M
      >>
      G |- istp (eq A M N)

- `eqFormInv3 A M N`

      G |- of A N
      >>
      G |- istp (eq A M N)


### Typing

- `ofForm A M`

      G |- istp (of A M)
      >>
      G |- of A M

- `ofEq A B M N`

      G |- eqtp (of A M) (of B N)
      >>
      G |- eqtp A B
      G |- eq A M N

- `ofFormUniv A I M`

      G |- of (univ I) (of A M)
      >>
      G |- of (univ I) A
      G |- of A M

- `ofEqUniv A B I M N`

      G |- eq (univ I) (of A M) (of B N)
      >>
      G |- eq (univ I) A B
      G |- eq A M N

- `ofIntro A M`

      G |- of (of A M) ()
      >>
      G |- of A M

- `ofElim A M P`

      G |- of A M
      >>
      G |- of (of A M) P

- `ofTrivialize A M`

      G |- of A M
      >>
      G |- of A M

- `ofExt A M P Q`

      G |- eq (of A M) P Q
      >>
      G |- of (of A M) P
      G |- of (of A M) Q

- `ofLeft n A B P`

      G1, (of A P), G2 |- B ext M[under_n (^1)]
      >>
      G1, G2[() . id] |- B[under_n (() . id)] ext M

- `ofEquand1 A M N`

      G |- of A M
      >>
      G |- eq A M N

- `ofEquand2 A M N`

      G |- of A N
      >>
      G |- eq A M N


### Type equality

- `eqtpForm A B`

      G |- istp (eqtp A B)
      >>
      G |- istp A
      G |- istp B

- `eqtpEq A B C D`

      G |- eqtp (eqtp A C) (eqtp B D)
      >>
      G |- eqtp A B
      G |- eqtp C D

- `eqtpFormUniv A B I`

      G |- of (univ I) (eqtp A B)
      >>
      G |- of (univ I) A
      G |- of (univ I) B

- `eqtpEqUniv A B C D I`

      G |- eq (univ I) (eqtp A C) (eqtp B D)
      >>
      G |- eq (univ I) A B
      G |- eq (univ I) C D

- `eqtpIntro A B`

      G |- of (eqtp A B) ()
      >>
      G |- eqtp A B

- `eqtpElim A B P`

      G |- eqtp A B
      >>
      G |- of (eqtp A B) P

- `eqtpExt A B P Q`

      G |- eq (eqtp A B) P Q
      >>
      G |- of (eqtp A B) P
      G |- of (eqtp A B) Q

- `eqtpLeft n A B C`

      G1, (eqtp A B), G2 |- C ext M[under_n (^1)]
      >>
      G1, G2[() . id] |- C[under_n (() . id)] ext M

- `eqtpFunct A B M N`

      G |- eqtp B[M . id] B[N . id]
      >>
      G, A |- istp B
      G |- eq A M N

- `eqtpFunctType A B B'`

      G |- eqtp A[B . id] A[B' . id]
      >>
      G, type |- istp A
      G |- eqtp B B'

- `equivalenceOf A B M`

      G |- of B M
      >>
      G |- eqtp A B
      G |- of A M

- `equivalenceEq A B M N`

      G |- eq B M N
      >>
      G |- eqtp A B
      G |- eq A M N

- `equivalence A B`

      G |- B ext M
      >>
      G |- eqtp A B
      G |- A ext M

- `equivalenceLeft n A B C`

      G1, A, G2 |- C ext M
      >>
      G1, (istp A) |- eqtp A[^1] B[^1]
      G1, B, G2 |- C ext M

- `equivalenceLeftAlt n A B C`

      G1, A, G2 |- C ext M
      >>
      G1, A, G2 |- eqtp A[(^1) o ^n] B[(^1) o ^n]
      G1, B, G2 |- C ext M

- `eqtpRefl A`

      G |- eqtp A A
      >>
      G |- istp A

- `eqtpSymm A B`

      G |- eqtp A B
      >>
      G |- eqtp B A

- `eqtpTrans A B C`

      G |- eqtp A C
      >>
      G |- eqtp A B
      G |- eqtp B C


### Type formation

- `istpForm A`

      G |- istp (istp A)
      >>
      G |- istp A

- `istpEq A B`

      G |- eqtp (istp A) (istp B)
      >>
      G |- eqtp A B

- `istpFormUniv A I`

      G |- of (univ I) (istp A)
      >>
      G |- of (univ I) A

- `istpEqUniv A B I`

      G |- eq (univ I) (istp A) (istp B)
      >>
      G |- eq (univ I) A B

- `istpIntro A`

      G |- of (istp A) ()
      >>
      G |- istp A

- `istpElim A P`

      G |- istp A
      >>
      G |- of (istp A) P

- `istpExt A P Q`

      G |- eq (istp A) P Q
      >>
      G |- of (istp A) P
      G |- of (istp A) Q

- `istpLeft n A B`

      G1, (istp A), G2 |- B ext M[under_n (^1)]
      >>
      G1, G2[() . id] |- B[under_n (() . id)] ext M

- `inhabitedForm A`

      G |- istp A
      >>
      G |- A


### Subtyping

- `subtypeForm A B`

      G |- istp (subtype A B)
      >>
      G |- istp A
      G |- istp B

- `subtypeEq A B C D`

      G |- eqtp (subtype A C) (subtype B D)
      >>
      G |- eqtp A B
      G |- eqtp C D

- `subtypeFormUniv A B I`

      G |- of (univ I) (subtype A B)
      >>
      G |- of (univ I) A
      G |- of (univ I) B

- `subtypeEqUniv A B C D I`

      G |- eq (univ I) (subtype A C) (subtype B D)
      >>
      G |- eq (univ I) A B
      G |- eq (univ I) C D

- `subtypeIntro A B`

      G |- of (subtype A B) ()
      >>
      G |- subtype A B

- `subtypeElim A B P`

      G |- subtype A B
      >>
      G |- of (subtype A B) P

- `subtypeExt A B P Q`

      G |- eq (subtype A B) P Q
      >>
      G |- of (subtype A B) P
      G |- of (subtype A B) Q

- `subtypeLeft n A B C`

      G1, (subtype A B), G2 |- C ext M[under_n (^1)]
      >>
      G1, G2[() . id] |- C[under_n (() . id)] ext M

- `subtypeEstablish A B`

      G |- subtype A B
      >>
      G |- istp A
      G |- istp B
      G, A |- of B[^1] 0

- `subsumptionOf A B M`

      G |- of B M
      >>
      G |- subtype A B
      G |- of A M

- `subsumptionEq A B M N`

      G |- eq B M N
      >>
      G |- subtype A B
      G |- eq A M N

- `subsumption A B`

      G |- B ext M
      >>
      G |- subtype A B
      G |- A ext M

- `subsumptionAlt A B`

      G |- B ext M
      >>
      G |- eeqtp B A
      G |- A ext M

- `subsumptionLeft n A B C`

      G1, A, G2 |- C ext M
      >>
      G1, (istp A) |- eeqtp A[^1] B[^1]
      G1, B, G2 |- C ext M

- `subsumptionLeftAlt n A B C`

      G1, A, G2 |- C ext M
      >>
      G1, A, G2 |- eeqtp A[(^1) o ^n] B[(^1) o ^n]
      G1, B, G2 |- C ext M

- `subsumptionLast n A B C`

      G1, A, G2 |- C[(id) o ^n] ext M[(id) o ^n]
      >>
      G1, A |- subtype A[^1] B[^1]
      G1, B |- C ext M

- `tighten n A B C`

      G1, A, G2 |- C ext M
      >>
      G1, A, G2 |- subtype B[(^1) o ^n] A[(^1) o ^n]
      G1, A, G2 |- of B[(^1) o ^n] 0+n
      G1, B, G2 |- C ext M

- `subtypeRefl A`

      G |- subtype A A
      >>
      G |- istp A

- `subtypeReflEqtype A B`

      G |- subtype A B
      >>
      G |- eqtp A B

- `subtypeTrans A B C`

      G |- subtype A C
      >>
      G |- subtype A B
      G |- subtype B C

- `subtypeIstp1 A B`

      G |- istp A
      >>
      G |- subtype A B

- `subtypeIstp2 A B`

      G |- istp B
      >>
      G |- subtype A B


### Extensional type equality

- `eeqtpForm A B`

      G |- istp (eeqtp A B)
      >>
      G |- istp A
      G |- istp B

- `eeqtpEq A B C D`

      G |- eqtp (eeqtp A C) (eeqtp B D)
      >>
      G |- eqtp A B
      G |- eqtp C D

- `eeqtpFormUniv A B I`

      G |- of (univ I) (eeqtp A B)
      >>
      G |- of (univ I) A
      G |- of (univ I) B

- `eeqtpEqUniv A B C D I`

      G |- eq (univ I) (eeqtp A C) (eeqtp B D)
      >>
      G |- eq (univ I) A B
      G |- eq (univ I) C D


### Subset types

- `setForm A B`

      G |- istp (set A (fn . B))
      >>
      G |- istp A
      G, A |- istp B

- `setEq A A' B B'`

      G |- eqtp (set A (fn . B)) (set A' (fn . B'))
      >>
      G |- eqtp A A'
      G, A |- iff B B'

- `setFormUniv A B I`

      G |- of (univ I) (set A (fn . B))
      >>
      G |- of (univ I) A
      G, A |- of (univ I[^1]) B

- `setEqUniv A A' B B' I`

      G |- eq (univ I) (set A (fn . B)) (set A' (fn . B'))
      >>
      G |- eq (univ I) A A'
      G, A |- of (univ I[^1]) B
      G, A |- of (univ I[^1]) B'
      G, A |- iff B B'

- `setWeakenOf A B M`

      G |- of A M
      >>
      G |- of (set A (fn . B)) M

- `setWeakenEq A B M N`

      G |- eq A M N
      >>
      G |- eq (set A (fn . B)) M N

- `setWeaken A B`

      G |- A ext M
      >>
      G |- set A (fn . B) ext M

- `setIntroOf A B M`

      G |- of (set A (fn . B)) M
      >>
      G, A |- istp B
      G |- of A M
      G |- B[M . id]

- `setIntroEq A B M N`

      G |- eq (set A (fn . B)) M N
      >>
      G, A |- istp B
      G |- eq A M N
      G |- B[M . id]

- `setIntro A B M`

      G |- set A (fn . B) ext M
      >>
      G, A |- istp B
      G |- of A M
      G |- B[M . id]

- `setIntroOfSquash A B M`

      G |- of (set A (fn . B)) M
      >>
      G, A |- istp B
      G |- of A M
      G |- squash B[M . id]

- `setIntroEqSquash A B M N`

      G |- eq (set A (fn . B)) M N
      >>
      G, A |- istp B
      G |- eq A M N
      G |- squash B[M . id]

- `squashIntroOfSquash A`

      G |- of (squash A) ()
      >>
      G |- istp A
      G |- squash A

- `setElim A B C M`

      G |- C ext N[() . id]
      >>
      G, A |- istp B
      G |- of (set A (fn . B)) M
      G, (hidden) B[M . id] |- C[^1] ext N

- `setLeft n A B C`

      G1, (set A (fn . B)), G2 |- C ext M[under_n (() . id)]
      >>
      G1, A |- istp B
      G1, A, (hidden) B, G2[^1] |- C[under_n (^1)] ext M

- `setSquash A B`

      G |- eqtp (set A (fn . B)) (set A (fn . squash B))
      >>
      G |- istp (set A (fn . B))

- `setFormInv A B`

      G |- istp A
      >>
      G |- istp (set A (fn . B))

- `setSubElim A A' B`

      G |- subtype (set A (fn . B)) A'
      >>
      G |- subtype A A'
      G, A |- istp B


### Intensional subset types

- `isetForm A B`

      G |- istp (iset A (fn . B))
      >>
      G |- istp A
      G, A |- istp B

- `isetEq A A' B B'`

      G |- eqtp (iset A (fn . B)) (iset A' (fn . B'))
      >>
      G |- eqtp A A'
      G, A |- eqtp B B'

- `isetFormUniv A B I`

      G |- of (univ I) (iset A (fn . B))
      >>
      G |- of (univ I) A
      G, A |- of (univ I[^1]) B

- `isetEqUniv A A' B B' I`

      G |- eq (univ I) (iset A (fn . B)) (iset A' (fn . B'))
      >>
      G |- eq (univ I) A A'
      G, A |- eq (univ I[^1]) B B'

- `isetWeakenOf A B M`

      G |- of A M
      >>
      G |- of (iset A (fn . B)) M

- `isetWeakenEq A B M N`

      G |- eq A M N
      >>
      G |- eq (iset A (fn . B)) M N

- `isetWeaken A B`

      G |- A ext M
      >>
      G |- iset A (fn . B) ext M

- `isetIntroOf A B M`

      G |- of (iset A (fn . B)) M
      >>
      G, A |- istp B
      G |- of A M
      G |- B[M . id]

- `isetIntroEq A B M N`

      G |- eq (iset A (fn . B)) M N
      >>
      G, A |- istp B
      G |- eq A M N
      G |- B[M . id]

- `isetIntro A B M`

      G |- iset A (fn . B) ext M
      >>
      G, A |- istp B
      G |- of A M
      G |- B[M . id]

- `isetIntroOfSquash A B M`

      G |- of (iset A (fn . B)) M
      >>
      G, A |- istp B
      G |- of A M
      G |- squash B[M . id]

- `isetIntroEqSquash A B M N`

      G |- eq (iset A (fn . B)) M N
      >>
      G, A |- istp B
      G |- eq A M N
      G |- squash B[M . id]

- `isetElim A B C M`

      G |- C ext N[() . id]
      >>
      G |- of (iset A (fn . B)) M
      G, (hidden) B[M . id] |- C[^1] ext N

- `isetLeft n A B C`

      G1, (iset A (fn . B)), G2 |- C ext M[under_n (() . id)]
      >>
      G1, A, (hidden) B, G2[^1] |- C[under_n (^1)] ext M

- `isetFormInv1 A B`

      G |- istp A
      >>
      G |- istp (iset A (fn . B))

- `isetFormInv2 A B M`

      G |- istp B[M . id]
      >>
      G |- istp (iset A (fn . B))
      G |- of A M

- `isetSubElim A A' B`

      G |- subtype (iset A (fn . B)) A'
      >>
      G |- subtype A A'
      G, A |- istp B


### Squash

- `squashForm A`

      G |- istp (squash A)
      >>
      G |- istp A

- `squashEq A B`

      G |- eqtp (squash A) (squash B)
      >>
      G |- iff A B

- `squashFormUniv A I`

      G |- of (univ I) (squash A)
      >>
      G |- of (univ I) A

- `squashEqUniv A B I`

      G |- eq (univ I) (squash A) (squash B)
      >>
      G |- of (univ I) A
      G |- of (univ I) B
      G |- iff A B

- `squashIntroOf A`

      G |- of (squash A) ()
      >>
      G |- A

- `squashIntro A`

      G |- squash A
      >>
      G |- A

- `squashElim A C M`

      G |- C ext N[() . id]
      >>
      G |- of (squash A) M
      G |- istp A
      G, (hidden) A |- C[^1] ext N

- `squashExt A M N`

      G |- eq (squash A) M N
      >>
      G |- of (squash A) M
      G |- of (squash A) N
      G |- istp A

- `squashLeft n A C`

      G1, (squash A), G2 |- C ext M[under_n (() . ^1)]
      >>
      G1 |- istp A
      G1, (hidden) A, G2[() . ^1] |- C[under_n (() . ^1)] ext M

- `squashSub A B`

      G |- subtype (squash A) (squash B)
      >>
      G |- istp B
      G |- arrow A B


### Intensional squash

- `isquashForm A`

      G |- istp (isquash A)
      >>
      G |- istp A

- `isquashEq A B`

      G |- eqtp (isquash A) (isquash B)
      >>
      G |- eqtp A B

- `isquashFormUniv A I`

      G |- of (univ I) (isquash A)
      >>
      G |- of (univ I) A

- `isquashEqUniv A B I`

      G |- eq (univ I) (isquash A) (isquash B)
      >>
      G |- of (univ I) A
      G |- of (univ I) B
      G |- eq (univ I) A B

- `isquashIntroOf A`

      G |- of (isquash A) ()
      >>
      G |- A

- `isquashIntro A`

      G |- isquash A
      >>
      G |- A

- `isquashIntroOfIsquash A`

      G |- of (isquash A) ()
      >>
      G |- isquash A

- `isquashElim A C M`

      G |- C ext N[() . id]
      >>
      G |- of (isquash A) M
      G, (hidden) A |- C[^1] ext N

- `isquashExt A M N`

      G |- eq (isquash A) M N
      >>
      G |- of (isquash A) M
      G |- of (isquash A) N

- `isquashLeft n A C`

      G1, (isquash A), G2 |- C ext M[under_n (() . ^1)]
      >>
      G1, (hidden) A, G2[() . ^1] |- C[under_n (() . ^1)] ext M

- `isquashSub A B`

      G |- subtype (isquash A) (isquash B)
      >>
      G |- istp B
      G |- arrow A B

- `isquashFormInv A`

      G |- istp A
      >>
      G |- istp (isquash A)


### Quotient types

- `quotientForm A B`

      G |- istp (quotient A (fn . fn . B))
      >>
      G |- istp A
      G, A, A[^1] |- istp B
      G, A, A[^1], B |- B[2 . 1 . ^3]
      G, A, A[^1], A[^2], B[^1], B[1 . 2 . ^4] |- B[2 . ^4]

- `quotientEq A A' B B'`

      G |- eqtp (quotient A (fn . fn . B)) (quotient A' (fn . fn . B'))
      >>
      G |- eqtp A A'
      G, A, A[^1] |- istp B
      G, A, A[^1] |- istp B'
      G, A, A[^1], B |- B'[^1]
      G, A, A[^1], B' |- B[^1]
      G, A, A[^1], B |- B[2 . 1 . ^3]
      G, A, A[^1], A[^2], B[^1], B[1 . 2 . ^4] |- B[2 . ^4]

- `quotientFormUniv A B I`

      G |- of (univ I) (quotient A (fn . fn . B))
      >>
      G |- of (univ I) A
      G, A, A[^1] |- of (univ I[^2]) B
      G, A, A[^1], B |- B[2 . 1 . ^3]
      G, A, A[^1], A[^2], B[^1], B[1 . 2 . ^4] |- B[2 . ^4]

- `quotientEqUniv A A' B B' I`

      G |- eq (univ I) (quotient A (fn . fn . B)) (quotient A' (fn . fn . B'))
      >>
      G |- eq (univ I) A A'
      G, A, A[^1] |- of (univ I[^2]) B
      G, A, A[^1] |- of (univ I[^2]) B'
      G, A, A[^1], B |- B'[^1]
      G, A, A[^1], B' |- B[^1]
      G, A, A[^1], B |- B[2 . 1 . ^3]
      G, A, A[^1], A[^2], B[^1], B[1 . 2 . ^4] |- B[2 . ^4]

- `quotientIntroOf A B M`

      G |- of (quotient A (fn . fn . B)) M
      >>
      G |- istp (quotient A (fn . fn . B))
      G |- of A M
      G |- B[M . M . id]

- `quotientIntroEq A B M N`

      G |- eq (quotient A (fn . fn . B)) M N
      >>
      G |- istp (quotient A (fn . fn . B))
      G |- of A M
      G |- of A N
      G |- B[N . M . id]

- `quotientElimOf A B C M P`

      G |- of C[M . id] P[M . id]
      >>
      G |- of (quotient A (fn . fn . B)) M
      G, A, A[^1] |- istp B
      G, (quotient A (fn . fn . B)) |- istp C
      G, A, A[^1], B |- eq C[^2] P[^2] P[1 . ^3]

- `quotientElimEq A B C M N P Q`

      G |- eq C[M . id] P[M . id] Q[N . id]
      >>
      G |- eq (quotient A (fn . fn . B)) M N
      G, A, A[^1] |- istp B
      G, (quotient A (fn . fn . B)) |- istp C
      G, A, A[^1], B |- eq C[^2] P[^2] Q[1 . ^3]

- `quotientElimIstype A B C M`

      G |- istp C[M . id]
      >>
      G |- of (quotient A (fn . fn . B)) M
      G, A, A[^1] |- istp B
      G, A, A[^1], B |- eqtp C[^2] C[1 . ^3]

- `quotientElimEqtype A B C D M N`

      G |- eqtp C[M . id] D[N . id]
      >>
      G |- eq (quotient A (fn . fn . B)) M N
      G, A, A[^1] |- istp B
      G, A, A[^1], B |- eqtp C[^2] D[1 . ^3]

- `quotientDescent A B C M N`

      G |- C ext P[() . id]
      >>
      G, A, A[^1] |- istp B
      G |- istp C
      G |- of A M
      G |- of A N
      G |- eq (quotient A (fn . fn . B)) M N
      G, (hidden) B[N . M . id] |- C[^1] ext P

- `quotientLeft n A B C`

      G1, (quotient A (fn . fn . B)), G2 |- C ext M[under_n (() . ^1)]
      >>
      G1, (quotient A (fn . fn . B)), G2 |- istp C
      G1, (hidden) A, G2 |- C ext M

- `quotientLeftRefl n A B C`

      G1, (quotient A (fn . fn . B)), G2 |- C ext M[under_n (() . () . ^1)]
      >>
      G1, A, A[^1] |- istp B
      G1, (quotient A (fn . fn . B)), G2 |- istp C
      G1, (hidden) A, (hidden) B[0 . id], G2[^1] |- C[under_n (^1)] ext M

- `quotientLeftIstype n A B C`

      G1, (quotient A (fn . fn . B)), G2 |- istp C
      >>
      G1, A, A[^1] |- istp B
      G1, A, A[^1], B, G2[^2] |- eqtp C[under_n (^2)] C[under_n (1 . ^3)]

- `quotientLeftEqtype n A B C D`

      G1, (quotient A (fn . fn . B)), G2 |- eqtp C D
      >>
      G1, A, A[^1] |- istp B
      G1, A, A[^1], B, G2[^2] |- eqtp C[under_n (^2)] D[under_n (1 . ^3)]

- `quotientLeftOf n A B C M`

      G1, (quotient A (fn . fn . B)), G2 |- of C[under_n (^1)] M
      >>
      G1, A, A[^1] |- istp B
      G1, A, A[^1], B, G2[^2] |- eq C[under_n (^3)] M[under_n (^2)] M[under_n (1 . ^3)]

- `quotientLeftEq n A B C M N`

      G1, (quotient A (fn . fn . B)), G2 |- eq C[under_n (^1)] M N
      >>
      G1, A, A[^1] |- istp B
      G1, A, A[^1], B, G2[^2] |- eq C[under_n (^3)] M[under_n (^2)] N[under_n (1 . ^3)]

- `quotientLeftOfDep n A B C M`

      G1, (quotient A (fn . fn . B)), G2 |- of C M
      >>
      G1, A, A[^1] |- istp B
      G1, A, A[^1], B, G2[^2] |- eqtp C[under_n (^2)] C[under_n (1 . ^3)]
      G1, A, A[^1], B, G2[^2] |- eq C[under_n (^2)] M[under_n (^2)] M[under_n (1 . ^3)]

- `quotientLeftEqDep n A B C M N`

      G1, (quotient A (fn . fn . B)), G2 |- eq C M N
      >>
      G1, A, A[^1] |- istp B
      G1, A, A[^1], B, G2[^2] |- eqtp C[under_n (^2)] C[under_n (1 . ^3)]
      G1, A, A[^1], B, G2[^2] |- eq C[under_n (^2)] M[under_n (^2)] N[under_n (1 . ^3)]

- `quotientFormInv A B`

      G |- istp A
      >>
      G |- istp (quotient A (fn . fn . B))


### Impredicative universals

- `iforallForm A I K`

      G |- istp (iforall I K (fn . A))
      >>
      G |- of (kind I) K
      G, K |- istp A

- `iforallEq A B I K L`

      G |- eqtp (iforall I K (fn . A)) (iforall I L (fn . B))
      >>
      G |- eq (kind I) K L
      G, K |- eqtp A B

- `iforallFormUniv A I J K`

      G |- of (univ J) (iforall I K (fn . A))
      >>
      G |- of (kind I) K
      G |- lleq I J
      G, K |- of (univ J[^1]) A

- `iforallEqUniv A B I J K L`

      G |- eq (univ J) (iforall I K (fn . A)) (iforall I L (fn . B))
      >>
      G |- eq (kind I) K L
      G |- lleq I J
      G, K |- eq (univ J[^1]) A B

- `iforallIntroOf A I K M`

      G |- of (iforall I K (fn . A)) M
      >>
      G |- of (kind I) K
      G, K |- of A M[^1]

- `iforallIntroEq A I K M N`

      G |- eq (iforall I K (fn . A)) M N
      >>
      G |- of (kind I) K
      G, K |- eq A M[^1] N[^1]

- `iforallIntro A I K`

      G |- iforall I K (fn . A) ext M[() . id]
      >>
      G |- of (kind I) K
      G, (hidden) K |- A ext M

- `iforallElimOf A I K M P`

      G |- of A[P . id] M
      >>
      G, K |- istp A
      G |- of (iforall I K (fn . A)) M
      G |- of K P

- `iforallElimEq A I K M N P`

      G |- eq A[P . id] M N
      >>
      G, K |- istp A
      G |- eq (iforall I K (fn . A)) M N
      G |- of K P

- `iforallElim A I K P`

      G |- A[P . id] ext M
      >>
      G, K |- istp A
      G |- iforall I K (fn . A) ext M
      G |- of K P


### Impredicative polymorphism

- `foralltpForm A`

      G |- istp (foralltp (fn . A))
      >>
      G, type |- istp A

- `foralltpEq A B`

      G |- eqtp (foralltp (fn . A)) (foralltp (fn . B))
      >>
      G, type |- eqtp A B

- `foralltpIntroOf A M`

      G |- of (foralltp (fn . A)) M
      >>
      G, type |- of A M[^1]

- `foralltpIntroEq A M N`

      G |- eq (foralltp (fn . A)) M N
      >>
      G, type |- eq A M[^1] N[^1]

- `foralltpIntro A`

      G |- foralltp (fn . A) ext M[() . id]
      >>
      G, (hidden) type |- A ext M

- `foralltpElimOf A B M`

      G |- of A[B . id] M
      >>
      G, type |- istp A
      G |- of (foralltp (fn . A)) M
      G |- istp B

- `foralltpElimEq A B M N`

      G |- eq A[B . id] M N
      >>
      G, type |- istp A
      G |- eq (foralltp (fn . A)) M N
      G |- istp B

- `foralltpElim A B`

      G |- A[B . id] ext M
      >>
      G, type |- istp A
      G |- foralltp (fn . A) ext M
      G |- istp B


### Impredicative existentials

- `iexistsForm A I K`

      G |- istp (iexists I K (fn . A))
      >>
      G |- of (kind I) K
      G, K |- istp A

- `iexistsEq A B I K L`

      G |- eqtp (iexists I K (fn . A)) (iexists I L (fn . B))
      >>
      G |- eq (kind I) K L
      G, K |- eqtp A B

- `iexistsFormUniv A I J K`

      G |- of (univ J) (iexists I K (fn . A))
      >>
      G |- of (kind I) K
      G |- lleq I J
      G, K |- of (univ J[^1]) A

- `iexistsEqUniv A B I J K L`

      G |- eq (univ J) (iexists I K (fn . A)) (iexists I L (fn . B))
      >>
      G |- eq (kind I) K L
      G |- lleq I J
      G, K |- eq (univ J[^1]) A B

- `iexistsIntroOf A B I K M`

      G |- of (iexists I K (fn . A)) M
      >>
      G |- of (kind I) K
      G, K |- istp A
      G |- of K B
      G |- of A[B . id] M

- `iexistsIntroEq A B I K M N`

      G |- eq (iexists I K (fn . A)) M N
      >>
      G |- of (kind I) K
      G, K |- istp A
      G |- of K B
      G |- eq A[B . id] M N

- `iexistsIntro A B I K`

      G |- iexists I K (fn . A) ext M
      >>
      G |- of (kind I) K
      G, K |- istp A
      G |- of K B
      G |- A[B . id] ext M

- `iexistsElimOf A B I K M P`

      G |- of B P[M . id]
      >>
      G |- istp K
      G, K |- istp A
      G, K, A |- of B[^2] P[0 . ^2]
      G |- of (iexists I K (fn . A)) M

- `iexistsElimEq A B I K M N P Q`

      G |- eq B P[M . id] Q[N . id]
      >>
      G |- istp K
      G, K |- istp A
      G, K, A |- eq B[^2] P[0 . ^2] Q[0 . ^2]
      G |- eq (iexists I K (fn . A)) M N

- `iexistsElim A B I K M`

      G |- B ext P[M . () . id]
      >>
      G |- istp K
      G, K |- istp A
      G, (hidden) K, A |- B[^2] ext P
      G |- of (iexists I K (fn . A)) M

- `iexistsElimOfDep A B I K M P`

      G |- of B[M . id] P[M . id]
      >>
      G |- istp K
      G, K |- istp A
      G, K, A |- of B[0 . ^2] P[0 . ^2]
      G |- of (iexists I K (fn . A)) M

- `iexistsElimEqDep A B I K M N P Q`

      G |- eq B[M . id] P[M . id] Q[N . id]
      >>
      G |- istp K
      G, K |- istp A
      G, K, A |- eq B[0 . ^2] P[0 . ^2] Q[0 . ^2]
      G |- eq (iexists I K (fn . A)) M N

- `iexistsElimDep A B I K M`

      G |- B[M . id] ext P[M . () . id]
      >>
      G |- istp K
      G, K |- istp A
      G, (hidden) K, A |- B[0 . ^2] ext P
      G |- of (iexists I K (fn . A)) M

- `iexistsElimIstype A B I K M`

      G |- istp B[M . id]
      >>
      G |- istp K
      G, K |- istp A
      G, K, A |- istp B[0 . ^2]
      G |- of (iexists I K (fn . A)) M

- `iexistsElimEqtype A B C I K M N`

      G |- eqtp B[M . id] C[N . id]
      >>
      G |- istp K
      G, K |- istp A
      G, K, A |- eqtp B[0 . ^2] C[0 . ^2]
      G |- eq (iexists I K (fn . A)) M N


### Miscellaneous

- `substitution n A B M`

      G1, A, G2 |- B ext N[under_n (^1)]
      >>
      G1, A, G2 |- istp B
      G1, A, G2 |- eq A[(^1) o ^n] 0+n M[(^1) o ^n]
      G1, G2[M . id] |- B[under_n (M . id)] ext N

- `substitutionSimple n A B M`

      G1, A, G2 |- B[under_n (^1)] ext N[under_n (^1)]
      >>
      G1, A, G2 |- eq A[(^1) o ^n] 0+n M[(^1) o ^n]
      G1, G2[M . id] |- B ext N

- `substitutionLater n A B M`

      G1, (later) A, G2 |- B ext N[under_n (^1)]
      >>
      G1, (later) A, G2 |- istp B
      promote(G1), A, promote(G2) |- eq A[(^1) o ^n] 0+n M[(^1) o ^n]
      G1, G2[M . id] |- B[under_n (M . id)] ext N

- `substitutionLaterSimple n A B M`

      G1, (later) A, G2 |- B[under_n (^1)] ext N[under_n (^1)]
      >>
      promote(G1), A, promote(G2) |- eq A[(^1) o ^n] 0+n M[(^1) o ^n]
      G1, G2[M . id] |- B ext N

- `generalize A B M`

      G |- B[M . id] ext N[M . id]
      >>
      G |- of A M
      G, A |- B ext N

- `assert A B`

      G |- B ext let M (fn . N)
      >>
      G |- A ext M
      G, A |- B[^1] ext N

- `assert' A B`

      G |- B ext N[M . id]
      >>
      G |- A ext M
      G, A |- B[^1] ext N

- `inhabitant A M`

      G |- A ext M
      >>
      G |- of A M

- `letForm A B M N`

      G |- of B (let M (fn . N))
      >>
      G |- of A M
      G, A |- of B[^1] N

- `lethForm A B M N`

      G |- of B (leth M (fn . N))
      >>
      G |- of A M
      G, A |- of B[^1] N

- `leteForm A B M N`

      G |- of B (lete M (fn . N))
      >>
      G |- of A M
      G, A |- of B[^1] N

- `eeqtpSymm A B`

      G |- eeqtp A B ext (() , ())
      >>
      G |- eeqtp B A

- `weakenEqtpEeqtp A B`

      G |- eeqtp A B ext (() , ())
      >>
      G |- eqtp A B

- `accInd A B I M N R`

      G |- B[M . id] ext fix (fn . fn . P[fn . fn . 3 1 . 0 . ^2]) M
      >>
      G |- of (univ I) A
      G |- of (arrow A (arrow A (univ I))) R
      G, A, (forall A[^1] (fn . arrow (R[^2] 0 1) B[0 . ^2])) |- B[^1] ext P
      G |- of A M
      G |- of (acc A R M) N

- `insert n`

      G1, G2 |- C ext M[under_n (() . id)]
      >>
      G1, unit, G2[^] |- C[under_n (^1)] ext M

- `forallLeft M`

      G, (forall A (fn . B)) |- C[^] ext N[0 M[^] . ^]
      >>
      G |- of A M
      G, B[M . id] |- C[^] ext N

- `arrowLeft`

      G, arrow A B |- C[^] ext N[0 M[^] . ^]
      >>
      G |- A ext M
      G, B |- C[^] ext N


### Syntactic equality

Syntactic equality is intended for internal use only.

- `sequalForm M`

      G |- istp (sequal M M)

- `sequalIntroOf M`

      G |- of (sequal M M) ()

- `sequalIntro M`

      G |- sequal M M

- `sequalTrivialize M N`

      G |- sequal M N
      >>
      G |- sequal M N

- `sequalExt M N P Q`

      G |- eq (sequal M N) P Q
      >>
      G |- of (sequal M N) P
      G |- of (sequal M N) Q

- `sequalLeft n C M N`

      G1, (sequal M N), G2 |- C ext P[under_n (^1)]
      >>
      G1, G2[() . id] |- C[under_n (() . id)] ext P

- `sequalEq A M N`

      G |- eq A M N
      >>
      G |- sequal M N
      G |- of A M

- `sequalEqtp A B`

      G |- eqtp A B
      >>
      G |- sequal A B
      G |- istp A

- `sequivalence A B`

      G |- B ext M
      >>
      G |- sequal A B
      G |- A ext M

- `sequivalenceLeft n A B C`

      G1, A, G2 |- C ext M
      >>
      G1, A, G2 |- sequal A[(^1) o ^n] B[(^1) o ^n]
      G1, B, G2 |- C ext M

- `sequivalencePath path M N`

      G |- C ext P
      >>
      G |- sequal M N
      G |- C' ext P

      (where C' is obtained from C by changing a subterm determined by path from M to N)

- `sequivalenceLeftPath n path M N`

      G1, H, G2 |- C ext P
      >>
      G1 |- sequal M N
      G1, H', G2 |- C ext P

      (where H' is obtained from H by changing a subterm determined by path from M to N)

- `substitutionSyntactic n A B M`

      G1, A, G2 |- B ext N[under_n (^1)]
      >>
      G1, A, G2 |- sequal 0+n M[(^1) o ^n]
      G1, G2[M . id] |- B[under_n (M . id)] ext N

- `sequalSymm M N`

      G |- sequal N M
      >>
      G |- sequal M N

- `sequalTrans M N P`

      G |- sequal M P
      >>
      G |- sequal M N
      G |- sequal N P

- `sequalCompat M N P`

      G |- sequal P[M . id] P[N . id]
      >>
      G |- sequal M N

- `sequalCompatLam M N`

      G |- sequal (fn . M) (fn . N)
      >>
      G, nonsense |- sequal M N

- `sequalCompatPath path M N P`

      G |- sequal C{N[^k]} C{P[^k]}
      >>
      G |- sequal N P

      (where M = C{M'}, C is determined by path, and C binds k variables)

- `forallEtaSequal A B M`

      G |- sequal M (fn . M[^1] 0)
      >>
      G |- of (forall A (fn . B)) M

- `arrowEtaSequal A B M`

      G |- sequal M (fn . M[^1] 0)
      >>
      G |- of (arrow A B) M

- `existsEtaSequal A B M`

      G |- sequal M (M #1 , M #2)
      >>
      G |- of (exists A (fn . B)) M

- `prodEtaSequal A B M`

      G |- sequal M (M #1 , M #2)
      >>
      G |- of (prod A B) M

- `futureEtaSequal A M`

      G |- sequal M (next (M #prev))
      >>
      G |- of (future A) M


### Partial types

- `partialForm A`

      G |- istp (partial A)
      >>
      G |- istp A

- `partialEq A B`

      G |- eqtp (partial A) (partial B)
      >>
      G |- eqtp A B

- `partialFormUniv A I`

      G |- of (univ I) (partial A)
      >>
      G |- of (univ I) A

- `partialEqUniv A B I`

      G |- eq (univ I) (partial A) (partial B)
      >>
      G |- eq (univ I) A B

- `partialSub A B`

      G |- subtype (partial A) (partial B)
      >>
      G |- subtype A B

- `partialStrict A`

      G |- subtype (partial A) (partial (partial A))
      >>
      G |- istp A

- `partialStrictConverse A`

      G |- subtype (partial (partial A)) (partial A)
      >>
      G |- istp A

- `partialIdem A`

      G |- eeqtp (partial (partial A)) (partial A) ext (() , ())
      >>
      G |- istp A

- `haltsForm A M`

      G |- istp (halts M)
      >>
      G |- of (partial A) M

- `haltsEq A M N`

      G |- eqtp (halts M) (halts N)
      >>
      G |- eq (partial A) M N

- `haltsFormUniv A I M`

      G |- of (univ I) (halts M)
      >>
      G |- of level I
      G |- of (partial A) M

- `haltsEqUniv A I M N`

      G |- eq (univ I) (halts M) (halts N)
      >>
      G |- of level I
      G |- eq (partial A) M N

- `partialIntroBottomOf A`

      G |- of (partial A) bottom
      >>
      G |- istp A

- `bottomDiverges`

      G |- void
      >>
      G |- halts bottom

- `partialExt A M N`

      G |- eq (partial A) M N
      >>
      G |- istp A
      G |- iff (halts M) (halts N)
      G, (halts M) |- eq A[^1] M[^1] N[^1]

- `partialElimEq A M N`

      G |- eq A M N
      >>
      G |- eq (partial A) M N
      G |- halts M

- `partialElimOf A M`

      G |- of A M
      >>
      G |- of (partial A) M
      G |- halts M

- `haltsTrivialize M`

      G |- halts M
      >>
      G |- halts M

- `haltsExt M N P`

      G |- eq (halts M) N P
      >>
      G |- of (halts M) N
      G |- of (halts M) P

- `haltsLeft n C M`

      G1, (halts M), G2 |- C ext N[under_n (^1)]
      >>
      G1, G2[() . id] |- C[under_n (() . id)] ext N

- `haltsValue`

      G |- halts M
      >>
      (where M is valuable)

- `fixpointInductionEq A M N`

      G |- eq (partial A) (fix M) (fix N)
      >>
      G |- eq (arrow (partial A) (partial A)) M N
      G |- admiss A

- `fixpointInductionOf A M`

      G |- of (partial A) (fix M)
      >>
      G |- of (arrow (partial A) (partial A)) M
      G |- admiss A

- `partialFormInv A`

      G |- istp A
      >>
      G |- istp (partial A)

- `seqBind A B M M' N N'`

      G |- eq (partial B) (seq M (fn . N)) (seq M' (fn . N'))
      >>
      G |- eq (partial A) M M'
      G, A |- eq (partial B[^1]) N N'
      G |- istp B

- `activeApp A B M N`

      G |- of (partial B) (M N)
      >>
      G |- of (partial A) M
      G, A |- of (partial B[^1]) (0 N[^1])
      G |- istp B

- `activeAppSeq A B M N`

      G |- eq (partial B) (M N) (seq M (fn . 0 N[^1]))
      >>
      G |- of (partial A) M
      G, A |- of (partial B[^1]) (0 N[^1])
      G |- istp B

- `appHaltsInv M N`

      G |- halts M
      >>
      G |- halts (M N)

- `activePi1 A B M`

      G |- of (partial B) (M #1)
      >>
      G |- of (partial A) M
      G, A |- of (partial B[^1]) (0 #1)
      G |- istp B

- `activePi1Seq A B M`

      G |- eq (partial B) (M #1) (seq M (fn . 0 #1))
      >>
      G |- of (partial A) M
      G, A |- of (partial B[^1]) (0 #1)
      G |- istp B

- `pi1HaltsInv M`

      G |- halts M
      >>
      G |- halts (M #1)

- `activePi2 A B M`

      G |- of (partial B) (M #2)
      >>
      G |- of (partial A) M
      G, A |- of (partial B[^1]) (0 #2)
      G |- istp B

- `activePi2Seq A B M`

      G |- eq (partial B) (M #2) (seq M (fn . 0 #2))
      >>
      G |- of (partial A) M
      G, A |- of (partial B[^1]) (0 #2)
      G |- istp B

- `pi2HaltsInv M`

      G |- halts M
      >>
      G |- halts (M #2)

- `prevHaltsInv M`

      G |- halts M
      >>
      G |- halts (M #prev)

- `activeCase A B M P R`

      G |- of (partial B) (sum_case M (fn . P) (fn . R))
      >>
      G |- of (partial A) M
      G, A |- of (partial B[^1]) (sum_case 0 (fn . P[0 . ^2]) (fn . R[0 . ^2]))
      G |- istp B

- `activeCaseSeq A B M P R`

      G |- eq (partial B) (sum_case M (fn . P) (fn . R)) (seq M (fn . sum_case 0 (fn . P[0 . ^2]) (fn . R[0 . ^2])))
      >>
      G |- of (partial A) M
      G, A |- of (partial B[^1]) (sum_case 0 (fn . P[0 . ^2]) (fn . R[0 . ^2]))
      G |- istp B

- `caseHaltsInv M P R`

      G |- halts M
      >>
      G |- halts (sum_case M (fn . P) (fn . R))

- `seqHaltsSequal M N`

      G |- sequal (seq M (fn . N)) N[M . id]
      >>
      G |- halts M

- `seqHaltsInv M N`

      G |- halts M
      >>
      G |- halts (seq M N)

- `sequalUnderSeq M M' N`

      G |- sequal (seq M (fn . N)) N[M' . id]
      >>
      G |- seq M (fn . sequal 0 M'[^1])

- `totalStrict A`

      G |- subtype A (partial A)
      >>
      G |- istp A
      G, A |- halts 0

- `voidTotal'`

      G |- total void ext fn . ()

- `voidStrict`

      G |- subtype void (partial void)

- `unitTotal M`

      G |- halts M
      >>
      G |- of unit M

- `unitTotal'`

      G |- total unit ext fn . ()

- `unitStrict`

      G |- subtype unit (partial unit)

- `boolTotal M`

      G |- halts M
      >>
      G |- of bool M

- `boolTotal'`

      G |- total bool ext fn . ()

- `boolStrict`

      G |- subtype bool (partial bool)

- `forallTotal A B M`

      G |- halts M
      >>
      G |- of (forall A (fn . B)) M

- `forallTotal' A B`

      G |- total (forall A (fn . B)) ext fn . ()
      >>
      G |- istp A
      G, A |- istp B

- `forallStrict A B`

      G |- subtype (forall A (fn . B)) (partial (forall A (fn . B)))
      >>
      G |- istp A
      G, A |- istp B

- `forallfutTotal A B M`

      G |- halts M
      >>
      G |- of (forallfut A (fn . B)) M

- `forallfutTotal' A B`

      G |- total (forallfut A (fn . B)) ext (() , fn . ())
      >>
      promote(G) |- istp A
      G, (later) A |- istp B

- `forallfutStrict A B`

      G |- subtype (forallfut A (fn . B)) (partial (forallfut A (fn . B)))
      >>
      promote(G) |- istp A
      G, (later) A |- istp B

- `arrowTotal A B M`

      G |- halts M
      >>
      G |- of (arrow A B) M

- `arrowTotal' A B`

      G |- total (arrow A B) ext fn . ()
      >>
      G |- istp A
      G, A |- istp B[^1]

- `arrowStrict A B`

      G |- subtype (arrow A B) (partial (arrow A B))
      >>
      G |- istp A
      G |- istp B

- `intersectStrict A B`

      G |- subtype (intersect A (fn . B)) (partial (intersect A (fn . B)))
      >>
      G |- A
      G, A |- subtype B (partial B)

- `intersectfutStrict A B`

      G |- subtype (intersectfut A (fn . B)) (partial (intersectfut A (fn . B)))
      >>
      promote(G) |- A
      G, (later) A |- subtype B (partial B)

- `parametricTotal A B M`

      G |- halts M
      >>
      G |- of (parametric A (fn . B)) M

- `parametricTotal' A B`

      G |- total (parametric A (fn . B)) ext (() , fn . ())
      >>
      G |- istp A
      G, A |- istp B

- `parametricStrict A B`

      G |- subtype (parametric A (fn . B)) (partial (parametric A (fn . B)))
      >>
      G |- istp A
      G, A |- istp B

- `parametricfutTotal A B M`

      G |- halts M
      >>
      G |- of (parametricfut A (fn . B)) M

- `parametricfutTotal' A B`

      G |- total (parametricfut A (fn . B)) ext (() , fn . ())
      >>
      promote(G) |- istp A
      G, (later) A |- istp B

- `parametricfutStrict A B`

      G |- subtype (parametricfut A (fn . B)) (partial (parametricfut A (fn . B)))
      >>
      promote(G) |- istp A
      G, (later) A |- istp B

- `intersectStrict A B`

      G |- subtype (intersect A (fn . B)) (partial (intersect A (fn . B)))
      >>
      G |- A
      G, A |- subtype B (partial B)

- `intersectfutStrict A B`

      G |- subtype (intersectfut A (fn . B)) (partial (intersectfut A (fn . B)))
      >>
      promote(G) |- A
      G, (later) A |- subtype B (partial B)

- `existsTotal A B M`

      G |- halts M
      >>
      G |- of (exists A (fn . B)) M

- `existsTotal' A B`

      G |- total (exists A (fn . B)) ext fn . ()
      >>
      G |- istp A
      G, A |- istp B

- `existsStrict A B`

      G |- subtype (exists A (fn . B)) (partial (exists A (fn . B)))
      >>
      G |- istp A
      G, A |- istp B

- `prodTotal A B M`

      G |- halts M
      >>
      G |- of (prod A B) M

- `prodTotal' A B`

      G |- total (prod A B) ext fn . ()
      >>
      G |- istp A
      G |- istp B

- `prodStrict A B`

      G |- subtype (prod A B) (partial (prod A B))
      >>
      G |- istp A
      G |- istp B

- `dprodTotal A B M`

      G |- halts M
      >>
      G |- of (dprod A B) M

- `dprodTotal' A B`

      G |- total (dprod A B) ext (() , fn . ())
      >>
      G |- istp A
      G |- istp B

- `dprodStrict A B`

      G |- subtype (dprod A B) (partial (dprod A B))
      >>
      G |- istp A
      G |- istp B

- `sumTotal A B M`

      G |- halts M
      >>
      G |- of (sum A B) M

- `sumTotal' A B`

      G |- total (sum A B) ext fn . ()
      >>
      G |- istp A
      G |- istp B

- `sumStrict A B`

      G |- subtype (sum A B) (partial (sum A B))
      >>
      G |- istp A
      G |- istp B

- `futureTotal A M`

      G |- halts M
      >>
      G |- of (future A) M

- `futureTotal' A`

      G |- total (future A) ext fn . ()
      >>
      promote(G) |- istp A

- `futureStrict A`

      G |- subtype (future A) (partial (future A))
      >>
      promote(G) |- istp A

- `setTotal' A B`

      G |- total (set A (fn . B)) ext (() , fn . ())
      >>
      G, A |- istp B
      G |- total A

- `setStrict A B`

      G |- subtype (set A (fn . B)) (partial (set A (fn . B)))
      >>
      G, A |- istp B
      G |- subtype A (partial A)

- `isetTotal' A B`

      G |- total (iset A (fn . B)) ext (() , fn . ())
      >>
      G, A |- istp B
      G |- total A

- `isetStrict A B`

      G |- subtype (iset A (fn . B)) (partial (iset A (fn . B)))
      >>
      G, A |- istp B
      G |- subtype A (partial A)

- `quotientTotal' A B`

      G |- total (quotient A (fn . fn . B)) ext (() , fn . ())
      >>
      G |- istp (quotient A (fn . fn . B))
      G, A, A[^1] |- istp B
      G |- total A

- `natTotal M`

      G |- halts M
      >>
      G |- of nat M

- `natTotal'`

      G |- total nat ext fn . ()

- `natStrict`

      G |- subtype nat (partial nat)

- `typeHalts A`

      G |- halts A
      >>
      G |- istp A

- `reduceSeqTotal A M N`

      G |- sequal (seq M (fn . N)) N[M . id]
      >>
      G |- of A M
      G |- total A

- `haltsTotal A M`

      G |- halts M
      >>
      G |- of A M
      G |- total A

- `uptypeForm A`

      G |- istp (uptype A)
      >>
      G |- istp A

- `uptypeEq A B`

      G |- eqtp (uptype A) (uptype B)
      >>
      G |- eqtp A B

- `uptypeFormUniv A I`

      G |- of (univ I) (uptype A)
      >>
      G |- of (univ I) A

- `uptypeEqUniv A B I`

      G |- eq (univ I) (uptype A) (uptype B)
      >>
      G |- eq (univ I) A B

- `uptypeTrivialize A`

      G |- uptype A
      >>
      G |- uptype A

- `uptypeExt A M N`

      G |- eq (uptype A) M N
      >>
      G |- of (uptype A) M
      G |- of (uptype A) N

- `uptypeLeft n A B`

      G1, (uptype A), G2 |- B ext M[under_n (^1)]
      >>
      G1, G2[() . id] |- B[under_n (() . id)] ext M

- `uptypeEeqtp A B`

      G |- uptype B
      >>
      G |- uptype A
      G |- eeqtp A B

- `uptypeUnitary A`

      G |- uptype A
      >>
      G |- subtype A unit

- `voidUptype`

      G |- uptype void

- `unitUptype`

      G |- uptype unit

- `boolUptype`

      G |- uptype bool

- `forallUptype A B`

      G |- uptype (forall A (fn . B))
      >>
      G |- istp A
      G, A |- uptype B

- `forallfutUptype A B`

      G |- uptype (forallfut A (fn . B))
      >>
      promote(G) |- istp A
      G, (later) A |- uptype B

- `arrowUptype A B`

      G |- uptype (arrow A B)
      >>
      G |- istp A
      G |- uptype B

- `intersectUptype A B`

      G |- uptype (intersect A (fn . B))
      >>
      G |- istp A
      G, A |- uptype B

- `intersectfutUptype A B`

      G |- uptype (intersectfut A (fn . B))
      >>
      promote(G) |- istp A
      G, (later) A |- uptype B

- `existsUptype A B`

      G |- uptype (exists A (fn . B))
      >>
      G |- uptype A
      G, A |- uptype B

- `prodUptype A B`

      G |- uptype (prod A B)
      >>
      G |- uptype A
      G |- uptype B

- `dprodUptype A B`

      G |- uptype (dprod A B)
      >>
      G |- uptype A
      G, A |- uptype B[^1]

- `sumUptype A B`

      G |- uptype (sum A B)
      >>
      G |- uptype A
      G |- uptype B

- `futureUptype A`

      G |- uptype (future A)
      >>
      promote(G) |- uptype A

- `eqUptype A M N`

      G |- uptype (eq A M N)
      >>
      G |- of A M
      G |- of A N

- `ofUptype A M`

      G |- uptype (of A M)
      >>
      G |- of A M

- `eqtpUptype A B`

      G |- uptype (eqtp A B)
      >>
      G |- istp A
      G |- istp B

- `istpUptype A`

      G |- uptype (istp A)
      >>
      G |- istp A

- `subtypeUptype A B`

      G |- uptype (subtype A B)
      >>
      G |- istp A
      G |- istp B

- `setUptype A B`

      G |- uptype (set A (fn . B))
      >>
      G |- uptype A
      G, A |- istp B

- `isetUptype A B`

      G |- uptype (iset A (fn . B))
      >>
      G |- uptype A
      G, A |- istp B

- `muUptype A`

      G |- uptype (mu (fn . A))
      >>
      G, type |- istp A
      G, type, (uptype 0) |- uptype A[^1]
      G |- positive (fn . A)

- `muUptypeUniv A I`

      G |- uptype (mu (fn . A))
      >>
      G |- of level I
      G, (univ I) |- of (univ I[^1]) A
      G, (univ I), (uptype 0) |- uptype A[^1]
      G |- positive (fn . A)

- `recUptype A`

      G |- uptype (rec (fn . A))
      >>
      G, (later) type |- istp A
      G, (later) type, (later) (uptype 0) |- uptype A[^1]

- `recUptypeUniv A I`

      G |- uptype (rec (fn . A))
      >>
      G |- of level I
      G, (later) (univ I) |- of (univ I[^1]) A
      G, (later) (univ I), (later) (uptype 0) |- uptype A[^1]

- `natUptype`

      G |- uptype nat

- `uptypeFormInv A`

      G |- istp A
      >>
      G |- istp (uptype A)

- `admissForm A`

      G |- istp (admiss A)
      >>
      G |- istp A

- `admissEq A B`

      G |- eqtp (admiss A) (admiss B)
      >>
      G |- eqtp A B

- `admissFormUniv A I`

      G |- of (univ I) (admiss A)
      >>
      G |- of (univ I) A

- `admissEqUniv A B I`

      G |- eq (univ I) (admiss A) (admiss B)
      >>
      G |- eq (univ I) A B

- `admissTrivialize A`

      G |- admiss A
      >>
      G |- admiss A

- `admissExt A M N`

      G |- eq (admiss A) M N
      >>
      G |- of (admiss A) M
      G |- of (admiss A) N

- `admissLeft n A B`

      G1, (admiss A), G2 |- B ext M[under_n (^1)]
      >>
      G1, G2[() . id] |- B[under_n (() . id)] ext M

- `admissEeqtp A B`

      G |- admiss B
      >>
      G |- admiss A
      G |- eeqtp A B

- `uptypeAdmiss A`

      G |- admiss A
      >>
      G |- uptype A

- `partialAdmiss A`

      G |- admiss (partial A)
      >>
      G |- admiss A

- `voidAdmiss`

      G |- admiss void

- `unitAdmiss`

      G |- admiss unit

- `boolAdmiss`

      G |- admiss bool

- `forallAdmiss A B`

      G |- admiss (forall A (fn . B))
      >>
      G |- istp A
      G, A |- admiss B

- `forallfutAdmiss A B`

      G |- admiss (forallfut A (fn . B))
      >>
      promote(G) |- istp A
      G, (later) A |- admiss B

- `arrowAdmiss A B`

      G |- admiss (arrow A B)
      >>
      G |- istp A
      G |- admiss B

- `intersectAdmiss A B`

      G |- admiss (intersect A (fn . B))
      >>
      G |- istp A
      G, A |- admiss B

- `intersectfutAdmiss A B`

      G |- admiss (intersectfut A (fn . B))
      >>
      promote(G) |- istp A
      G, (later) A |- admiss B

- `existsAdmissUptype A B`

      G |- admiss (exists A (fn . B))
      >>
      G |- uptype A
      G, A |- admiss B

- `prodAdmiss A B`

      G |- admiss (prod A B)
      >>
      G |- admiss A
      G |- admiss B

- `dprodAdmissUptype A B`

      G |- admiss (dprod A B)
      >>
      G |- uptype A
      G, A |- admiss B[^1]

- `sumAdmiss A B`

      G |- admiss (sum A B)
      >>
      G |- admiss A
      G |- admiss B

- `futureAdmiss A`

      G |- admiss (future A)
      >>
      promote(G) |- admiss A

- `eqAdmiss A M N`

      G |- admiss (eq A M N)
      >>
      G |- of A M
      G |- of A N

- `ofAdmiss A M`

      G |- admiss (of A M)
      >>
      G |- of A M

- `eqtpAdmiss A B`

      G |- admiss (eqtp A B)
      >>
      G |- istp A
      G |- istp B

- `istpAdmiss A`

      G |- admiss (istp A)
      >>
      G |- istp A

- `subtypeAdmiss A B`

      G |- admiss (subtype A B)
      >>
      G |- istp A
      G |- istp B

- `recAdmiss A`

      G |- admiss (rec (fn . A))
      >>
      G, (later) type |- istp A
      G, (later) type, (later) (admiss 0) |- admiss A[^1]

- `recAdmissUniv A I`

      G |- admiss (rec (fn . A))
      >>
      G |- of level I
      G, (later) (univ I) |- of (univ I[^1]) A
      G, (later) (univ I), (later) (admiss 0) |- admiss A[^1]

- `natAdmiss`

      G |- admiss nat

- `admissFormInv A`

      G |- istp A
      >>
      G |- istp (admiss A)

- `partialType`

      G |- of (intersect level (fn . arrow (univ 0) (univ 0))) partial

- `haltsType`

      G |- of (intersect level (fn . intersect (univ 0) (fn . arrow (partial 0) (univ lzero)))) halts

- `admissType`

      G |- of (intersect level (fn . arrow (univ 0) (univ 0))) admiss

- `uptypeType`

      G |- of (intersect level (fn . arrow (univ 0) (univ 0))) uptype

- `seqType`

      G |- of (intersect level (fn . intersect (univ 0) (fn . intersect (univ 1) (fn . arrow (partial 1) (arrow (arrow 1 (partial 0)) (partial 0)))))) seq


### Let hypotheses

- `letIntro M`

      G |- C ext let M (fn . N)
      >>
      G1, = M |- C[^] ext N

- `letSubst n`

      G1, = M, G2 |- C ext N[under_n (^1)]
      >>
      G1, G2[M . id] |- C[under_n (M . id)] ext N

- `letFold n C`

      G1, = M, G2 |- C[M[^n+1] . id] ext N
      >>
      G1, = M, G2 |- C[n . id] ext N

- `letUnfold n C`

      G1, = M, G2 |- C[n . id] ext N
      >>
      G1, = M, G2 |- C[M[^n+1] . id] ext N

- `letFoldHyp (m+n+1) m H`

      G1, = M, G2, H[M[^n+1] . id], G3 |- C ext N
      >> 
      G1, = M, G2, H[n . id], G3 |- C ext N
      (where m = length(G3) and n = length(G2))

- `letUnfoldHyp (m+n+1) m H`

      G1, = M, G2, H[n . id], G3 |- C ext N
      >> 
      G1, = M, G2, H[M[^n+1] . id], G3 |- C ext N
      (where m = length(G3) and n = length(G2))


### Integers

- `integerForm`

      G |- istp integer

- `integerEq`

      G |- eqtp integer integer

- `integerFormUniv I`

      G |- of (univ I) integer
      >>
      G |- of level I

- `integerEqUniv I`

      G |- eq (univ I) integer integer
      >>
      G |- of level I

- `integerIntroOf`

      G |- of integer M
      (where M is an integer literal)

- `integerIntroEq`

      G |- eq integer M M
      (where M is an integer literal)

- `integerToDefType`

      G |- of (arrow integer Integer) integer_to_def

- `integerFromDefType`

      G |- of (arrow Integer integer) integer_from_def

- `integerIsomorphism1`

      G |- eq (arrow integer integer) (fn . integer_from_Integer (integer_to_Integer 0)) (fn . 0)

- `integerIsomorphism2`

      G |- eq (arrow Integer Integer) (fn . integer_to_Integer (integer_from_Integer 0)) (fn . 0)

- `pluszSpec`

      G |- eq 
             (arrow integer (arrow integer integer))
             plusz
             (fn . fn . integer_from_Integer (Plusz (integer_to_Integer 1) (integer_to_Integer 0)))

- `negzSpec`

      G |- eq 
             (arrow integer integer)
             negz 
             (fn . integer_from_Integer (Negz (integer_to_Integer 0)))

- `eqzbSpec`

      G |- eq
             (arrow integer (arrow integer bool))
             eqzb
             (fn . fn . Eqzb (integer_to_Integer 1) (integer_to_Integer 0))

- `leqzbSpec`

      G |- eq 
             (arrow integer (arrow integer bool))
             leqzb
             (fn . fn . Leqzb (integer_to_Integer 1) (integer_to_Integer 0))

- `timeszSpec`

      G |- eq 
             (arrow integer (arrow integer integer))
             timesz
             (fn . fn . integer_from_Integer (Timesz (integer_to_Integer 1) (integer_to_Integer 0)))

- `integerTotal M`

      G |- halts M
      >>
      G |- of integer M

- `integerStrict`

      G |- subtype integer (partial integer)

- `integerUptype`

      G |- uptype integer

- `integerAdmiss`

      G |- admiss integer

- `integerSequal M N`

      G |- sequal M N
      >>
      G |- eq integer M N


### Symbols

- `symbolForm`

      G |- istp symbol

- `symbolEq`

      G |- eqtp symbol symbol

- `symbolFormUniv I`

      G |- of (univ I) symbol
      >>
      G |- of level I

- `symbolEqUniv I`

      G |- eq (univ I) symbol symbol
      >>
      G |- of level I

- `symbolIntroOf`

      G |- of symbol M
      (where M is an symbol literal)

- `symbolIntroEq`

      G |- eq symbol M M
      (where M is an symbol literal)

- `symbol_eqbType`

      G |- of (arrow symbol (arrow symbol bool)) symbol_eqb

- `symbol_eqbSpec1 M N`

      G |- eq bool (symbol_eqb M N) true
      >>
      G |- eq symbol M N

- `symbol_eqbSpec2 M N`

      G |- eq symbol M N
      >>
      G |- eq bool (symbol_eqb M N) true

- `symbolTotal M`

      G |- halts M
      >>
      G |- of symbol M

- `symbolStrict`

      G |- subtype symbol (partial symbol)

- `symbolUptype`

      G |- uptype symbol

- `symbolAdmiss`

      G |- admiss symbol

- `symbolSequal M N`

      G |- sequal M N
      >>
      G |- eq symbol M N


### Rewriting

This rules are tailor-made to justify certain transformations in the
rewriter, to improve performance and robustness.  (Some of the
justifying derivations are quite large.)

- `eeqtpRefl A`

      G |- eeqtp A A ext (() , ())
      >>
      G |- istp A

- `eeqtpSymm A B`

      G |- eeqtp A B ext (() , ())
      >>
      G |- eeqtp B A

- `eeqtpTrans A B C`

      G |- eeqtp A C ext (() , ())
      >>
      G |- eeqtp A B
      G |- eeqtp B C

- `weakenEqtpEeqtp A B`

      G |- eeqtp A B ext (() , ())
      >>
      G |- eqtp A B

- `weakenSubtypeArrow A B`

      G |- arrow A B ext fn . 0
      >>
      G |- subtype A B

- `weakenEeqtpIff A B`

      G |- iff A B ext (fn . 0 , fn . 0)
      >>
      G |- eeqtp A B

- `compatGuardEqtp1 A B B'`

      G |- eqtp (guard A B) (guard A B')
      >>
      G |- istp A
      G |- eqtp B B'

- `compatSetEqtp0 A A' B`

      G |- eqtp (set A (fn . B)) (set A' (fn . B))
      >>
      G |- eqtp A A'
      G, A |- istp B

- `forallEeq A A' B B'`

      G |- eeqtp (forall A (fn . B)) (forall A' (fn . B')) ext (() , ())
      >>
      G |- eeqtp A A'
      G, A |- eeqtp B B'

- `existsEeq A A' B B'`

      G |- eeqtp (exists A (fn . B)) (exists A' (fn . B')) ext (() , ())
      >>
      G |- eeqtp A A'
      G, A |- eeqtp B B'

- `arrowEeq A A' B B'`

      G |- eeqtp (arrow A B) (arrow A' B') ext (() , ())
      >>
      G |- eeqtp A A'
      G |- eeqtp B B'

- `prodEeq A A' B B'`

      G |- eeqtp (prod A B) (prod A' B') ext (() , ())
      >>
      G |- eeqtp A A'
      G |- eeqtp B B'

- `dprodEeq A A' B B'`

      G |- eeqtp (dprod A B) (dprod A' B') ext (() , ())
      >>
      G |- eeqtp A A'
      G, A |- eeqtp B[^1] B'[^1]

- `sumEeq A A' B B'`

      G |- eeqtp (sum A B) (sum A' B') ext (() , ())
      >>
      G |- eeqtp A A'
      G |- eeqtp B B'

- `futureEeq A A'`

      G |- eeqtp (future A) (future A') ext (() , ())
      >>
      promote(G) |- eeqtp A A'

- `intersectEeq A A' B B'`

      G |- eeqtp (intersect A (fn . B)) (intersect A' (fn . B')) ext (() , ())
      >>
      G |- eeqtp A A'
      G, A |- eeqtp B B'

- `unionEeq A A' B B'`

      G |- eeqtp (union A (fn . B)) (union A' (fn . B')) ext (() , ())
      >>
      G |- eeqtp A A'
      G, A |- eeqtp B B'

- `compatGuardEeq1 A B B'`

      G |- eeqtp (guard A B) (guard A B') ext (() , ())
      >>
      G |- istp A
      G |- eeqtp B B'

- `compatSetEeq0 A A' B`

      G |- eeqtp (set A (fn . B)) (set A' (fn . B)) ext (() , ())
      >>
      G |- eeqtp A A'
      G, A |- istp B

- `compatIsetEeq0 A A' B`

      G |- eeqtp (iset A (fn . B)) (iset A' (fn . B)) ext (() , ())
      >>
      G |- eeqtp A A'
      G, A |- istp B

- `compatIsetIff1 A B B'`

      G |- eeqtp (iset A (fn . B)) (iset A (fn . B')) ext (() , ())
      >>
      G |- istp A
      G, A |- iff B B'

- `compatForallSubtype0 A A' B`

      G |- subtype (forall A (fn . B)) (forall A' (fn . B))
      >>
      G |- subtype A' A
      G, A |- istp B

- `compatForallSubtype1 A B B'`

      G |- subtype (forall A (fn . B)) (forall A (fn . B'))
      >>
      G |- istp A
      G, A |- subtype B B'

- `compatExistsSubtype0 A A' B`

      G |- subtype (exists A (fn . B)) (exists A' (fn . B))
      >>
      G |- subtype A A'
      G, A' |- istp B

- `compatExistsSubtype1 A B B'`

      G |- subtype (exists A (fn . B)) (exists A (fn . B'))
      >>
      G |- istp A
      G, A |- subtype B B'

- `compatIntersectSubtype0 A A' B`

      G |- subtype (intersect A (fn . B)) (intersect A' (fn . B))
      >>
      G |- subtype A' A
      G, A |- istp B

- `compatIntersectSubtype1 A B B'`

      G |- subtype (intersect A (fn . B)) (intersect A (fn . B'))
      >>
      G |- istp A
      G, A |- subtype B B'

- `compatUnionSubtype0 A A' B`

      G |- subtype (union A (fn . B)) (union A' (fn . B))
      >>
      G |- subtype A A'
      G, A' |- istp B

- `compatUnionSubtype1 A B B'`

      G |- subtype (union A (fn . B)) (union A (fn . B'))
      >>
      G |- istp A
      G, A |- subtype B B'

- `compatGuardArrow0 A A' B`

      G |- subtype (guard A B) (guard A' B)
      >>
      G |- istp A
      G |- istp B
      G |- arrow A' A

- `compatGuardSubtype1 A B B'`

      G |- subtype (guard A B) (guard A B')
      >>
      G |- istp A
      G |- subtype B B'

- `compatSetSubtype0 A A' B`

      G |- subtype (set A (fn . B)) (set A' (fn . B))
      >>
      G |- subtype A A'
      G, A' |- istp B

- `compatSetArrow1 A B B'`

      G |- subtype (set A (fn . B)) (set A (fn . B'))
      >>
      G |- istp A
      G, A |- istp B'
      G, A |- arrow B B'

- `compatIsetSubtype0 A A' B`

      G |- subtype (iset A (fn . B)) (iset A' (fn . B))
      >>
      G |- subtype A A'
      G, A' |- istp B

- `compatIsetArrow1 A B B'`

      G |- subtype (iset A (fn . B)) (iset A (fn . B'))
      >>
      G |- istp A
      G, A |- istp B'
      G, A |- arrow B B'

- `compatForallIff1 A B B'`

      G |- iff (forall A (fn . B)) (forall A (fn . B')) ext (fn . fn . M[0 . ^2] #1 (1 0) , fn . fn . M[0 . ^2] #2 (1 0))
      >>
      G |- istp A
      G, A |- iff B B' ext M

- `compatExistsIff1 A B B'`

      G |- iff (exists A (fn . B)) (exists A (fn . B')) ext (fn . (0 #1 , M[0 #1 . ^1] #1 (0 #2)) , fn . (0 #1 , M[0 #1 . ^1] #2 (0 #2)))
      >>
      G |- istp A
      G, A |- iff B B' ext M

- `compatArrowIff0 A A' B`

      G |- iff (arrow A B) (arrow A' B) ext (fn . fn . 1 (M[^2] #2 0) , fn . fn . 1 (M[^2] #1 0))
      >>
      G |- istp B
      G |- iff A A' ext M

- `compatArrowIff1 A B B'`

      G |- iff (arrow A B) (arrow A B') ext (fn . fn . M[^2] #1 (1 0) , fn . fn . M[^2] #2 (1 0))
      >>
      G |- istp A
      G |- iff B B' ext M

- `compatProdIff0 A A' B`

      G |- iff (prod A B) (prod A' B) ext (fn . (M[^1] #1 (0 #1) , 0 #2) , fn . (M[^1] #2 (0 #1) , 0 #2))
      >>
      G |- istp B
      G |- iff A A' ext M

- `compatProdIff1 A B B'`

      G |- iff (prod A B) (prod A B') ext (fn . (0 #1 , M[^1] #1 (0 #2)) , fn . (0 #1 , M[^1] #2 (0 #2)))
      >>
      G |- istp A
      G |- iff B B' ext M

- `compatDprodIff0 A A' B`

      G |- iff (dprod A B) (dprod A' B) ext (fn . (M[^1] #1 (0 #1) , 0 #2) , fn . (M[^1] #2 (0 #1) , 0 #2))
      >>
      G, A |- istp B[^1]
      G |- iff A A' ext M

- `compatDprodIff1 A B B'`

      G |- iff (dprod A B) (dprod A B') ext (fn . (0 #1 , M[^1] #1 (0 #2)) , fn . (0 #1 , M[^1] #2 (0 #2)))
      >>
      G |- istp A
      G |- iff B B' ext M

- `compatSumIff0 A A' B`

      G |- iff (sum A B) (sum A' B) ext (fn . sum_case 0 (fn . inl (M[^2] #1 0)) (fn . inr 0) , fn . sum_case 0 (fn . inl (M[^2] #2 0)) (fn . inr 0))
      >>
      G |- istp B
      G |- iff A A' ext M

- `compatSumIff1 A B B'`

      G |- iff (sum A B) (sum A B') ext (fn . sum_case 0 (fn . inl 0) (fn . inr (M[^2] #1 0)) , fn . sum_case 0 (fn . inl 0) (fn . inr (M[^2] #2 0)))
      >>
      G |- istp A
      G |- iff B B' ext M

- `compatFutureIff A A'`

      G |- iff (future A) (future A') ext (fn . letnext 0 (fn . next (M[^2] #1 0)) , fn . letnext 0 (fn . next (M[^2] #2 0)))
      >>
      promote(G) |- iff A A' ext M

- `compatForallArrow1 A B B'`

      G |- arrow (forall A (fn . B)) (forall A (fn . B')) ext fn . fn . M[0 . ^2] (1 0)
      >>
      G |- istp A
      G, A |- arrow B B' ext M

- `compatExistsArrow1 A B B'`

      G |- arrow (exists A (fn . B)) (exists A (fn . B')) ext fn . (0 #1 , M[0 #1 . ^1] (0 #2))
      >>
      G |- istp A
      G, A |- istp B'
      G, A |- arrow B B' ext M

- `compatArrowArrow0 A A' B`

      G |- arrow (arrow A B) (arrow A' B) ext fn . fn . 1 (M[^2] 0)
      >>
      G |- istp A
      G |- istp B
      G |- arrow A' A ext M

- `compatArrowArrow1 A B B'`

      G |- arrow (arrow A B) (arrow A B') ext fn . fn . M[^2] (1 0)
      >>
      G |- istp A
      G |- arrow B B' ext M

- `compatProdArrow0 A A' B`

      G |- arrow (prod A B) (prod A' B) ext fn . (M[^1] (0 #1) , 0 #2)
      >>
      G |- istp B
      G |- arrow A A' ext M

- `compatProdArrow1 A B B'`

      G |- arrow (prod A B) (prod A B') ext fn . (0 #1 , M[^1] (0 #2))
      >>
      G |- istp A
      G |- arrow B B' ext M

- `compatDprodArrow0 A A' B`

      G |- arrow (dprod A B) (dprod A' B) ext fn . (M[^1] (0 #1) , 0 #2)
      >>
      G |- istp B
      G |- arrow A A' ext M

- `compatDprodArrow1 A B B'`

      G |- arrow (dprod A B) (dprod A B') ext fn . (0 #1 , M[^1] (0 #2))
      >>
      G |- istp A
      G |- arrow B B' ext M

- `compatSumArrow0 A A' B`

      G |- arrow (sum A B) (sum A' B) ext fn . sum_case 0 (fn . inl (M[^2] 0)) (fn . inr 0)
      >>
      G |- istp A'
      G |- istp B
      G |- arrow A A' ext M

- `compatSumArrow1 A B B'`

      G |- arrow (sum A B) (sum A B') ext fn . sum_case 0 (fn . inl 0) (fn . inr (M[^2] 0))
      >>
      G |- istp A
      G |- istp B'
      G |- arrow B B' ext M

- `compatFutureArrow A A'`

      G |- arrow (future A) (future A') ext fn . letnext 0 (fn . next (M[^2] 0))
      >>
      promote(G) |- arrow A A' ext M

- `compatForallEntails1 A B B'`

      G |- forall A (fn . B') ext fn . M[F[^1] 0 . id]
      >>
      G, A, B |- B'[^1] ext M
      G |- forall A (fn . B) ext F

- `compatArrowEntails1 A B B'`

      G |- arrow A B' ext fn . M[F[^1] 0 . ^1]
      >>
      G, B |- B'[^1] ext M
      G |- arrow A B ext F

- `compatProdEntails0 A A' B`

      G |- prod A' B ext (M[P #1 . id] , P #2)
      >>
      G, A |- A'[^1] ext M
      G |- prod A B ext P

- `compatProdEntails1 A B B'`

      G |- prod A B' ext (P #1 , M[P #2 . id])
      >>
      G, B |- B'[^1] ext M
      G |- prod A B ext P

- `compatDprodEntails0 A A' B`

      G |- dprod A' B ext (M[P #1 . id] , P #2)
      >>
      G, A |- A'[^1] ext M
      G |- dprod A B ext P

- `compatDprodEntails1 A B B'`

      G |- dprod A B' ext (P #1 , M[P #2 . id])
      >>
      G, B |- B'[^1] ext M
      G |- dprod A B ext P
