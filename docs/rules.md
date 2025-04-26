# Istari rules

Conventions:

- A rule is written `[conclusion] >> [premise] ... [premise]`.
  When a rule has no premises, the `>>` is omitted.

- The variables a metavariable may depend on is the intersection of
  the variables in scope in each of its appearances.

- The argument `n` is the length of the context `G2`, in rules where
  `G2` appears.

- Omitted extracts in the conclusion are taken to be `()`.  Omitted
  extracts in premises are unused.

Note that no effort was made to keep the set of rules minimal.  Many
rules that would follow from other rules are nonetheless included for
the sake of convenience or performance.  Since (nearly) all the rules
are verified, there is no robustness advantage to minimizing the set
of rules.

Rules are given here in human-readable format, using explicit
variables.  The official rules, using de Bruijn indices, are given
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
[Couarded types](#coguarded-types)<br>
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

      G1, x : A, G2 |- A ext x

- `hypothesisOf n`

      G1, x : A, G2 |- x : A

- `hypothesisEq n`

      G1, x : A, G2 |- x = x : A

- `hypothesisOfTp n`

      G1, x : type, G2 |- x : type

- `hypothesisEqTp n`

      G1, x : type, G2 |- x = x : type

- `weaken m n` 

      G1, G2, G3 |- A ext M
      >>
      G1, G3 |- A ext M
      (where m = length(G3) and n = length(G2))

- `exchange l m n` 

      G1, G2, G3, G4 |- A ext M
      >>
      G1, G3, G2, G4 |- A ext M
      (where l = length(G4), m = length(G3), n = length(G2))


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

      G |- [M / x]C ext P
      >>
      G |- [N / x]C ext P
      (where red reduces M to N, x is the ith variable in C's scope)

- `unreduceAt i C M red`

      G |- [N / x]C ext P
      >>
      G |- [M / x]C ext P
      (where red reduces M to N, x is the ith variable in C's scope)

- `reduceHyp n red`

      G1, y : C, G2 |- C ext M
      >>
      G1, y : D, G2 |- C ext M
      (where red reduces C to D)

- `unreduceHyp n C red`

      G1, y : D, G2 |- C ext M
      >>
      G1, y : C, G2 |- C ext M
      (where red reduces C to D)

- `reduceHypAt n i H M red`

      G1, y : [M / x]H, G2 |- C ext P
      >>
      G1, y : [N / x]H, G2 |- C ext P
      (where red reduces M to N, x is the ith variable in H's scope)

- `unreduceHypAt n i H M red`

      G1, y : [N / x]H, G2 |- C ext P
      >>
      G1, y : [M / x]H, G2 |- C ext P
      (where red reduces M to N, x is the ith variable in H's scope)

- `whnfConcl`

      G |- C ext M
      >>
      G |- D ext M
      (where the weak-head normal form of C is D)

- `whnfHyp n`

      G1, x : H, G2 |- C ext M
      >>
      G1, x : H', G2 |- C ext M
      (where the weak-head normal form of H is H')

- `whnfHardConcl`

      G |- C ext M
      >>
      G |- D ext M
      (where the hard weak-head normal form of C is D)

- `whnfHardHyp n`

      G1, x : H, G2 |- C ext M
      >>
      G1, x : H', G2 |- C ext M
      (where the hard weak-head normal form of H is H')

- `normalizeConcl`

      G |- C ext M
      >>
      G |- D ext M
      (where the normal form of C is D)

- `normalizeHyp n`

      G1, x : H, G2 |- C ext M
      >>
      G1, x : H', G2 |- C ext M
      (where the normal form of H is H')

- `whnfConclAt path`

      G |- C ext M
      >>
      G |- C' ext M
      (where C' is obtained from C by weak-head normalizing a subterm determined by path)

- `whnfHypAt n path`

      G1, x : H, G2 |- C ext M
      >>
      G1, x : H', G2 |- C' ext M
      (where H' is obtained from H by weak-head normalizing a subterm determined by path)


### Dependent functions

- `forallForm A B`

      G |- (forall (x : A) . B) : type
      >>
      G |- A : type
      G, x : A |- B : type

- `forallEq A A' B B'`

      G |- (forall (x : A) . B) = (forall (x : A') . B') : type
      >>
      G |- A = A' : type
      G, x : A |- B = B' : type

- `forallFormUniv A B I`

      G |- (forall (x : A) . B) : univ I
      >>
      G |- A : univ I
      G, x : A |- B : univ I

- `forallEqUniv A A' B B' I`

      G |- (forall (x : A) . B) = (forall (x : A') . B') : univ I
      >>
      G |- A = A' : univ I
      G, x : A |- B = B' : univ I

- `forallSub A A' B B'`

      G |- (forall (x : A) . B) <: (forall (x : A') . B')
      >>
      G |- A' <: A
      G, x : A' |- B <: B'
      G, x : A |- B : type

- `forallIntroOf A B M`

      G |- (fn x . M) : forall (x : A) . B
      >>
      G |- A : type
      G, x : A |- M : B

- `forallIntroEq A B M N`

      G |- (fn x . M) = (fn x . N) : (forall (x : A) . B)
      >>
      G |- A : type
      G, x : A |- M = N : B

- `forallIntro A B`

      G |- forall (x : A) . B ext fn x . M
      >>
      G |- A : type
      G, x : A |- B ext M

- `forallElimOf A B M P`

      G |- M P : [P / x]B
      >>
      G |- M : forall (x : A) . B
      G |- P : A

- `forallElimEq A B M N P Q`

      G |- M P = N Q : [P / x]B
      >>
      G |- M = N : (forall (x : A) . B)
      G |- P = Q : A

- `forallElim A B P`

      G |- [P / x]B ext M P
      >>
      G |- forall (x : A) . B ext M
      G |- P : A

- `forallEta A B M`

      G |- M = (fn x . M x) : (forall (x : A) . B)
      >>
      G |- M : forall (x : A) . B

- `forallExt A B M N`

      G |- M = N : (forall (x : A) . B)
      >>
      G |- M : forall (x : A) . B
      G |- N : forall (x : A) . B
      G, x : A |- M x = N x : B

- `forallExt' A A' A'' B B' B'' M N`

      G |- M = N : (forall (x : A) . B)
      >>
      G |- A : type
      G |- M : forall (x : A') . B'
      G |- N : forall (x : A'') . B''
      G, x : A |- M x = N x : B

- `forallOfExt A A' B B' M`

      G |- M : forall (x : A) . B
      >>
      G |- A : type
      G |- M : forall (x : A') . B'
      G, x : A |- M x : B

- `forallFormInv1 A B`

      G |- A : type
      >>
      G |- (forall (x : A) . B) : type

- `forallFormInv2 A B M`

      G |- [M / x]B : type
      >>
      G |- (forall (x : A) . B) : type
      G |- M : A


### Functions

- `arrowForm A B`

      G |- (A -> B) : type
      >>
      G |- A : type
      G, x : A |- B : type

- `arrowEq A A' B B'`

      G |- (A -> B) = (A' -> B') : type
      >>
      G |- A = A' : type
      G, x : A |- B = B' : type

- `arrowFormUniv A B I`

      G |- (A -> B) : univ I
      >>
      G |- A : univ I
      G, x : A |- B : univ I

- `arrowEqUniv A A' B B' I`

      G |- (A -> B) = (A' -> B') : univ I
      >>
      G |- A = A' : univ I
      G, x : A |- B = B' : univ I

- `arrowForallEq A A' B B'`

      G |- (A -> B) = (forall (x : A') . B') : type
      >>
      G |- A = A' : type
      G, x : A |- B = B' : type

- `arrowForallEqUniv A A' B B' I`

      G |- (A -> B) = (forall (x : A') . B') : univ I
      >>
      G |- A = A' : univ I
      G, x : A |- B = B' : univ I

- `arrowSub A A' B B'`

      G |- (A -> B) <: (A' -> B')
      >>
      G |- A' <: A
      G |- B <: B'

- `arrowForallSub A A' B B'`

      G |- (A -> B) <: (forall (x : A') . B')
      >>
      G |- A' <: A
      G, x : A' |- B <: B'
      G |- B : type

- `forallArrowSub A A' B B'`

      G |- (forall (x : A) . B) <: (A' -> B')
      >>
      G |- A' <: A
      G, x : A' |- B <: B'
      G, x : A |- B : type

- `arrowIntroOf A B M`

      G |- (fn x . M) : A -> B
      >>
      G |- A : type
      G, x : A |- M : B

- `arrowIntroEq A B M N`

      G |- (fn x . M) = (fn x . N) : (A -> B)
      >>
      G |- A : type
      G, x : A |- M = N : B

- `arrowIntro A B`

      G |- A -> B ext fn x . M
      >>
      G |- A : type
      G, x : A |- B ext M

- `arrowElimOf A B M P`

      G |- M P : B
      >>
      G |- M : A -> B
      G |- P : A

- `arrowElimEq A B M N P Q`

      G |- M P = N Q : B
      >>
      G |- M = N : (A -> B)
      G |- P = Q : A

- `arrowElim A B`

      G |- B ext M P
      >>
      G |- A -> B ext M
      G |- A ext P

- `arrowEta A B M`

      G |- M = (fn x . M x) : (A -> B)
      >>
      G |- M : A -> B

- `arrowExt A B M N`

      G |- M = N : (A -> B)
      >>
      G |- M : A -> B
      G |- N : A -> B
      G, x : A |- M x = N x : B

- `arrowExt' A A' A'' B B' B'' M N`

      G |- M = N : (A -> B)
      >>
      G |- A : type
      G |- M : forall (x : A') . B'
      G |- N : forall (x : A'') . B''
      G, x : A |- M x = N x : B

- `arrowOfExt A A' B B' M`

      G |- M : A -> B
      >>
      G |- A : type
      G |- M : forall (x : A') . B'
      G, x : A |- M x : B

- `arrowFormInv1 A B`

      G |- A : type
      >>
      G |- (A -> B) : type

- `arrowFormInv2 A B M`

      G |- B : type
      >>
      G |- (A -> B) : type
      G |- M : A


### T-Functions

- `tarrowKind A I K`

      G |- (A -t> K) : kind I
      >>
      G |- A : univ I
      G |- K : kind I

- `tarrowKindEq A A' I K K'`

      G |- (A -t> K) = (A' -t> K') : kind I
      >>
      G |- A = A' : univ I
      G |- K = K' : kind I

- `tarrowForm A B`

      G |- (A -t> B) : type
      >>
      G |- A : type
      G |- B : type

- `tarrowEq A A' B B'`

      G |- (A -t> B) = (A' -t> B') : type
      >>
      G |- A = A' : type
      G |- B = B' : type

- `tarrowFormUniv A B I`

      G |- (A -t> B) : univ I
      >>
      G |- A : univ I
      G |- B : univ I

- `tarrowEqUniv A A' B B' I`

      G |- (A -t> B) = (A' -t> B') : univ I
      >>
      G |- A = A' : univ I
      G |- B = B' : univ I

- `tarrowArrowEq A A' B B'`

      G |- (A -t> B) = (A' -> B') : type
      >>
      G |- A = A' : type
      G |- B = B' : type

- `tarrowArrowEqUniv A A' B B' I`

      G |- (A -t> B) = (A' -> B') : univ I
      >>
      G |- A = A' : univ I
      G |- B = B' : univ I

- `tarrowForallEq A A' B B'`

      G |- (A -t> B) = (forall (x : A') . B') : type
      >>
      G |- A = A' : type
      G, x : A |- B = B' : type
      G |- B : type

- `tarrowForallEqUniv A A' B B' I`

      G |- (A -t> B) = (forall (x : A') . B') : univ I
      >>
      G |- A = A' : univ I
      G, x : A |- B = B' : univ I
      G |- B : univ I

- `tarrowIntroOf A B M`

      G |- (fn x . M) : A -t> B
      >>
      G |- A : type
      G |- B : type
      G, x : A |- M : B

- `tarrowIntroEq A B M N`

      G |- (fn x . M) = (fn x . N) : (A -t> B)
      >>
      G |- A : type
      G |- B : type
      G, x : A |- M = N : B

- `tarrowIntro A B`

      G |- A -t> B ext fn x . M
      >>
      G |- A : type
      G |- B : type
      G, x : A |- B ext M

- `tarrowElimOf A B M P`

      G |- M P : B
      >>
      G |- M : A -t> B
      G |- P : A

- `tarrowElimEq A B M N P Q`

      G |- M P = N Q : B
      >>
      G |- M = N : (A -t> B)
      G |- P = Q : A

- `tarrowElim A B`

      G |- B ext M P
      >>
      G |- A -t> B ext M
      G |- A ext P

- `tarrowEta A B M`

      G |- M = (fn x . M x) : (A -t> B)
      >>
      G |- M : A -t> B

- `tarrowExt A B M N`

      G |- M = N : (A -t> B)
      >>
      G |- B : type
      G |- M : A -t> B
      G |- N : A -t> B
      G, x : A |- M x = N x : B

- `tarrowOfExt A A' B B' M`

      G |- M : A -t> B
      >>
      G |- A : type
      G |- B : type
      G |- M : forall (x : A') . B'
      G, x : A |- M x : B


### K-Functions

- `karrowKind I K L`

      G |- (K -k> L) : kind I
      >>
      G |- K : kind I
      G |- L : kind I

- `karrowKindEq I K K' L L'`

      G |- (K -k> L) = (K' -k> L') : kind I
      >>
      G |- K = K' : kind I
      G |- L = L' : kind I

- `karrowForm A B`

      G |- (A -k> B) : type
      >>
      G |- A : type
      G |- B : type

- `karrowEq A A' B B'`

      G |- (A -k> B) = (A' -k> B') : type
      >>
      G |- A = A' : type
      G |- B = B' : type

- `karrowFormUniv A B I`

      G |- (A -k> B) : univ I
      >>
      G |- A : univ I
      G |- B : univ I

- `karrowEqUniv A A' B B' I`

      G |- (A -k> B) = (A' -k> B') : univ I
      >>
      G |- A = A' : univ I
      G |- B = B' : univ I

- `karrowArrowEq A A' B B'`

      G |- (A -k> B) = (A' -> B') : type
      >>
      G |- A = A' : type
      G |- B = B' : type

- `karrowArrowEqUniv A A' B B' I`

      G |- (A -k> B) = (A' -> B') : univ I
      >>
      G |- A = A' : univ I
      G |- B = B' : univ I

- `karrowForallEq A A' B B'`

      G |- (A -k> B) = (forall (x : A') . B') : type
      >>
      G |- A = A' : type
      G, x : A |- B = B' : type
      G |- B : type

- `karrowForallEqUniv A A' B B' I`

      G |- (A -k> B) = (forall (x : A') . B') : univ I
      >>
      G |- A = A' : univ I
      G, x : A |- B = B' : univ I
      G |- B : univ I

- `karrowIntroOf A B M`

      G |- (fn x . M) : A -k> B
      >>
      G |- A : type
      G |- B : type
      G, x : A |- M : B

- `karrowIntroEq A B M N`

      G |- (fn x . M) = (fn x . N) : (A -k> B)
      >>
      G |- A : type
      G |- B : type
      G, x : A |- M = N : B

- `karrowIntro A B`

      G |- A -k> B ext fn x . M
      >>
      G |- A : type
      G |- B : type
      G, x : A |- B ext M

- `karrowElimOf A B M P`

      G |- M P : B
      >>
      G |- M : A -k> B
      G |- P : A

- `karrowElimEq A B M N P Q`

      G |- M P = N Q : B
      >>
      G |- M = N : (A -k> B)
      G |- P = Q : A

- `karrowElim A B`

      G |- B ext M P
      >>
      G |- A -k> B ext M
      G |- A ext P

- `karrowEta A B M`

      G |- M = (fn x . M x) : (A -k> B)
      >>
      G |- M : A -k> B

- `karrowExt A B M N`

      G |- M = N : (A -k> B)
      >>
      G |- B : type
      G |- M : A -k> B
      G |- N : A -k> B
      G, x : A |- M x = N x : B

- `karrowOfExt A A' B B' M`

      G |- M : A -k> B
      >>
      G |- A : type
      G |- B : type
      G |- M : forall (x : A') . B'
      G, x : A |- M x : B


### Intersection types

- `intersectForm A B`

      G |- (intersect (x : A) . B) : type
      >>
      G |- A : type
      G, x : A |- B : type

- `intersectEq A A' B B'`

      G |- (intersect (x : A) . B) = (intersect (x : A') . B') : type
      >>
      G |- A = A' : type
      G, x : A |- B = B' : type

- `intersectFormUniv A B I`

      G |- (intersect (x : A) . B) : univ I
      >>
      G |- A : univ I
      G, x : A |- B : univ I

- `intersectEqUniv A A' B B' I`

      G |- (intersect (x : A) . B) = (intersect (x : A') . B') : univ I
      >>
      G |- A = A' : univ I
      G, x : A |- B = B' : univ I

- `intersectSub A A' B B'`

      G |- (intersect (x : A) . B) <: (intersect (x : A') . B')
      >>
      G |- A' <: A
      G, x : A' |- B <: B'
      G, x : A |- B : type

- `intersectIntroOf A B M`

      G |- M : intersect (x : A) . B
      >>
      G |- A : type
      G, x : A |- M : B

- `intersectIntroEq A B M N`

      G |- M = N : (intersect (x : A) . B)
      >>
      G |- A : type
      G, x : A |- M = N : B

- `intersectIntro A B`

      G |- intersect (x : A) . B ext [() / x]M
      >>
      G |- A : type
      G, x (hidden) : A |- B ext M

- `intersectElimOf A B M P`

      G |- M : [P / x]B
      >>
      G |- M : intersect (x : A) . B
      G |- P : A

- `intersectElimEq A B M N P`

      G |- M = N : [P / x]B
      >>
      G |- M = N : (intersect (x : A) . B)
      G |- P : A

- `intersectElim A B P`

      G |- [P / x]B ext M
      >>
      G |- intersect (x : A) . B ext M
      G |- P : A

- `intersectFormInv1 A B`

      G |- A : type
      >>
      G |- (intersect (x : A) . B) : type

- `intersectFormInv2 A B M`

      G |- [M / x]B : type
      >>
      G |- (intersect (x : A) . B) : type
      G |- M : A


### Parametric functions

- `parametricForm A B`

      G |- parametric A (fn x . B) : type
      >>
      G |- A : type
      G, x : A |- B : type

- `parametricEq A A' B B'`

      G |- parametric A (fn x . B) = parametric A' (fn x . B') : type
      >>
      G |- A = A' : type
      G, x : A |- B = B' : type

- `parametricFormUniv A B I`

      G |- parametric A (fn x . B) : univ I
      >>
      G |- A : univ I
      G, x : A |- B : univ I

- `parametricEqUniv A A' B B' I`

      G |- parametric A (fn x . B) = parametric A' (fn x . B') : univ I
      >>
      G |- A = A' : univ I
      G, x : A |- B = B' : univ I

- `parametricSub A A' B B'`

      G |- parametric A (fn x . B) <: parametric A' (fn x . B')
      >>
      G |- A' <: A
      G, x : A' |- B <: B'
      G, x : A |- B : type

- `parametricForallSub A A' B B'`

      G |- parametric A (fn x . B) <: (forall (x : A') . B')
      >>
      G |- A' <: A
      G, x : A' |- B <: B'
      G, x : A |- B : type

- `parametricIntroOf A B M`

      G |- (fn x . M) : parametric A (fn x . B)
      >>
      G |- A : type
      G |- irrelevant (fn x . M)
      G, x : A |- M : B

- `parametricIntroEq A B M N`

      G |- (fn x . M) = (fn x . N) : parametric A (fn x . B)
      >>
      G |- A : type
      G |- irrelevant (fn x . M)
      G |- irrelevant (fn x . N)
      G, x : A |- M = N : B

- `parametricIntro A B`

      G |- parametric A (fn x . B) ext fn x . M
      >>
      G |- A : type
      G, x (hidden) : A |- B ext M

- `parametricIntroOfForall A B M`

      G |- M : parametric A (fn x . B)
      >>
      G |- M : forall (x : A) . B
      G |- irrelevant (fn x . M x)

- `parametricElimOf A B M P`

      G |- paramapp M P : [P / x]B
      >>
      G |- M : parametric A (fn x . B)
      G |- P : A

- `parametricElimEq A B M N P Q`

      G |- paramapp M P = paramapp N Q : [P / x]B
      >>
      G |- M = N : parametric A (fn x . B)
      G |- P = Q : A

- `parametricElim A B P`

      G |- [P / x]B ext paramapp M P
      >>
      G |- parametric A (fn x . B) ext M
      G |- P : A

- `parametricElim' A B P`

      G |- [P / x]B ext paramapp M unavailable
      >>
      G |- parametric A (fn x . B) ext M
      G |- P : A

- `parametricBeta M N`

      G |- sequal (paramapp (fn x . M) N) [N / x]M
      >>
      G |- irrelevant (fn x . M)

- `parametricEta A B M`

      G |- M = (fn x . paramapp M x) : parametric A (fn x . B)
      >>
      G |- M : parametric A (fn x . B)

- `parametricExt A B M N`

      G |- M = N : parametric A (fn x . B)
      >>
      G |- M : parametric A (fn x . B)
      G |- N : parametric A (fn x . B)
      G, x : A |- paramapp M x = paramapp N x : B

- `parametricExt' A A' A'' B B' B'' M N`

      G |- M = N : parametric A (fn x . B)
      >>
      G |- A : type
      G |- M : parametric A' (fn x . B')
      G |- N : parametric A'' (fn x . B'')
      G, x : A |- paramapp M x = paramapp N x : B

- `parametricOfExt A A' B B' M`

      G |- M : parametric A (fn x . B)
      >>
      G |- A : type
      G |- M : parametric A' (fn x . B')
      G, x : A |- paramapp M x : B

- `parametricFormInv1 A B`

      G |- A : type
      >>
      G |- parametric A (fn x . B) : type

- `parametricFormInv2 A B M`

      G |- [M / x]B : type
      >>
      G |- parametric A (fn x . B) : type
      G |- M : A

- `parametricElimIrrelevant M P Q`

      G |- sequal (paramapp M P) (paramapp M Q)

- `irrelevance M`

      G |- irrelevant (fn x . M)
      >>
      G, y : nonsense |- sequal [y / x]M [unavailable / x]M


### Guarded types

- `guardForm A B`

      G |- (A -g> B) : type
      >>
      G |- A : type
      G, x : A |- B : type

- `guardEq A A' B B'`

      G |- (A -g> B) = (A' -g> B') : type
      >>
      G |- iff A A'
      G, x : A |- B = B' : type

- `guardFormUniv A B I`

      G |- (A -g> B) : univ I
      >>
      G |- A : univ I
      G, x : A |- B : univ I

- `guardEqUniv A A' B B' I`

      G |- (A -g> B) = (A' -g> B') : univ I
      >>
      G |- A : univ I
      G |- A' : univ I
      G |- iff A A'
      G, x : A |- B = B' : univ I

- `guardIntroOf A B M`

      G |- M : A -g> B
      >>
      G |- A : type
      G, x : A |- M : B

- `guardIntroEq A B M N`

      G |- M = N : (A -g> B)
      >>
      G |- A : type
      G, x : A |- M = N : B

- `guardIntro A B`

      G |- A -g> B ext [() / x]M
      >>
      G |- A : type
      G, x (hidden) : A |- B ext M

- `guardElimOf A B M`

      G |- M : B
      >>
      G |- M : A -g> B
      G |- A

- `guardElimEq A B M N`

      G |- M = N : B
      >>
      G |- M = N : (A -g> B)
      G |- A

- `guardElim A B`

      G |- B ext M
      >>
      G |- A -g> B ext M
      G |- A

- `guardSatEq A B`

      G |- B = (A -g> B) : type
      >>
      G |- B : type
      G |- A

- `guardSub A A' B B'`

      G |- (A -g> B) <: (A' -g> B')
      >>
      G |- A' -> A
      G |- A : type
      G, x : A' |- B <: B'
      G, x : A |- B : type

- `guardSubIntro A B C`

      G |- C <: (A -g> B)
      >>
      G |- A : type
      G, x : A |- C <: B
      G |- C : type


### Strong sums

- `existsForm A B`

      G |- (exists (x : A) . B) : type
      >>
      G |- A : type
      G, x : A |- B : type

- `existsEq A A' B B'`

      G |- (exists (x : A) . B) = (exists (x : A') . B') : type
      >>
      G |- A = A' : type
      G, x : A |- B = B' : type

- `existsFormUniv A B I`

      G |- (exists (x : A) . B) : univ I
      >>
      G |- A : univ I
      G, x : A |- B : univ I

- `existsEqUniv A A' B B' I`

      G |- (exists (x : A) . B) = (exists (x : A') . B') : univ I
      >>
      G |- A = A' : univ I
      G, x : A |- B = B' : univ I

- `existsSub A A' B B'`

      G |- (exists (x : A) . B) <: (exists (x : A') . B')
      >>
      G |- A <: A'
      G, x : A |- B <: B'
      G, x : A' |- B' : type

- `existsIntroOf A B M N`

      G |- (M , N) : exists (x : A) . B
      >>
      G, x : A |- B : type
      G |- M : A
      G |- N : [M / x]B

- `existsIntroEq A B M M' N N'`

      G |- (M , N) = (M' , N') : (exists (x : A) . B)
      >>
      G, x : A |- B : type
      G |- M = M' : A
      G |- N = N' : [M / x]B

- `existsIntro A B M`

      G |- exists (x : A) . B ext (M , N)
      >>
      G, x : A |- B : type
      G |- M : A
      G |- [M / x]B ext N

- `existsElim1Of A B M`

      G |- M #1 : A
      >>
      G |- M : exists (x : A) . B

- `existsElim1Eq A B M N`

      G |- M #1 = N #1 : A
      >>
      G |- M = N : (exists (x : A) . B)

- `existsElim1 A B`

      G |- A ext M #1
      >>
      G |- exists (x : A) . B ext M

- `existsElim2Of A B M`

      G |- M #2 : [M #1 / x]B
      >>
      G |- M : exists (x : A) . B

- `existsElim2Eq A B M N`

      G |- M #2 = N #2 : [M #1 / x]B
      >>
      G |- M = N : (exists (x : A) . B)

- `existsEta A B M`

      G |- M = (M #1 , M #2) : (exists (x : A) . B)
      >>
      G |- M : exists (x : A) . B

- `existsExt A B M N`

      G |- M = N : (exists (x : A) . B)
      >>
      G |- M : exists (x : A) . B
      G |- N : exists (x : A) . B
      G |- M #1 = N #1 : A
      G |- M #2 = N #2 : [M #1 / x]B

- `existsLeft n A B C`

      G1, x : (exists (y : A) . B), G2 |- C ext [x #1, x #2 / y, z]M
      >>
      G1, y : A, z : B, [(y , z) / x]G2 |- [(y , z) / x]C ext M

- `existsFormInv1 A B`

      G |- A : type
      >>
      G |- (exists (x : A) . B) : type

- `existsFormInv2 A B M`

      G |- [M / x]B : type
      >>
      G |- (exists (x : A) . B) : type
      G |- M : A

- `existsFormInv2Eq A B M N`

      G |- [M / x]B = [N / x]B : type
      >>
      G |- (exists (x : A) . B) : type
      G |- M = N : A


### Products

- `prodKind I K L`

      G |- K & L : kind I
      >>
      G |- K : kind I
      G |- L : kind I

- `prodKindEq I K K' L L'`

      G |- (K & L) = (K' & L') : kind I
      >>
      G |- K = K' : kind I
      G |- L = L' : kind I

- `prodForm A B`

      G |- A & B : type
      >>
      G |- A : type
      G |- B : type

- `prodEq A A' B B'`

      G |- (A & B) = (A' & B') : type
      >>
      G |- A = A' : type
      G |- B = B' : type

- `prodFormUniv A B I`

      G |- A & B : univ I
      >>
      G |- A : univ I
      G |- B : univ I

- `prodEqUniv A A' B B' I`

      G |- (A & B) = (A' & B') : univ I
      >>
      G |- A = A' : univ I
      G |- B = B' : univ I

- `prodExistsEq A A' B B'`

      G |- (A & B) = (exists (x : A') . B') : type
      >>
      G |- A = A' : type
      G |- B = B' : type

- `prodExistsEqUniv A A' B B' I`

      G |- (A & B) = (exists (x : A') . B') : univ I
      >>
      G |- A = A' : univ I
      G |- B = B' : univ I

- `prodSub A A' B B'`

      G |- (A & B) <: (A' & B')
      >>
      G |- A <: A'
      G |- B <: B'

- `prodExistsSub A A' B B'`

      G |- (A & B) <: (exists (x : A') . B')
      >>
      G |- A <: A'
      G, x : A |- B <: B'
      G |- B : type
      G, x : A' |- B' : type

- `existsProdSub A A' B B'`

      G |- (exists (x : A) . B) <: (A' & B')
      >>
      G |- A <: A'
      G, x : A |- B <: B'
      G |- B' : type

- `prodIntroOf A B M N`

      G |- (M , N) : A & B
      >>
      G |- M : A
      G |- N : B

- `prodIntroEq A B M M' N N'`

      G |- (M , N) = (M' , N') : (A & B)
      >>
      G |- M = M' : A
      G |- N = N' : B

- `prodIntro A B`

      G |- A & B ext (M , N)
      >>
      G |- A ext M
      G |- B ext N

- `prodElim1Of A B M`

      G |- M #1 : A
      >>
      G |- M : A & B

- `prodElim1Eq A B M N`

      G |- M #1 = N #1 : A
      >>
      G |- M = N : (A & B)

- `prodElim1 A B`

      G |- A ext M #1
      >>
      G |- A & B ext M

- `prodElim2Of A B M`

      G |- M #2 : B
      >>
      G |- M : A & B

- `prodElim2Eq A B M N`

      G |- M #2 = N #2 : B
      >>
      G |- M = N : (A & B)

- `prodElim2 A B`

      G |- B ext M #2
      >>
      G |- A & B ext M

- `prodEta A B M`

      G |- M = (M #1 , M #2) : (A & B)
      >>
      G |- M : A & B

- `prodExt A B M N`

      G |- M = N : (A & B)
      >>
      G |- M : A & B
      G |- N : A & B
      G |- M #1 = N #1 : A
      G |- M #2 = N #2 : B

- `prodLeft n A B C`

      G1, x : (A & B), G2 |- C ext [x #1, x #2 / y, z]M
      >>
      G1, y : A, z : B, [(y , z) / x]G2 |- [(y , z) / x]C ext M

- `prodFormInv1 A B`

      G |- A : type
      >>
      G |- A & B : type

- `prodFormInv2 A B`

      G |- B : type
      >>
      G |- A & B : type
      G |- A


### Semi-dependent products

- `dprodForm A B`

      G |- dprod A B : type
      >>
      G |- A : type
      G, x : A |- B : type

- `dprodEq A A' B B'`

      G |- dprod A B = dprod A' B' : type
      >>
      G |- A = A' : type
      G, x : A |- B = B' : type

- `dprodFormUniv A B I`

      G |- dprod A B : univ I
      >>
      G |- A : univ I
      G, x : A |- B : univ I

- `dprodEqUniv A A' B B' I`

      G |- dprod A B = dprod A' B' : univ I
      >>
      G |- A = A' : univ I
      G, x : A |- B = B' : univ I

- `dprodExistsEq A A' B B'`

      G |- dprod A B = (exists (x : A') . B') : type
      >>
      G |- A = A' : type
      G, x : A |- B = B' : type

- `dprodExistsEqUniv A A' B B' I`

      G |- dprod A B = (exists (x : A') . B') : univ I
      >>
      G |- A = A' : univ I
      G, x : A |- B = B' : univ I

- `prodDprodEq A A' B B'`

      G |- (A & B) = dprod A' B' : type
      >>
      G |- A = A' : type
      G |- B = B' : type

- `prodDprodEqUniv A A' B B' I`

      G |- (A & B) = dprod A' B' : univ I
      >>
      G |- A = A' : univ I
      G |- B = B' : univ I

- `dprodSub A A' B B'`

      G |- dprod A B <: dprod A' B'
      >>
      G |- A <: A'
      G, x : A |- B <: B'
      G, x : A' |- B' : type

- `dprodExistsSub A A' B B'`

      G |- dprod A B <: (exists (x : A') . B')
      >>
      G |- A <: A'
      G, x : A |- B <: B'
      G, x : A' |- B' : type

- `existsDprodSub A A' B B'`

      G |- (exists (x : A) . B) <: dprod A' B'
      >>
      G |- A <: A'
      G, x : A |- B <: B'
      G, x : A' |- B' : type

- `dprodProdSub A A' B B'`

      G |- dprod A B <: (A' & B')
      >>
      G |- A <: A'
      G, x : A |- B <: B'
      G |- B' : type

- `prodDprodSub A A' B B'`

      G |- (A & B) <: dprod A' B'
      >>
      G |- A <: A'
      G, x : A |- B <: B'
      G |- B : type
      G, x : A' |- B' : type

- `dprodIntroOf A B M N`

      G |- (M , N) : dprod A B
      >>
      G |- M : A
      G |- N : B

- `dprodIntroEq A B M M' N N'`

      G |- (M , N) = (M' , N') : dprod A B
      >>
      G |- M = M' : A
      G |- N = N' : B

- `dprodIntro A B`

      G |- dprod A B ext (M , N)
      >>
      G |- A ext M
      G |- B ext N

- `dprodElim1Of A B M`

      G |- M #1 : A
      >>
      G |- M : dprod A B

- `dprodElim1Eq A B M N`

      G |- M #1 = N #1 : A
      >>
      G |- M = N : dprod A B

- `dprodElim1 A B`

      G |- A ext M #1
      >>
      G |- dprod A B ext M

- `dprodElim2Of A B M`

      G |- M #2 : B
      >>
      G |- M : dprod A B

- `dprodElim2Eq A B M N`

      G |- M #2 = N #2 : B
      >>
      G |- M = N : dprod A B

- `dprodElim2 A B`

      G |- B ext M #2
      >>
      G |- dprod A B ext M

- `dprodEta A B M`

      G |- M = (M #1 , M #2) : dprod A B
      >>
      G |- M : dprod A B

- `dprodExt A B M N`

      G |- M = N : dprod A B
      >>
      G |- M : dprod A B
      G |- N : dprod A B
      G |- M #1 = N #1 : A
      G |- M #2 = N #2 : B

- `dprodLeft n A B C`

      G1, x : (dprod A B), G2 |- C ext [x #1, x #2 / y, z]M
      >>
      G1, y : A, z : B, [(y , z) / x]G2 |- [(y , z) / x]C ext M

- `dprodFormInv1 A B`

      G |- A : type
      >>
      G |- dprod A B : type

- `dprodFormInv2 A B M`

      G |- B : type
      >>
      G |- dprod A B : type
      G |- M : A


### Union Types

- `unionForm A B`

      G |- (union (x : A) . B) : type
      >>
      G |- A : type
      G, x : A |- B : type

- `unionEq A A' B B'`

      G |- (union (x : A) . B) = (union (x : A') . B') : type
      >>
      G |- A = A' : type
      G, x : A |- B = B' : type

- `unionFormUniv A B I`

      G |- (union (x : A) . B) : univ I
      >>
      G |- A : univ I
      G, x : A |- B : univ I

- `unionEqUniv A A' B B' I`

      G |- (union (x : A) . B) = (union (x : A') . B') : univ I
      >>
      G |- A = A' : univ I
      G, x : A |- B = B' : univ I

- `unionIntroOf A B M N`

      G |- N : union (x : A) . B
      >>
      G, x : A |- B : type
      G |- M : A
      G |- N : [M / x]B

- `unionSub A A' B B'`

      G |- (union (x : A) . B) <: (union (x : A') . B')
      >>
      G |- A <: A'
      G, x : A |- B <: B'
      G, x : A' |- B' : type

- `unionIntroEq A B M N N'`

      G |- N = N' : (union (x : A) . B)
      >>
      G, x : A |- B : type
      G |- M : A
      G |- N = N' : [M / x]B

- `unionIntro A B M`

      G |- union (x : A) . B ext N
      >>
      G, x : A |- B : type
      G |- M : A
      G |- [M / x]B ext N

- `unionElimOf A B C M P`

      G |- [M / y]P : C
      >>
      G, x : A, y : B |- P : C
      G |- M : union (x : A) . B

- `unionElimEq A B C M N P Q`

      G |- [M / y]P = [N / y]Q : C
      >>
      G, x : A, y : B |- P = Q : C
      G |- M = N : (union (x : A) . B)

- `unionElim A B C M`

      G |- C ext [(), M / x, y]P
      >>
      G, x (hidden) : A, y : B |- C ext P
      G |- M : union (x : A) . B

- `unionElimOfDep A B C M P`

      G |- [M / y]P : [M / y]C
      >>
      G, x : A, y : B |- P : C
      G |- M : union (x : A) . B

- `unionElimEqDep A B C M N P Q`

      G |- [M / y]P = [N / y]Q : [M / y]C
      >>
      G, x : A, y : B |- P = Q : C
      G |- M = N : (union (x : A) . B)

- `unionElimDep A B C M`

      G |- [M / y]C ext [(), M / x, y]P
      >>
      G, x (hidden) : A, y : B |- C ext P
      G |- M : union (x : A) . B

- `unionElimIstype A B C M`

      G |- [M / y]C : type
      >>
      G, x : A, y : B |- C : type
      G |- M : union (x : A) . B

- `unionElimEqtype A B C D M N`

      G |- [M / y]C = [N / y]D : type
      >>
      G, x : A, y : B |- C = D : type
      G |- M = N : (union (x : A) . B)


### Coguarded types

- `coguardForm A B`

      G |- A &g B : type
      >>
      G |- A : type
      G, x : A |- B : type

- `coguardEq A A' B B'`

      G |- (A &g B) = (A' &g B') : type
      >>
      G |- iff A A'
      G, x : A |- B = B' : type

- `coguardFormUniv A B I`

      G |- A &g B : univ I
      >>
      G |- A : univ I
      G, x : A |- B : univ I

- `coguardEqUniv A A' B B' I`

      G |- (A &g B) = (A' &g B') : univ I
      >>
      G |- A : univ I
      G |- A' : univ I
      G |- iff A A'
      G, x : A |- B = B' : univ I

- `coguardIntroEq A B M N`

      G |- M = N : (A &g B)
      >>
      G |- A
      G |- M = N : B

- `coguardIntroOf A B M`

      G |- M : A &g B
      >>
      G |- A
      G |- M : B

- `coguardIntroOfSquash A B M`

      G |- M : A &g B
      >>
      G |- A : type
      G |- {A}
      G |- M : B

- `coguardIntro A B`

      G |- A &g B ext M
      >>
      G |- A
      G |- B ext M

- `coguardElim1 A B`

      G |- {A}
      >>
      G |- A : type
      G |- A &g B

- `coguardElim2Eq A B M N`

      G |- M = N : B
      >>
      G |- M = N : (A &g B)

- `coguardElim2Of A B M`

      G |- M : B
      >>
      G |- M : A &g B

- `coguardElim2 A B`

      G |- B ext M
      >>
      G |- A &g B ext M

- `coguardLeft n A B C`

      G1, x : (A &g B), G2 |- C ext [() / y]M
      >>
      G1 |- A : type
      G1, x : B, y (hidden) : A, G2 |- C ext M

- `coguardSatEq A B`

      G |- B = (A &g B) : type
      >>
      G |- B : type
      G |- A

- `coguardSub A A' B B'`

      G |- (A &g B) <: (A' &g B')
      >>
      G |- A -> A'
      G |- A' : type
      G, x : A |- B <: B'
      G, x : A' |- B' : type

- `coguardSubElim A B C`

      G |- (A &g B) <: C
      >>
      G |- A : type
      G, x : A |- B <: C
      G |- C : type


### Disjoint sums

- `sumForm A B`

      G |- A % B : type
      >>
      G |- A : type
      G |- B : type

- `sumEq A A' B B'`

      G |- (A % B) = (A' % B') : type
      >>
      G |- A = A' : type
      G |- B = B' : type

- `sumFormUniv A B I`

      G |- A % B : univ I
      >>
      G |- A : univ I
      G |- B : univ I

- `sumEqUniv A A' B B' I`

      G |- (A % B) = (A' % B') : univ I
      >>
      G |- A = A' : univ I
      G |- B = B' : univ I

- `sumSub A A' B B'`

      G |- (A % B) <: (A' % B')
      >>
      G |- A <: A'
      G |- B <: B'

- `sumIntro1Of A B M`

      G |- inl M : A % B
      >>
      G |- B : type
      G |- M : A

- `sumIntro1Eq A B M N`

      G |- inl M = inl N : (A % B)
      >>
      G |- B : type
      G |- M = N : A

- `sumIntro1 A B`

      G |- A % B ext inl M
      >>
      G |- B : type
      G |- A ext M

- `sumIntro2Of A B M`

      G |- inr M : A % B
      >>
      G |- A : type
      G |- M : B

- `sumIntro2Eq A B M N`

      G |- inr M = inr N : (A % B)
      >>
      G |- A : type
      G |- M = N : B

- `sumIntro2 A B`

      G |- A % B ext inr M
      >>
      G |- A : type
      G |- B ext M

- `sumElimOf A B C M P R`

      G |- sum_case M (fn x . P) (fn x . R) : [M / y]C
      >>
      G |- M : A % B
      G, x : A |- P : [inl x / y]C
      G, x : B |- R : [inr x / y]C

- `sumElimOfNondep A B C M P R`

      G |- sum_case M (fn x . P) (fn x . R) : C
      >>
      G |- M : A % B
      G, x : A |- P : C
      G, x : B |- R : C

- `sumElimEq A B C M N P Q R S`

      G |- sum_case M (fn x . P) (fn x . R) = sum_case N (fn x . Q) (fn x . S) : [M / y]C
      >>
      G |- M = N : (A % B)
      G, x : A |- P = Q : [inl x / y]C
      G, x : B |- R = S : [inr x / y]C

- `sumElim A B C M`

      G |- [M / y]C ext sum_case M (fn x . P) (fn x . R)
      >>
      G |- M : A % B
      G, x : A |- [inl x / y]C ext P
      G, x : B |- [inr x / y]C ext R

- `sumElimNondep A B C`

      G |- C ext sum_case M (fn x . P) (fn x . R)
      >>
      G |- A % B ext M
      G, x : A |- C ext P
      G, x : B |- C ext R

- `sumElimIstype A B C E M`

      G |- sum_case M (fn x . C) (fn x . E) : type
      >>
      G |- M : A % B
      G, x : A |- C : type
      G, x : B |- E : type

- `sumElimEqtype A B C D E F M N`

      G |- sum_case M (fn x . C) (fn x . E) = sum_case N (fn x . D) (fn x . F) : type
      >>
      G |- M = N : (A % B)
      G, x : A |- C = D : type
      G, x : B |- E = F : type

- `sumLeft n A B C`

      G1, x : (A % B), G2 |- C ext sum_case x (fn y . M) (fn y . N)
      >>
      G1, y : A, [inl y / x]G2 |- [inl y / x]C ext M
      G1, y : B, [inr y / x]G2 |- [inl r / x]C ext N

- `sumContradiction A B C M N`

      G |- C
      >>
      G |- inl M = inr N : (A % B)

- `sumInjection1 A B M N`

      G |- M = N : A
      >>
      G |- inl M = inl N : (A % B)

- `sumInjection2 A B M N`

      G |- M = N : B
      >>
      G |- inr M = inr N : (A % B)

- `sum_caseType`

      G |- sum_case : intersect (i : level) . intersect (a : univ i) . intersect (b : univ i) . intersect (c : univ i) . a % b -> (a -> c) -> (b -> c) -> c

- `sumFormInv1 A B`

      G |- A : type
      >>
      G |- A % B : type

- `sumFormInv2 A B`

      G |- B : type
      >>
      G |- A % B : type


### Future modality

- `futureKind I K`

      G |- future K : kind I
      >>
      G |- I : level
      promote(G) |- K : kind I

- `futureKindEq I K L`

      G |- future K = future L : kind I
      >>
      G |- I : level
      promote(G) |- K = L : kind I

- `futureForm A`

      G |- future A : type
      >>
      promote(G) |- A : type

- `futureEq A B`

      G |- future A = future B : type
      >>
      promote(G) |- A = B : type

- `futureFormUniv A I`

      G |- future A : univ I
      >>
      G |- I : level
      promote(G) |- A : univ I

- `futureEqUniv A B I`

      G |- future A = future B : univ I
      >>
      G |- I : level
      promote(G) |- A = B : univ I

- `futureSub A B`

      G |- future A <: future B
      >>
      promote(G) |- A <: B

- `futureIntroOf A M`

      G |- next M : future A
      >>
      promote(G) |- M : A

- `futureIntroEq A M N`

      G |- next M = next N : future A
      >>
      promote(G) |- M = N : A

- `futureIntro A`

      G |- future A ext next M
      >>
      promote(G) |- A ext M

- `futureElimOf A B M P`

      G |- [M #prev / x]P : [M #prev / x]B
      >>
      promote(G) |- A : type
      G |- M : future A
      G, x (later) : A |- P : B

- `futureElimOfLetnext A B M P`

      G |- letnext M (fn x . P) : [M #prev / x]B
      >>
      promote(G) |- A : type
      G |- M : future A
      G, x (later) : A |- P : B

- `futureElimOfLetnextNondep A B M P`

      G |- letnext M (fn x . P) : B
      >>
      promote(G) |- A : type
      G |- M : future A
      G, x (later) : A |- P : B

- `futureElimEq A B M N P Q`

      G |- [M #prev / x]P = [N #prev / x]Q : [M #prev / x]B
      >>
      promote(G) |- A : type
      G |- M = N : future A
      G, x (later) : A |- P = Q : B

- `futureElim A B M`

      G |- [M #prev / x]B ext [M #prev / x]P
      >>
      promote(G) |- A : type
      G |- M : future A
      G, x (later) : A |- B ext P

- `futureElimIstype A B M`

      G |- [M #prev / x]B : type
      >>
      promote(G) |- A : type
      G |- M : future A
      G, x (later) : A |- B : type

- `futureElimIstypeLetnext A B M`

      G |- letnext M (fn x . B) : type
      >>
      promote(G) |- A : type
      G |- M : future A
      G, x (later) : A |- B : type

- `futureElimEqtype A B C M N`

      G |- [M #prev / x]B = [N #prev / x]C : type
      >>
      promote(G) |- A : type
      G |- M = N : future A
      G, x (later) : A |- B = C : type

- `futureEta A M`

      G |- M = next (M #prev) : future A
      >>
      G |- M : future A

- `futureExt A M N`

      G |- M = N : future A
      >>
      G |- M : future A
      G |- N : future A
      promote(G) |- M #prev = N #prev : A

- `futureLeft n A B`

      G1, x : (future A), G2 |- B ext [x #prev / y]M
      >>
      promote(G1) |- A : type
      G1, y (later) : A, [next y / x]G2 |- [next y / x]B ext M

- `futureLeftHidden n A B`

      G1, x (hidden) : (future A), G2 |- B ext [() / y]M
      >>
      promote(G1) |- A : type
      G1, y (later hidden) : A, [next y / x]G2 |- [next y / x]B ext M

- `futureInjection A M N`

      G |- future (M = N : A) ext next ()
      >>
      promote(G) |- A : type
      G |- next M = next N : future A

- `squashFutureSwap A`

      G |- {future A}
      >>
      promote(G) |- A : type
      G |- future {A}

- `isquashFutureSwap A`

      G |- isquash (future A)
      >>
      promote(G) |- A : type
      G |- future (isquash A)

- `futureSquashSwap A`

      G |- future {A} ext next ()
      >>
      promote(G) |- A : type
      G |- {future A}

- `futureIsquashSwap A`

      G |- future (isquash A) ext next ()
      >>
      promote(G) |- A : type
      G |- isquash (future A)


### Future functions

- `forallfutForm A B`

      G |- forallfut A (fn x . B) : type
      >>
      promote(G) |- A : type
      G, x (later) : A |- B : type

- `forallfutEq A A' B B'`

      G |- forallfut A (fn x . B) = forallfut A' (fn x . B') : type
      >>
      promote(G) |- A = A' : type
      G, x (later) : A |- B = B' : type

- `forallfutFormUniv A B I`

      G |- forallfut A (fn x . B) : univ I
      >>
      G |- I : level
      promote(G) |- A : univ I
      G, x (later) : A |- B : univ I

- `forallfutEqUniv A A' B B' I`

      G |- forallfut A (fn x . B) = forallfut A' (fn x . B') : univ I
      >>
      G |- I : level
      promote(G) |- A = A' : univ I
      G, x (later) : A |- B = B' : univ I

- `forallfutSub A A' B B'`

      G |- forallfut A (fn x . B) <: forallfut A' (fn x . B')
      >>
      promote(G) |- A' <: A
      G, x (later) : A' |- B <: B'
      G, x (later) : A |- B : type

- `forallfutForallVoidSub A B B'`

      G |- forallfut A (fn x . B) <: (forall (x : void) . B')
      >>
      promote(G) |- A : type
      G, x (later) : A |- B : type

- `forallfutIntroOf A B M`

      G |- (fn x . M) : forallfut A (fn x . B)
      >>
      promote(G) |- A : type
      G, x (later) : A |- M : B

- `forallfutIntroEq A B M N`

      G |- (fn x . M) = (fn x . N) : forallfut A (fn x . B)
      >>
      promote(G) |- A : type
      G, x (later) : A |- M = N : B

- `forallfutIntro A B`

      G |- forallfut A (fn x . B) ext fn x . M
      >>
      promote(G) |- A : type
      G, x (later) : A |- B ext M

- `forallfutElimOf A B M P`

      G |- M P : [P / x]B
      >>
      G |- M : forallfut A (fn x . B)
      promote(G) |- P : A

- `forallfutElimEq A B M N P Q`

      G |- M P = N Q : [P / x]B
      >>
      G |- M = N : forallfut A (fn x . B)
      promote(G) |- P = Q : A

- `forallfutElim A B P`

      G |- [P / x]B ext M P
      >>
      G |- forallfut A (fn x . B) ext M
      promote(G) |- P : A

- `forallfutExt A B M N`

      G |- M = N : forallfut A (fn x . B)
      >>
      promote(G) |- A : type
      G |- M : forallfut A (fn x . B)
      G |- N : forallfut A (fn x . B)
      G, x (later) : A |- M x = N x : B

- `forallfutExt' A A' A'' B B' B'' M N`

      G |- M = N : forallfut A (fn x . B)
      >>
      promote(G) |- A : type
      G |- M : forall (x : A') . B'
      G |- N : forall (x : A'') . B''
      G, x (later) : A |- M x = N x : B

- `forallfutOfExt A A' B B' M`

      G |- M : forallfut A (fn x . B)
      >>
      promote(G) |- A : type
      G |- M : forall (x : A') . B'
      G, x (later) : A |- M x : B


### Future intersect

- `intersectfutForm A B`

      G |- intersectfut A (fn x . B) : type
      >>
      promote(G) |- A : type
      G, x (later) : A |- B : type

- `intersectfutEq A A' B B'`

      G |- intersectfut A (fn x . B) = intersectfut A' (fn x . B') : type
      >>
      promote(G) |- A = A' : type
      G, x (later) : A |- B = B' : type

- `intersectfutFormUniv A B I`

      G |- intersectfut A (fn x . B) : univ I
      >>
      G |- I : level
      promote(G) |- A : univ I
      G, x (later) : A |- B : univ I

- `intersectfutEqUniv A A' B B' I`

      G |- intersectfut A (fn x . B) = intersectfut A' (fn x . B') : univ I
      >>
      G |- I : level
      promote(G) |- A = A' : univ I
      G, x (later) : A |- B = B' : univ I

- `intersectfutSub A A' B B'`

      G |- intersectfut A (fn x . B) <: intersectfut A' (fn x . B')
      >>
      promote(G) |- A' <: A
      G, x (later) : A' |- B <: B'
      G, x (later) : A |- B : type

- `intersectfutIntroOf A B M`

      G |- M : intersectfut A (fn x . B)
      >>
      promote(G) |- A : type
      G, x (later) : A |- M : B

- `intersectfutIntroEq A B M N`

      G |- M = N : intersectfut A (fn x . B)
      >>
      promote(G) |- A : type
      G, x (later) : A |- M = N : B

- `intersectfutIntro A B`

      G |- intersectfut A (fn x . B) ext [() / x]M
      >>
      promote(G) |- A : type
      G, x (later hidden) : A |- B ext M

- `intersectfutElimOf A B M P`

      G |- M : [P / x]B
      >>
      G |- M : intersectfut A (fn x . B)
      promote(G) |- P : A

- `intersectfutElimEq A B M N P`

      G |- M = N : [P / x]B
      >>
      G |- M = N : intersectfut A (fn x . B)
      promote(G) |- P : A

- `intersectfutElim A B P`

      G |- [P / x]B ext M
      >>
      G |- intersectfut A (fn x . B) ext M
      promote(G) |- P : A


### Future parametric

- `parametricfutForm A B`

      G |- parametricfut A (fn x . B) : type
      >>
      promote(G) |- A : type
      G, x (later) : A |- B : type

- `parametricfutEq A A' B B'`

      G |- parametricfut A (fn x . B) = parametricfut A' (fn x . B') : type
      >>
      promote(G) |- A = A' : type
      G, x (later) : A |- B = B' : type

- `parametricfutFormUniv A B I`

      G |- parametricfut A (fn x . B) : univ I
      >>
      G |- I : level
      promote(G) |- A : univ I
      G, x (later) : A |- B : univ I

- `parametricfutEqUniv A A' B B' I`

      G |- parametricfut A (fn x . B) = parametricfut A' (fn x . B') : univ I
      >>
      G |- I : level
      promote(G) |- A = A' : univ I
      G, x (later) : A |- B = B' : univ I

- `parametricfutSub A A' B B'`

      G |- parametricfut A (fn x . B) <: parametricfut A' (fn x . B')
      >>
      promote(G) |- A' <: A
      G, x (later) : A' |- B <: B'
      G, x (later) : A |- B : type

- `parametricfutIntroOf A B M`

      G |- (fn x . M) : parametricfut A (fn x . B)
      >>
      promote(G) |- A : type
      G |- irrelevant (fn x . M)
      G, x (later) : A |- M : B

- `parametricfutIntroEq A B M N`

      G |- (fn x . M) = (fn x . N) : parametricfut A (fn x . B)
      >>
      promote(G) |- A : type
      G |- irrelevant (fn x . M)
      G |- irrelevant (fn x . N)
      G, x (later) : A |- M = N : B

- `parametricfutIntro A B`

      G |- parametricfut A (fn x . B) ext fn x . M
      >>
      promote(G) |- A : type
      G, x (later hidden) : A |- B ext M

- `parametricfutElimOf A B M P`

      G |- paramapp M P : [P / x]B
      >>
      G |- M : parametricfut A (fn x . B)
      promote(G) |- P : A

- `parametricfutElimEq A B M N P Q`

      G |- paramapp M P = paramapp N Q : [P / x]B
      >>
      G |- M = N : parametricfut A (fn x . B)
      promote(G) |- P = Q : A

- `parametricfutElim A B P`

      G |- [P / x]B ext paramapp M P
      >>
      G |- parametricfut A (fn x . B) ext M
      promote(G) |- P : A

- `parametricfutElim' A B P`

      G |- [P / x]B ext paramapp M unavailable
      >>
      G |- parametricfut A (fn x . B) ext M
      promote(G) |- P : A

- `parametricfutExt A B M N`

      G |- M = N : parametricfut A (fn x . B)
      >>
      promote(G) |- A : type
      G |- M : parametricfut A (fn x . B)
      G |- N : parametricfut A (fn x . B)
      G, x (later) : A |- paramapp M x = paramapp N x : B

- `parametricfutExt' A A' A'' B B' B'' M N`

      G |- M = N : parametricfut A (fn x . B)
      >>
      promote(G) |- A : type
      G |- M : parametric A' (fn x . B')
      G |- N : parametric A'' (fn x . B'')
      G, x (later) : A |- paramapp M x = paramapp N x : B

- `parametricfutOfExt A A' B B' M`

      G |- M : parametricfut A (fn x . B)
      >>
      promote(G) |- A : type
      G |- M : parametric A' (fn x . B')
      G, x (later) : A |- paramapp M x : B


### Recursive types

- `recKind I K`

      G |- (rec x . K) : kind I
      >>
      G |- I : level
      G, x (later) : (kind I) |- K : kind I

- `recKindEq I K L`

      G |- (rec x . K) = (rec x . L) : kind I
      >>
      G |- I : level
      G, x (later) : (kind I) |- K = L : kind I

- `recForm A`

      G |- (rec x . A) : type
      >>
      G, x (later) : type |- A : type

- `recEq A B`

      G |- (rec x . A) = (rec x . B) : type
      >>
      G, x (later) : type |- A = B : type

- `recFormUniv A I`

      G |- (rec x . A) : univ I
      >>
      G |- I : level
      G, x (later) : (univ I) |- A : univ I

- `recEqUniv A B I`

      G |- (rec x . A) = (rec x . B) : univ I
      >>
      G |- I : level
      G, x (later) : (univ I) |- A = B : univ I

- `recUnroll A`

      G |- (rec x . A) = [rec x . A / x]A : type
      >>
      G, x (later) : type |- A : type

- `recUnrollUniv A I`

      G |- (rec x . A) = [rec x . A / x]A : univ I
      >>
      G |- I : level
      G, x (later) : (univ I) |- A : univ I

- `recBisimilar A B`

      G |- B = (rec x . A) : type
      >>
      G, x (later) : type |- A : type
      G |- B = [B / x]A : type


### Inductive types

- `muForm A`

      G |- (mu t . A) : type
      >>
      G, t : type |- A : type
      G |- positive (fn t . A)

- `muEq A B`

      G |- (mu t . A) = (mu t . B) : type
      >>
      G, t : type |- A = B : type
      G |- positive (fn t . A)
      G |- positive (fn t . B)

- `muFormUniv A I`

      G |- (mu t . A) : univ I
      >>
      G |- I : level
      G, t : (univ I) |- A : univ I
      G |- positive (fn t . A)

- `muEqUniv A B I`

      G |- (mu t . A) = (mu t . B) : univ I
      >>
      G |- I : level
      G, t : (univ I) |- A = B : univ I
      G |- positive (fn t . A)
      G |- positive (fn t . B)

- `muUnroll A`

      G |- eeqtp (mu t . A) [mu t . A / t]A ext (() , ())
      >>
      G, t : type |- A : type
      G |- positive (fn t . A)

- `muUnrollUniv A I`

      G |- eeqtp (mu t . A) [mu t . A / t]A ext (() , ())
      >>
      G |- I : level
      G, t : (univ I) |- A : univ I
      G |- positive (fn t . A)

- `muInd A B M`

      G |- [M / w]B ext fix (fn z . fn x . [(), () / y, t']N) M
      >>
      G, t : type |- A : type
      G |- positive (fn t . A)
      G, t' (hidden) : type, x : [t' / t]A, y : (t' <: (mu t'' . [t'' / t]A)), z : (forall (w : t') . B) |- [x / w]B ext N
      G |- M : mu t . A

- `muIndUniv A B I M`

      G |- [M / w]B ext fix (fn z . fn x . [(), () / y, t']N #1) M
      >>
      G |- I : level
      G, t : (univ I) |- A : univ I
      G |- positive (fn t . A)
      G, t' (hidden) : (univ I), x : [t' / t]A, y : (t' <: (mu t'' . [t'' / t]A)), z : (forall (w : t') . B) |- [x / w]B & ([x / w]B : univ I) ext N
      G |- M : mu t . A

- `checkPositive`

  Proves valid goals of the form:

      G |- positive (fn t . A)

- `checkNegative`

  Proves valid goals of the form:

      G |- negative (fn t . A)


### Void

- `voidForm`

      G |- void : type

- `voidEq`

      G |- void = void : type

- `voidFormUniv I`

      G |- void : univ I
      >>
      G |- I : level

- `voidEqUniv I`

      G |- void = void : univ I
      >>
      G |- I : level

- `voidElim A`

      G |- A
      >>
      G |- void

- `voidSub A`

      G |- void <: A
      >>
      G |- A : type

- `abortType`

      G |- abort : intersect (i : level) . intersect (a : univ i) . void -> a


### Unit

- `unitKind I`

      G |- unit : kind I
      >>
      G |- I : level

- `unitKindEq I`

      G |- unit = unit : kind I
      >>
      G |- I : level

- `unitForm`

      G |- unit : type

- `unitEq`

      G |- unit = unit : type

- `unitFormUniv I`

      G |- unit : univ I
      >>
      G |- I : level

- `unitEqUniv I`

      G |- unit = unit : univ I
      >>
      G |- I : level

- `unitIntroOf`

      G |- () : unit

- `unitIntro`

      G |- unit

- `unitExt M N`

      G |- M = N : unit
      >>
      G |- M : unit
      G |- N : unit

- `unitLeft n B`

      G1, x : unit, G2 |- B ext M
      >>
      G1, [() / x]G2 |- [() / x]B ext M


### Bool

- `boolForm`

      G |- bool : type

- `boolEq`

      G |- bool = bool : type

- `boolFormUniv I`

      G |- bool : univ I
      >>
      G |- I : level

- `boolEqUniv I`

      G |- bool = bool : univ I
      >>
      G |- I : level

- `boolIntro1Of`

      G |- true : bool

- `boolIntro2Of`

      G |- false : bool

- `boolElimOf A M P R`

      G |- ite M P R : [M / x]A
      >>
      G |- M : bool
      G |- P : [true / x]A
      G |- R : [false / x]A

- `boolElimOfNondep A M P R`

      G |- ite M P R : A
      >>
      G |- M : bool
      G |- P : A
      G |- R : A

- `boolElimEq A M N P Q R S`

      G |- ite M P R = ite N Q S : [M / x]A
      >>
      G |- M = N : bool
      G |- P = Q : [true / x]A
      G |- R = S : [false / x]A

- `boolElim A M`

      G |- [M / x]A ext ite M P R
      >>
      G |- M : bool
      G |- [true / x]A ext P
      G |- [false / x]A ext R

- `boolElimIstype A C M`

      G |- ite M A C : type
      >>
      G |- M : bool
      G |- A : type
      G |- C : type

- `boolElimEqtype A B C D M N`

      G |- ite M A C = ite N B D : type
      >>
      G |- M = N : bool
      G |- A = B : type
      G |- C = D : type

- `boolLeft n A`

      G1, x : bool, G2 |- A ext ite x M N
      >>
      G1, [true / x]G2 |- [true / x]A ext M
      G1, [false / x]G2 |- [false / x]A ext N

- `boolContradiction A`

      G |- A
      >>
      G |- true = false : bool

- `iteType`

      G |- ite : intersect (i : level) . intersect (a : univ i) . bool -> a -> a -> a


### Natural numbers

- `natForm`

      G |- nat : type

- `natEq`

      G |- nat = nat : type

- `natFormUniv I`

      G |- nat : univ I
      >>
      G |- I : level

- `natEqUniv I`

      G |- nat = nat : univ I
      >>
      G |- I : level

- `natElimEq A M N P Q R S`

      G |- natcase M P (fn x . R) = natcase N Q (fn x . S) : [M / y]A
      >>
      G |- M = N : nat
      G |- P = Q : [zero / y]A
      G, x : nat |- R = S : [succ x / y]A

- `natElimEqtype A B C D M N`

      G |- natcase M A (fn x . C) = natcase N B (fn x . D) : type
      >>
      G |- M = N : nat
      G |- A = B : type
      G, x : nat |- C = D : type

- `natUnroll`

      G |- eeqtp nat (unit % nat) ext (() , ())

- `natContradiction A M`

      G |- A
      >>
      G |- zero = succ M : nat

- `natInjection M N`

      G |- M = N : nat
      >>
      G |- succ M = succ N : nat

- `zeroType`

      G |- zero : nat

- `succType`

      G |- succ : nat -> nat


### Universes

- `univKind I J`

      G |- univ J : kind I
      >>
      G |- J = I : level

- `univKindEq I J K`

      G |- univ J = univ K : kind I
      >>
      G |- J = K : level
      G |- J = I : level

- `univForm I`

      G |- univ I : type
      >>
      G |- I : level

- `univEq I J`

      G |- univ I = univ J : type
      >>
      G |- I = J : level

- `univFormUniv I J`

      G |- univ J : univ I
      >>
      G |- lsucc J <l= I

- `univFormUnivSucc I`

      G |- univ I : univ (lsucc I)
      >>
      G |- I : level

- `univEqUniv I J K`

      G |- univ J = univ K : univ I
      >>
      G |- J = K : level
      G |- lsucc J <l= I

- `univCumulativeOf A I J`

      G |- A : univ J
      >>
      G |- A : univ I
      G |- I <l= J

- `univCumulativeEq A B I J`

      G |- A = B : univ J
      >>
      G |- A = B : univ I
      G |- I <l= J

- `univCumulativeSuccOf A I`

      G |- A : univ (lsucc I)
      >>
      G |- A : univ I

- `univSub I J`

      G |- univ I <: univ J
      >>
      G |- I <l= J

- `univForgetOf A I`

      G |- A : type
      >>
      G |- A : univ I

- `univForgetEq A B I`

      G |- A = B : type
      >>
      G |- A = B : univ I

- `univIntroEqtype A B I`

      G |- A = B : univ I
      >>
      G |- A = B : type
      G |- A : univ I
      G |- B : univ I

- `univFormInv I`

      G |- I : level
      >>
      G |- univ I : type


### Kinds

- `kindForm I`

      G |- kind I : type
      >>
      G |- I : level

- `kindEq I J`

      G |- kind I = kind J : type
      >>
      G |- I = J : level

- `kindFormUniv I K`

      G |- kind I : univ K
      >>
      G |- lsucc (lsucc I) <l= K

- `kindEqUniv I J K`

      G |- kind I = kind J : univ K
      >>
      G |- I = J : level
      G |- lsucc (lsucc I) <l= K

- `kindForgetOf A I`

      G |- A : univ (lsucc I)
      >>
      G |- A : kind I

- `kindForgetEq A B I`

      G |- A = B : univ (lsucc I)
      >>
      G |- A = B : kind I

- `kindUnivSub I J`

      G |- kind I <: univ J
      >>
      G |- lsucc I <l= J


### Levels

- `levelForm`

      G |- level : type

- `levelEq`

      G |- level = level : type

- `levelFormUniv I`

      G |- level : univ I
      >>
      G |- I : level

- `levelEqUniv I`

      G |- level = level : univ I
      >>
      G |- I : level

- `lleqForm I J`

      G |- I <l= J : type
      >>
      G |- I : level
      G |- J : level

- `lleqEq I I' J J'`

      G |- (I <l= J) = (I' <l= J') : type
      >>
      G |- I = I' : level
      G |- J = J' : level

- `lleqFormUniv I J K`

      G |- I <l= J : univ K
      >>
      G |- I : level
      G |- J : level
      G |- K : level

- `lleqEqUniv I I' J J' K`

      G |- (I <l= J) = (I' <l= J') : univ K
      >>
      G |- I = I' : level
      G |- J = J' : level
      G |- K : level

- `lzeroLevel`

      G |- lzero : level

- `lsuccLevel M`

      G |- lsucc M : level
      >>
      G |- M : level

- `lsuccEq M N`

      G |- lsucc M = lsucc N : level
      >>
      G |- M = N : level

- `lmaxLevel M N`

      G |- lmax M N : level
      >>
      G |- M : level
      G |- N : level

- `lmaxEq M M' N N'`

      G |- lmax M N = lmax M' N' : level
      >>
      G |- M = M' : level
      G |- N = N' : level

- `lleqRefl M`

      G |- M <l= M
      >>
      G |- M : level

- `lleqTrans M N P`

      G |- M <l= P
      >>
      G |- M <l= N
      G |- N <l= P

- `lleqZero M`

      G |- lzero <l= M
      >>
      G |- M : level

- `lleqSucc M N`

      G |- lsucc M <l= lsucc N
      >>
      G |- M <l= N

- `lleqIncrease M N`

      G |- M <l= lsucc N
      >>
      G |- M <l= N

- `lleqMaxL M N P`

      G |- lmax M N <l= P
      >>
      G |- M <l= P
      G |- N <l= P

- `lleqMaxR1 M N P`

      G |- M <l= lmax N P
      >>
      G |- M <l= N
      G |- P : level

- `lleqMaxR2 M N P`

      G |- M <l= lmax N P
      >>
      G |- M <l= P
      G |- N : level

- `lleqResp M M' N N'`

      G |- M <l= N
      >>
      G |- M' = M : level
      G |- N' = N : level
      G |- M' <l= N'

- `lsuccMaxDistTrans M N P`

      G |- M = lsucc (lmax N P) : level
      >>
      G |- M = lmax (lsucc N) (lsucc P) : level

- `lzeroType`

      G |- lzero : level

- `lsuccType`

      G |- lsucc : level -> level

- `lmaxType`

      G |- lmax : level -> level -> level


### Equality

- `eqForm A M P`

      G |- M = P : A : type
      >>
      G |- M : A
      G |- P : A

- `eqEq A B M N P Q`

      G |- (M = P : A) = (N = Q : B) : type
      >>
      G |- A = B : type
      G |- M = N : A
      G |- P = Q : A

- `eqFormUniv A I M P`

      G |- M = P : A : univ I
      >>
      G |- A : univ I
      G |- M : A
      G |- P : A

- `eqEqUniv A B I M N P Q`

      G |- (M = P : A) = (N = Q : B) : univ I
      >>
      G |- A = B : univ I
      G |- M = N : A
      G |- P = Q : A

- `eqIntro A M N`

      G |- () : M = N : A
      >>
      G |- M = N : A

- `eqElim A M N P`

      G |- M = N : A
      >>
      G |- P : M = N : A

- `eqTrivialize A M N`

      G |- M = N : A
      >>
      G |- M = N : A

- `eqExt A M N P Q`

      G |- P = Q : (M = N : A)
      >>
      G |- P : M = N : A
      G |- Q : M = N : A

- `eqLeft n A B P Q`

      G1, x : (P = Q : A), G2 |- B ext M
      >>
      G1, [() / x]G2 |- [() / x]B ext M

- `eqRefl A M`

      G |- M = M : A
      >>
      G |- M : A

- `eqSymm A M N`

      G |- M = N : A
      >>
      G |- N = M : A

- `eqTrans A M N P`

      G |- M = P : A
      >>
      G |- M = N : A
      G |- N = P : A

- `eqFormInv1 A M N`

      G |- A : type
      >>
      G |- M = N : A : type

- `eqFormInv2 A M N`

      G |- M : A
      >>
      G |- M = N : A : type

- `eqFormInv3 A M N`

      G |- N : A
      >>
      G |- M = N : A : type


### Typing

- `ofForm A M`

      G |- (M : A) : type
      >>
      G |- M : A

- `ofEq A B M N`

      G |- (M : A) = (N : B) : type
      >>
      G |- A = B : type
      G |- M = N : A

- `ofFormUniv A I M`

      G |- (M : A) : univ I
      >>
      G |- A : univ I
      G |- M : A

- `ofEqUniv A B I M N`

      G |- (M : A) = (N : B) : univ I
      >>
      G |- A = B : univ I
      G |- M = N : A

- `ofIntro A M`

      G |- () : M : A
      >>
      G |- M : A

- `ofElim A M P`

      G |- M : A
      >>
      G |- P : M : A

- `ofTrivialize A M`

      G |- M : A
      >>
      G |- M : A

- `ofExt A M P Q`

      G |- P = Q : (M : A)
      >>
      G |- P : M : A
      G |- Q : M : A

- `ofLeft n A B P`

      G1, x : (P : A), G2 |- B ext M
      >>
      G1, [() / x]G2 |- [() / x]B ext M

- `ofEquand1 A M N`

      G |- M : A
      >>
      G |- M = N : A

- `ofEquand2 A M N`

      G |- N : A
      >>
      G |- M = N : A


### Type equality

- `eqtpForm A B`

      G |- A = B : type : type
      >>
      G |- A : type
      G |- B : type

- `eqtpEq A B C D`

      G |- (A = C : type) = (B = D : type) : type
      >>
      G |- A = B : type
      G |- C = D : type

- `eqtpFormUniv A B I`

      G |- A = B : type : univ I
      >>
      G |- A : univ I
      G |- B : univ I

- `eqtpEqUniv A B C D I`

      G |- (A = C : type) = (B = D : type) : univ I
      >>
      G |- A = B : univ I
      G |- C = D : univ I

- `eqtpIntro A B`

      G |- () : A = B : type
      >>
      G |- A = B : type

- `eqtpElim A B P`

      G |- A = B : type
      >>
      G |- P : A = B : type

- `eqtpExt A B P Q`

      G |- P = Q : (A = B : type)
      >>
      G |- P : A = B : type
      G |- Q : A = B : type

- `eqtpLeft n A B C`

      G1, x : (A = B : type), G2 |- C ext M
      >>
      G1, [() / x]G2 |- [() / x]C ext M

- `eqtpFunct A B M N`

      G |- [M / x]B = [N / x]B : type
      >>
      G, x : A |- B : type
      G |- M = N : A

- `eqtpFunctType A B B'`

      G |- [B / x]A = [B' / x]A : type
      >>
      G, x : type |- A : type
      G |- B = B' : type

- `equivalenceOf A B M`

      G |- M : B
      >>
      G |- A = B : type
      G |- M : A

- `equivalenceEq A B M N`

      G |- M = N : B
      >>
      G |- A = B : type
      G |- M = N : A

- `equivalence A B`

      G |- B ext M
      >>
      G |- A = B : type
      G |- A ext M

- `equivalenceLeft n A B C`

      G1, x : A, G2 |- C ext M
      >>
      G1, y : (A : type) |- A = B : type
      G1, x : B, G2 |- C ext M

- `equivalenceLeftAlt n A B C`

      G1, x : A, G2 |- C ext M
      >>
      G1, x : A, G2 |- A = B : type
      G1, x : B, G2 |- C ext M

- `eqtpRefl A`

      G |- A = A : type
      >>
      G |- A : type

- `eqtpSymm A B`

      G |- A = B : type
      >>
      G |- B = A : type

- `eqtpTrans A B C`

      G |- A = C : type
      >>
      G |- A = B : type
      G |- B = C : type


### Type formation

- `istpForm A`

      G |- (A : type) : type
      >>
      G |- A : type

- `istpEq A B`

      G |- (A : type) = (B : type) : type
      >>
      G |- A = B : type

- `istpFormUniv A I`

      G |- (A : type) : univ I
      >>
      G |- A : univ I

- `istpEqUniv A B I`

      G |- (A : type) = (B : type) : univ I
      >>
      G |- A = B : univ I

- `istpIntro A`

      G |- () : A : type
      >>
      G |- A : type

- `istpElim A P`

      G |- A : type
      >>
      G |- P : A : type

- `istpExt A P Q`

      G |- P = Q : (A : type)
      >>
      G |- P : A : type
      G |- Q : A : type

- `istpLeft n A B`

      G1, x : (A : type), G2 |- B ext M
      >>
      G1, [() / x]G2 |- [() / x]B ext M

- `inhabitedForm A`

      G |- A : type
      >>
      G |- A


### Subtyping

- `subtypeForm A B`

      G |- A <: B : type
      >>
      G |- A : type
      G |- B : type

- `subtypeEq A B C D`

      G |- (A <: C) = (B <: D) : type
      >>
      G |- A = B : type
      G |- C = D : type

- `subtypeFormUniv A B I`

      G |- A <: B : univ I
      >>
      G |- A : univ I
      G |- B : univ I

- `subtypeEqUniv A B C D I`

      G |- (A <: C) = (B <: D) : univ I
      >>
      G |- A = B : univ I
      G |- C = D : univ I

- `subtypeIntro A B`

      G |- () : A <: B
      >>
      G |- A <: B

- `subtypeElim A B P`

      G |- A <: B
      >>
      G |- P : A <: B

- `subtypeExt A B P Q`

      G |- P = Q : (A <: B)
      >>
      G |- P : A <: B
      G |- Q : A <: B

- `subtypeLeft n A B C`

      G1, x : (A <: B), G2 |- C ext M
      >>
      G1, [() / x]G2 |- [() / x]C ext M

- `subtypeEstablish A B`

      G |- A <: B
      >>
      G |- A : type
      G |- B : type
      G, x : A |- x : B

- `subsumptionOf A B M`

      G |- M : B
      >>
      G |- A <: B
      G |- M : A

- `subsumptionEq A B M N`

      G |- M = N : B
      >>
      G |- A <: B
      G |- M = N : A

- `subsumption A B`

      G |- B ext M
      >>
      G |- A <: B
      G |- A ext M

- `subsumptionAlt A B`

      G |- B ext M
      >>
      G |- eeqtp B A
      G |- A ext M

- `subsumptionLeft n A B C`

      G1, x : A, G2 |- C ext M
      >>
      G1, y : (A : type) |- eeqtp A B
      G1, x : B, G2 |- C ext M

- `subsumptionLeftAlt n A B C`

      G1, x : A, G2 |- C ext M
      >>
      G1, x : A, G2 |- eeqtp A B
      G1, x : B, G2 |- C ext M

- `subsumptionLast n A B C`

      G1, x : A, G2 |- C ext M
      >>
      G1, x : A |- A <: B
      G1, x : B |- C ext M

- `tighten n A B C`

      G1, x : A, G2 |- C ext M
      >>
      G1, x : A, G2 |- B <: A
      G1, x : A, G2 |- x : B
      G1, x : B, G2 |- C ext M

- `subtypeRefl A`

      G |- A <: A
      >>
      G |- A : type

- `subtypeReflEqtype A B`

      G |- A <: B
      >>
      G |- A = B : type

- `subtypeTrans A B C`

      G |- A <: C
      >>
      G |- A <: B
      G |- B <: C

- `subtypeIstp1 A B`

      G |- A : type
      >>
      G |- A <: B

- `subtypeIstp2 A B`

      G |- B : type
      >>
      G |- A <: B


### Extensional type equality

- `eeqtpForm A B`

      G |- eeqtp A B : type
      >>
      G |- A : type
      G |- B : type

- `eeqtpEq A B C D`

      G |- eeqtp A C = eeqtp B D : type
      >>
      G |- A = B : type
      G |- C = D : type

- `eeqtpFormUniv A B I`

      G |- eeqtp A B : univ I
      >>
      G |- A : univ I
      G |- B : univ I

- `eeqtpEqUniv A B C D I`

      G |- eeqtp A C = eeqtp B D : univ I
      >>
      G |- A = B : univ I
      G |- C = D : univ I


### Subset types

- `setForm A B`

      G |- {x : A | B} : type
      >>
      G |- A : type
      G, x : A |- B : type

- `setEq A A' B B'`

      G |- {x : A | B} = {x : A' | B'} : type
      >>
      G |- A = A' : type
      G, x : A |- iff B B'

- `setFormUniv A B I`

      G |- {x : A | B} : univ I
      >>
      G |- A : univ I
      G, x : A |- B : univ I

- `setEqUniv A A' B B' I`

      G |- {x : A | B} = {x : A' | B'} : univ I
      >>
      G |- A = A' : univ I
      G, x : A |- B : univ I
      G, x : A |- B' : univ I
      G, x : A |- iff B B'

- `setWeakenOf A B M`

      G |- M : A
      >>
      G |- M : {x : A | B}

- `setWeakenEq A B M N`

      G |- M = N : A
      >>
      G |- M = N : {x : A | B}

- `setWeaken A B`

      G |- A ext M
      >>
      G |- {x : A | B} ext M

- `setIntroOf A B M`

      G |- M : {x : A | B}
      >>
      G, x : A |- B : type
      G |- M : A
      G |- [M / x]B

- `setIntroEq A B M N`

      G |- M = N : {x : A | B}
      >>
      G, x : A |- B : type
      G |- M = N : A
      G |- [M / x]B

- `setIntro A B M`

      G |- {x : A | B} ext M
      >>
      G, x : A |- B : type
      G |- M : A
      G |- [M / x]B

- `setIntroOfSquash A B M`

      G |- M : {x : A | B}
      >>
      G, x : A |- B : type
      G |- M : A
      G |- {[M / x]B}

- `setIntroEqSquash A B M N`

      G |- M = N : {x : A | B}
      >>
      G, x : A |- B : type
      G |- M = N : A
      G |- {[M / x]B}

- `squashIntroOfSquash A`

      G |- () : {A}
      >>
      G |- A : type
      G |- {A}

- `setElim A B C M`

      G |- C ext [() / y]N
      >>
      G, x : A |- B : type
      G |- M : {x : A | B}
      G, y (hidden) : [M / x]B |- C ext N

- `setLeft n A B C`

      G1, x : {x : A | B}, G2 |- C ext [() / y]M
      >>
      G1, x : A |- B : type
      G1, x : A, y (hidden) : B, G2 |- C ext M

- `setSquash A B`

      G |- {x : A | B} = {x : A | {B}} : type
      >>
      G |- {x : A | B} : type

- `setFormInv A B`

      G |- A : type
      >>
      G |- {x : A | B} : type

- `setSubElim A A' B`

      G |- {x : A | B} <: A'
      >>
      G |- A <: A'
      G, x : A |- B : type


### Intensional subset types

- `isetForm A B`

      G |- iset A (fn x . B) : type
      >>
      G |- A : type
      G, x : A |- B : type

- `isetEq A A' B B'`

      G |- iset A (fn x . B) = iset A' (fn x . B') : type
      >>
      G |- A = A' : type
      G, x : A |- B = B' : type

- `isetFormUniv A B I`

      G |- iset A (fn x . B) : univ I
      >>
      G |- A : univ I
      G, x : A |- B : univ I

- `isetEqUniv A A' B B' I`

      G |- iset A (fn x . B) = iset A' (fn x . B') : univ I
      >>
      G |- A = A' : univ I
      G, x : A |- B = B' : univ I

- `isetWeakenOf A B M`

      G |- M : A
      >>
      G |- M : iset A (fn x . B)

- `isetWeakenEq A B M N`

      G |- M = N : A
      >>
      G |- M = N : iset A (fn x . B)

- `isetWeaken A B`

      G |- A ext M
      >>
      G |- iset A (fn x . B) ext M

- `isetIntroOf A B M`

      G |- M : iset A (fn x . B)
      >>
      G, x : A |- B : type
      G |- M : A
      G |- [M / x]B

- `isetIntroEq A B M N`

      G |- M = N : iset A (fn x . B)
      >>
      G, x : A |- B : type
      G |- M = N : A
      G |- [M / x]B

- `isetIntro A B M`

      G |- iset A (fn x . B) ext M
      >>
      G, x : A |- B : type
      G |- M : A
      G |- [M / x]B

- `isetIntroOfSquash A B M`

      G |- M : iset A (fn x . B)
      >>
      G, x : A |- B : type
      G |- M : A
      G |- {[M / x]B}

- `isetIntroEqSquash A B M N`

      G |- M = N : iset A (fn x . B)
      >>
      G, x : A |- B : type
      G |- M = N : A
      G |- {[M / x]B}

- `isetElim A B C M`

      G |- C ext [() / y]N
      >>
      G |- M : iset A (fn x . B)
      G, y (hidden) : [M / x]B |- C ext N

- `isetLeft n A B C`

      G1, x : (iset A (fn x . B)), G2 |- C ext [() / y]M
      >>
      G1, x : A, y (hidden) : B, G2 |- C ext M

- `isetFormInv1 A B`

      G |- A : type
      >>
      G |- iset A (fn x . B) : type

- `isetFormInv2 A B M`

      G |- [M / x]B : type
      >>
      G |- iset A (fn x . B) : type
      G |- M : A

- `isetSubElim A A' B`

      G |- iset A (fn x . B) <: A'
      >>
      G |- A <: A'
      G, x : A |- B : type


### Squash

- `squashForm A`

      G |- {A} : type
      >>
      G |- A : type

- `squashEq A B`

      G |- {A} = {B} : type
      >>
      G |- iff A B

- `squashFormUniv A I`

      G |- {A} : univ I
      >>
      G |- A : univ I

- `squashEqUniv A B I`

      G |- {A} = {B} : univ I
      >>
      G |- A : univ I
      G |- B : univ I
      G |- iff A B

- `squashIntroOf A`

      G |- () : {A}
      >>
      G |- A

- `squashIntro A`

      G |- {A}
      >>
      G |- A

- `squashElim A C M`

      G |- C ext [() / x]N
      >>
      G |- M : {A}
      G |- A : type
      G, x (hidden) : A |- C ext N

- `squashExt A M N`

      G |- M = N : {A}
      >>
      G |- M : {A}
      G |- N : {A}
      G |- A : type

- `squashLeft n A C`

      G1, x : {A}, G2 |- C ext [() / y]M
      >>
      G1 |- A : type
      G1, y (hidden) : A, [() / x]G2 |- [() / x]C ext M

- `squashSub A B`

      G |- {A} <: {B}
      >>
      G |- B : type
      G |- A -> B


### Intensional squash

- `isquashForm A`

      G |- isquash A : type
      >>
      G |- A : type

- `isquashEq A B`

      G |- isquash A = isquash B : type
      >>
      G |- A = B : type

- `isquashFormUniv A I`

      G |- isquash A : univ I
      >>
      G |- A : univ I

- `isquashEqUniv A B I`

      G |- isquash A = isquash B : univ I
      >>
      G |- A : univ I
      G |- B : univ I
      G |- A = B : univ I

- `isquashIntroOf A`

      G |- () : isquash A
      >>
      G |- A

- `isquashIntro A`

      G |- isquash A
      >>
      G |- A

- `isquashIntroOfIsquash A`

      G |- () : isquash A
      >>
      G |- isquash A

- `isquashElim A C M`

      G |- C ext [() / x]N
      >>
      G |- M : isquash A
      G, x (hidden) : A |- C ext N

- `isquashExt A M N`

      G |- M = N : isquash A
      >>
      G |- M : isquash A
      G |- N : isquash A

- `isquashLeft n A C`

      G1, x : (isquash A), G2 |- C ext [() / y]M
      >>
      G1, y (hidden) : A, [() / x]G2 |- [() / x]C ext M

- `isquashSub A B`

      G |- isquash A <: isquash B
      >>
      G |- B : type
      G |- A -> B

- `isquashFormInv A`

      G |- A : type
      >>
      G |- isquash A : type


### Quotient types

- `quotientForm A B`

      G |- (quotient (x y : A) . B) : type
      >>
      G |- A : type
      G, x : A, y : A |- B : type
      G, x' : A, y' : A, w : [x', y' / x, y]B |- [y', x' / x, y]B
      G, x' : A, y' : A, z' : A, w : [x', y' / x, y]B, w' : [y', z' / x, y]B |- [x', z' / x, y]B

- `quotientEq A A' B B'`

      G |- (quotient (x y : A) . B) = (quotient (x y : A') . B') : type
      >>
      G |- A = A' : type
      G, x : A, y : A |- B : type
      G, x : A, y : A |- B' : type
      G, x : A, y : A, w : B |- B'
      G, x : A, y : A, w : B' |- B
      G, x' : A, y' : A, w : [x', y' / x, y]B |- [y', x' / x, y]B
      G, x' : A, y' : A, z' : A, w : [x', y' / x, y]B, w' : [y', z' / x, y]B |- [x', z' / x, y]B

- `quotientFormUniv A B I`

      G |- (quotient (x y : A) . B) : univ I
      >>
      G |- A : univ I
      G, x : A, y : A |- B : univ I
      G, x' : A, y' : A, w : [x', y' / x, y]B |- [y', x' / x, y]B
      G, x' : A, y' : A, z' : A, w : [x', y' / x, y]B, w' : [y', z' / x, y]B |- [x', z' / x, y]B

- `quotientEqUniv A A' B B' I`

      G |- (quotient (x y : A) . B) = (quotient (x y : A') . B') : univ I
      >>
      G |- A = A' : univ I
      G, x : A, y : A |- B : univ I
      G, x : A, y : A |- B' : univ I
      G, x : A, y : A, w : B |- B'
      G, x : A, y : A, w : B' |- B
      G, x' : A, y' : A, w : [x', y' / x, y]B |- [y', x' / x, y]B
      G, x' : A, y' : A, z' : A, w : [x', y' / x, y]B, w' : [y', z' / x, y]B |- [x', z' / x, y]B

- `quotientIntroOf A B M`

      G |- M : quotient (x y : A) . B
      >>
      G |- (quotient (x y : A) . B) : type
      G |- M : A
      G |- [M, M / x, y]B

- `quotientIntroEq A B M N`

      G |- M = N : (quotient (x y : A) . B)
      >>
      G |- (quotient (x y : A) . B) : type
      G |- M : A
      G |- N : A
      G |- [M, N / x, y]B

- `quotientElimOf A B C M P`

      G |- [M / z]P : [M / z]C
      >>
      G |- M : quotient (x y : A) . B
      G, x : A, y : A |- B : type
      G, z : (quotient (x y : A) . B) |- C : type
      G, x : A, y : A, w : B |- [x / z]P = [y / z]P : [x / z]C

- `quotientElimEq A B C M N P Q`

      G |- [M / z]P = [N / z]Q : [M / z]C
      >>
      G |- M = N : (quotient (x y : A) . B)
      G, x : A, y : A |- B : type
      G, z : (quotient (x y : A) . B) |- C : type
      G, x : A, y : A, w : B |- [x / z]P = [y / z]Q : [x / z]C

- `quotientElimIstype A B C M`

      G |- [M / z]C : type
      >>
      G |- M : quotient (x y : A) . B
      G, x : A, y : A |- B : type
      G, x : A, y : A, w : B |- [x / z]C = [y / z]C : type

- `quotientElimEqtype A B C D M N`

      G |- [M / z]C = [N / z]D : type
      >>
      G |- M = N : (quotient (x y : A) . B)
      G, x : A, y : A |- B : type
      G, x : A, y : A, w : B |- [x / z]C = [y / z]D : type

- `quotientDescent A B C M N`

      G |- C ext [() / z]P
      >>
      G, x : A, y : A |- B : type
      G |- C : type
      G |- M : A
      G |- N : A
      G |- M = N : (quotient (x y : A) . B)
      G, z (hidden) : [M, N / x, y]B |- C ext P

- `quotientLeft n A B C`

      G1, z : (quotient (x y : A) . B), G2 |- C ext [() / z']M
      >>
      G1, z : (quotient (x y : A) . B), G2 |- C : type
      G1, z' (hidden) : A, [z' / z]G2 |- [z' / z]C ext M

- `quotientLeftRefl n A B C`

      G1, z : (quotient (x y : A) . B), G2 |- C ext [(), () / v, w]M
      >>
      G1, x : A, y : A |- B : type
      G1, z : (quotient (x y : A) . B), G2 |- C : type
      G1, v (hidden) : A, w (hidden) : [v, v / x, y]B, [v / z]G2 |- [v / z]C ext M

- `quotientLeftIstype n A B C`

      G1, z : (quotient (x y : A) . B), G2 |- C : type
      >>
      G1, x : A, y : A |- B : type
      G1, x : A, y : A, w : B, [x / z]G2 |- [x / z]C = [y / z]C : type

- `quotientLeftEqtype n A B C D`

      G1, z : (quotient (x y : A) . B), G2 |- C = D : type
      >>
      G1, x : A, y : A |- B : type
      G1, x : A, y : A, w : B, [x / z]G2 |- [x / z]C = [y / z]D : type

- `quotientLeftOf n A B C M`

      G1, z : (quotient (x y : A) . B), G2 |- M : C
      >>
      G1, x : A, y : A |- B : type
      G1, x : A, y : A, w : B, [x / z]G2 |- [x / z]M = [y / z]M : C

- `quotientLeftEq n A B C M N`

      G1, z : (quotient (x y : A) . B), G2 |- M = N : C
      >>
      G1, x : A, y : A |- B : type
      G1, x : A, y : A, w : B, [x / z]G2 |- [x / z]M = [y / z]N : C

- `quotientLeftOfDep n A B C M`

      G1, z : (quotient (x y : A) . B), G2 |- M : C
      >>
      G1, x : A, y : A |- B : type
      G1, x : A, y : A, w : B, [x / z]G2 |- [x / z]C = [y / z]C : type
      G1, x : A, y : A, w : B, [x / z]G2 |- [x / z]M = [y / z]M : [x / z]C

- `quotientLeftEqDep n A B C M N`

      G1, z : (quotient (x y : A) . B), G2 |- M = N : C
      >>
      G1, x : A, y : A |- B : type
      G1, x : A, y : A, w : B, [x / z]G2 |- [x / z]C = [y / z]C : type
      G1, x : A, y : A, w : B, [x / z]G2 |- [x / z]M = [y / z]N : [x / z]C

- `quotientFormInv A B`

      G |- A : type
      >>
      G |- (quotient (x y : A) . B) : type


### Impredicative universals

- `iforallForm A I K`

      G |- (iforall I (x : K) . A) : type
      >>
      G |- K : kind I
      G, x : K |- A : type

- `iforallEq A B I K L`

      G |- (iforall I (x : K) . A) = (iforall I (x : L) . B) : type
      >>
      G |- K = L : kind I
      G, x : K |- A = B : type

- `iforallFormUniv A I J K`

      G |- (iforall I (x : K) . A) : univ J
      >>
      G |- K : kind I
      G |- I <l= J
      G, x : K |- A : univ J

- `iforallEqUniv A B I J K L`

      G |- (iforall I (x : K) . A) = (iforall I (x : L) . B) : univ J
      >>
      G |- K = L : kind I
      G |- I <l= J
      G, x : K |- A = B : univ J

- `iforallIntroOf A I K M`

      G |- M : iforall I (x : K) . A
      >>
      G |- K : kind I
      G, x : K |- M : A

- `iforallIntroEq A I K M N`

      G |- M = N : (iforall I (x : K) . A)
      >>
      G |- K : kind I
      G, x : K |- M = N : A

- `iforallIntro A I K`

      G |- iforall I (x : K) . A ext [() / x]M
      >>
      G |- K : kind I
      G, x (hidden) : K |- A ext M

- `iforallElimOf A I K M P`

      G |- M : [P / x]A
      >>
      G, x : K |- A : type
      G |- M : iforall I (x : K) . A
      G |- P : K

- `iforallElimEq A I K M N P`

      G |- M = N : [P / x]A
      >>
      G, x : K |- A : type
      G |- M = N : (iforall I (x : K) . A)
      G |- P : K

- `iforallElim A I K P`

      G |- [P / x]A ext M
      >>
      G, x : K |- A : type
      G |- iforall I (x : K) . A ext M
      G |- P : K


### Impredicative polymorphism

- `foralltpForm A`

      G |- (foralltp t . A) : type
      >>
      G, t : type |- A : type

- `foralltpEq A B`

      G |- (foralltp t . A) = (foralltp t . B) : type
      >>
      G, t : type |- A = B : type

- `foralltpIntroOf A M`

      G |- M : foralltp t . A
      >>
      G, t : type |- M : A

- `foralltpIntroEq A M N`

      G |- M = N : (foralltp t . A)
      >>
      G, t : type |- M = N : A

- `foralltpIntro A`

      G |- foralltp t . A ext [() / t]M
      >>
      G, t (hidden) : type |- A ext M

- `foralltpElimOf A B M`

      G |- M : [B / t]A
      >>
      G, t : type |- A : type
      G |- M : foralltp t . A
      G |- B : type

- `foralltpElimEq A B M N`

      G |- M = N : [B / t]A
      >>
      G, t : type |- A : type
      G |- M = N : (foralltp t . A)
      G |- B : type

- `foralltpElim A B`

      G |- [B / t]A ext M
      >>
      G, t : type |- A : type
      G |- foralltp t . A ext M
      G |- B : type


### Impredicative existentials

- `iexistsForm A I K`

      G |- (iexists I (x : K) . A) : type
      >>
      G |- K : kind I
      G, x : K |- A : type

- `iexistsEq A B I K L`

      G |- (iexists I (x : K) . A) = (iexists I (x : L) . B) : type
      >>
      G |- K = L : kind I
      G, x : K |- A = B : type

- `iexistsFormUniv A I J K`

      G |- (iexists I (x : K) . A) : univ J
      >>
      G |- K : kind I
      G |- I <l= J
      G, x : K |- A : univ J

- `iexistsEqUniv A B I J K L`

      G |- (iexists I (x : K) . A) = (iexists I (x : L) . B) : univ J
      >>
      G |- K = L : kind I
      G |- I <l= J
      G, x : K |- A = B : univ J

- `iexistsIntroOf A B I K M`

      G |- M : iexists I (x : K) . A
      >>
      G |- K : kind I
      G, x : K |- A : type
      G |- B : K
      G |- M : [B / x]A

- `iexistsIntroEq A B I K M N`

      G |- M = N : (iexists I (x : K) . A)
      >>
      G |- K : kind I
      G, x : K |- A : type
      G |- B : K
      G |- M = N : [B / x]A

- `iexistsIntro A B I K`

      G |- iexists I (x : K) . A ext M
      >>
      G |- K : kind I
      G, x : K |- A : type
      G |- B : K
      G |- [B / x]A ext M

- `iexistsElimOf A B I K M P`

      G |- [M / y]P : B
      >>
      G |- K : type
      G, x : K |- A : type
      G, x : K, y : A |- P : B
      G |- M : iexists I (x : K) . A

- `iexistsElimEq A B I K M N P Q`

      G |- [M / y]P = [N / y]Q : B
      >>
      G |- K : type
      G, x : K |- A : type
      G, x : K, y : A |- P = Q : B
      G |- M = N : (iexists I (x : K) . A)

- `iexistsElim A B I K M`

      G |- B ext [(), M / x, y]P
      >>
      G |- K : type
      G, x : K |- A : type
      G, x (hidden) : K, y : A |- B ext P
      G |- M : iexists I (x : K) . A

- `iexistsElimIstype A B I K M`

      G |- [M / y]B : type
      >>
      G |- K : type
      G, x : K |- A : type
      G, x : K, y : A |- B : type
      G |- M : iexists I (x : K) . A

- `iexistsElimEqtype A B C I K M N`

      G |- [M / y]B = [N / y]C : type
      >>
      G |- K : type
      G, x : K |- A : type
      G, x : K, y : A |- B = C : type
      G |- M = N : (iexists I (x : K) . A)


### Miscellaneous

- `substitution n A B M`

      G1, x : A, G2 |- B ext N
      >>
      G1, x : A, G2 |- B : type
      G1, x : A, G2 |- x = M : A
      G1, [M / x]G2 |- [M / x]B ext N

- `substitutionSimple n A B M`

      G1, x : A, G2 |- B ext N
      >>
      G1, x : A, G2 |- x = M : A
      G1, [M / x]G2 |- B ext N

- `substitutionLater n A B M`

      G1, x (later) : A, G2 |- B ext N
      >>
      G1, x (later) : A, G2 |- B : type
      promote(G1), x : A, promote(G2) |- x = M : A
      G1, [M / x]G2 |- [M / x]B ext N

- `substitutionLaterSimple n A B M`

      G1, x (later) : A, G2 |- B ext N
      >>
      promote(G1), x : A, promote(G2) |- x = M : A
      G1, [M / x]G2 |- B ext N

- `generalize A B M`

      G |- [M / x]B ext [M / x]N
      >>
      G |- M : A
      G, x : A |- B ext N

- `assert A B`

      G |- B ext let M (fn x . N)
      >>
      G |- A ext M
      G, x : A |- B ext N

- `assert' A B`

      G |- B ext [M / x]N
      >>
      G |- A ext M
      G, x : A |- B ext N

- `inhabitant A M`

      G |- A ext M
      >>
      G |- M : A

- `letForm A B M N`

      G |- let M (fn x . N) : B
      >>
      G |- M : A
      G, x : A |- N : B

- `lethForm A B M N`

      G |- leth M (fn x . N) : B
      >>
      G |- M : A
      G, x : A |- N : B

- `leteForm A B M N`

      G |- lete M (fn x . N) : B
      >>
      G |- M : A
      G, x : A |- N : B

- `accInd A B I M N R`

      G |- [M / w]B ext fix (fn g . fn x . [fn y . fn r . g y / z]P) M
      >>
      G |- A : univ I
      G |- R : A -> A -> univ I
      G, x : A, z : (forall (y : A) . R y x -> [y / w]B) |- [x / w]B ext P
      G |- M : A
      G |- N : acc A R M

- `insert n`

      G1, G2 |- C ext [() / x]M
      >>
      G1, x : unit, G2 |- C ext M

- `forallLeft M`

      G, x : (forall (y : A) . B) |- C ext [x M / y]N
      >>
      G |- M : A
      G, y : [M / x]B |- C ext N
      (where x is not free in C)

- `arrowLeft`

      G, x : (A -> B) |- C ext [x M / y/N
      >>
      G |- A ext M
      G, y : B |- C ext N
      (where x is not free in C)


### Syntactic equality 

Syntactic equality is intended for internal use only.

- `sequalForm M`

      G |- sequal M M : type

- `sequalIntroOf M`

      G |- () : sequal M M

- `sequalIntro M`

      G |- sequal M M

- `sequalTrivialize M N`

      G |- sequal M N
      >>
      G |- sequal M N

- `sequalExt M N P Q`

      G |- P = Q : sequal M N
      >>
      G |- P : sequal M N
      G |- Q : sequal M N

- `sequalLeft n C M N`

      G1, x : (sequal M N), G2 |- C ext P
      >>
      G1, [() / x]G2 |- [() / x]C ext P

- `sequalEq A M N`

      G |- M = N : A
      >>
      G |- sequal M N
      G |- M : A

- `sequalEqtp A B`

      G |- A = B : type
      >>
      G |- sequal A B
      G |- A : type

- `sequivalence A B`

      G |- B ext M
      >>
      G |- sequal A B
      G |- A ext M

- `sequivalenceLeft n A B C`

      G1, x : A, G2 |- C ext M
      >>
      G1, x : A, G2 |- sequal A B
      G1, x : B, G2 |- C ext M

- `substitutionSyntactic n A B M`

      G1, x : A, G2 |- B ext N
      >>
      G1, x : A, G2 |- sequal x M
      G1, [M / x]G2 |- [M / x]B ext N

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

      G |- sequal [M / x]P [N / x]P
      >>
      G |- sequal M N

- `sequalCompatLam M N`

      G |- sequal (fn x . M) (fn x . N)
      >>
      G, x : nonsense |- sequal M N

- `sequalCompatPath path M N P`

      G |- sequal C{N} C{P}
      >>
      G |- sequal N P

      (where M = C{M'}, and C is determined by path)

- `forallEtaSequal A B M`

      G |- sequal M (fn x . M x)
      >>
      G |- M : forall (x : A) . B

- `arrowEtaSequal A B M`

      G |- sequal M (fn x . M x)
      >>
      G |- M : A -> B

- `existsEtaSequal A B M`

      G |- sequal M (M #1 , M #2)
      >>
      G |- M : exists (x : A) . B

- `prodEtaSequal A B M`

      G |- sequal M (M #1 , M #2)
      >>
      G |- M : A & B

- `futureEtaSequal A M`

      G |- sequal M (next (M #prev))
      >>
      G |- M : future A


### Partial types

- `partialForm A`

      G |- partial A : type
      >>
      G |- A : type

- `partialEq A B`

      G |- partial A = partial B : type
      >>
      G |- A = B : type

- `partialFormUniv A I`

      G |- partial A : univ I
      >>
      G |- A : univ I

- `partialEqUniv A B I`

      G |- partial A = partial B : univ I
      >>
      G |- A = B : univ I

- `partialSub A B`

      G |- partial A <: partial B
      >>
      G |- A <: B

- `partialStrict A`

      G |- partial A <: partial (partial A)
      >>
      G |- A : type

- `partialStrictConverse A`

      G |- partial (partial A) <: partial A
      >>
      G |- A : type

- `partialIdem A`

      G |- eeqtp (partial (partial A)) (partial A) ext (() , ())
      >>
      G |- A : type

- `haltsForm A M`

      G |- halts M : type
      >>
      G |- M : partial A

- `haltsEq A M N`

      G |- halts M = halts N : type
      >>
      G |- M = N : partial A

- `haltsFormUniv A I M`

      G |- halts M : univ I
      >>
      G |- I : level
      G |- M : partial A

- `haltsEqUniv A I M N`

      G |- halts M = halts N : univ I
      >>
      G |- I : level
      G |- M = N : partial A

- `partialIntroBottomOf A`

      G |- bottom : partial A
      >>
      G |- A : type

- `bottomDiverges`

      G |- void
      >>
      G |- halts bottom

- `partialExt A M N`

      G |- M = N : partial A
      >>
      G |- A : type
      G |- iff (halts M) (halts N)
      G, x : (halts M) |- M = N : A

- `partialElimEq A M N`

      G |- M = N : A
      >>
      G |- M = N : partial A
      G |- halts M

- `partialElimOf A M`

      G |- M : A
      >>
      G |- M : partial A
      G |- halts M

- `haltsTrivialize M`

      G |- halts M
      >>
      G |- halts M

- `haltsExt M N P`

      G |- N = P : halts M
      >>
      G |- N : halts M
      G |- P : halts M

- `haltsLeft n C M`

      G1, x : (halts M), G2 |- C ext N
      >>
      G1, [() / x]G2 |- [() / x]C ext N

- `haltsValue`

      G |- halts M
      >>
      (where M is valuable)

- `fixpointInductionEq A M N`

      G |- fix M = fix N : partial A
      >>
      G |- M = N : (partial A -> partial A)
      G |- admiss A

- `fixpointInductionOf A M`

      G |- fix M : partial A
      >>
      G |- M : partial A -> partial A
      G |- admiss A

- `partialFormInv A`

      G |- A : type
      >>
      G |- partial A : type

- `seqBind A B M M' N N'`

      G |- seq M (fn x . N) = seq M' (fn x . N') : partial B
      >>
      G |- M = M' : partial A
      G, x : A |- N = N' : partial B
      G |- B : type

- `activeApp A B M N`

      G |- M N : partial B
      >>
      G |- M : partial A
      G, x : A |- x N : partial B
      G |- B : type

- `activeAppSeq A B M N`

      G |- M N = seq M (fn x . x N) : partial B
      >>
      G |- M : partial A
      G, x : A |- x N : partial B
      G |- B : type

- `appHaltsInv M N`

      G |- halts M
      >>
      G |- halts (M N)

- `activePi1 A B M`

      G |- M #1 : partial B
      >>
      G |- M : partial A
      G, x : A |- x #1 : partial B
      G |- B : type

- `activePi1Seq A B M`

      G |- M #1 = seq M (fn x . x #1) : partial B
      >>
      G |- M : partial A
      G, x : A |- x #1 : partial B
      G |- B : type

- `pi1HaltsInv M`

      G |- halts M
      >>
      G |- halts (M #1)

- `activePi2 A B M`

      G |- M #2 : partial B
      >>
      G |- M : partial A
      G, x : A |- x #2 : partial B
      G |- B : type

- `activePi2Seq A B M`

      G |- M #2 = seq M (fn x . x #2) : partial B
      >>
      G |- M : partial A
      G, x : A |- x #2 : partial B
      G |- B : type

- `pi2HaltsInv M`

      G |- halts M
      >>
      G |- halts (M #2)

- `prevHaltsInv M`

      G |- halts M
      >>
      G |- halts (M #prev)

- `activeCase A B M P R`

      G |- sum_case M (fn y . P) (fn y . R) : partial B
      >>
      G |- M : partial A
      G, x : A |- sum_case x (fn y . P) (fn y . R) : partial B
      G |- B : type

- `activeCaseSeq A B M P R`

      G |- sum_case M (fn y . P) (fn y . R) = seq M (fn x . sum_case x (fn y . P) (fn y . R)) : partial B
      >>
      G |- M : partial A
      G, x : A |- sum_case x (fn y . P) (fn y . R) : partial B
      G |- B : type

- `caseHaltsInv M P R`

      G |- halts M
      >>
      G |- halts (sum_case M (fn y . P) (fn y . R))

- `seqHaltsSequal M N`

      G |- sequal (seq M (fn x . N)) [M / x]N
      >>
      G |- halts M

- `seqHaltsInv M N`

      G |- halts M
      >>
      G |- halts (seq M N)

- `sequalUnderSeq M M' N`

      G |- sequal (seq M (fn x . N)) [M' / x]N
      >>
      G |- seq M (fn x . sequal x M')

- `totalStrict A`

      G |- A <: partial A
      >>
      G |- A : type
      G, x : A |- halts x

- `voidTotal'`

      G |- total void ext fn x . ()

- `voidStrict`

      G |- void <: partial void

- `unitTotal M`

      G |- halts M
      >>
      G |- M : unit

- `unitTotal'`

      G |- total unit ext fn x . ()

- `unitStrict`

      G |- unit <: partial unit

- `boolTotal M`

      G |- halts M
      >>
      G |- M : bool

- `boolTotal'`

      G |- total bool ext fn x . ()

- `boolStrict`

      G |- bool <: partial bool

- `forallTotal A B M`

      G |- halts M
      >>
      G |- M : forall (x : A) . B

- `forallTotal' A B`

      G |- total (forall (x : A) . B) ext fn x . ()
      >>
      G |- A : type
      G, x : A |- B : type

- `forallStrict A B`

      G |- (forall (x : A) . B) <: partial (forall (x : A) . B)
      >>
      G |- A : type
      G, x : A |- B : type

- `forallfutTotal A B M`

      G |- halts M
      >>
      G |- M : forallfut A (fn x . B)

- `forallfutTotal' A B`

      G |- total (forallfut A (fn x . B)) ext (() , fn x . ())
      >>
      promote(G) |- A : type
      G, x (later) : A |- B : type

- `forallfutStrict A B`

      G |- forallfut A (fn x . B) <: partial (forallfut A (fn x . B))
      >>
      promote(G) |- A : type
      G, x (later) : A |- B : type

- `arrowTotal A B M`

      G |- halts M
      >>
      G |- M : A -> B

- `arrowTotal' A B`

      G |- total (A -> B) ext fn x . ()
      >>
      G |- A : type
      G, x : A |- B : type

- `arrowStrict A B`

      G |- (A -> B) <: partial (A -> B)
      >>
      G |- A : type
      G |- B : type

- `intersectStrict A B`

      G |- (intersect (x : A) . B) <: partial (intersect (x : A) . B)
      >>
      G |- A
      G, x : A |- B <: partial B

- `intersectfutStrict A B`

      G |- intersectfut A (fn x . B) <: partial (intersectfut A (fn x . B))
      >>
      promote(G) |- A
      G, x (later) : A |- B <: partial B

- `parametricTotal A B M`

      G |- halts M
      >>
      G |- M : parametric A (fn x . B)

- `parametricTotal' A B`

      G |- total (parametric A (fn x . B)) ext (() , fn x . ())
      >>
      G |- A : type
      G, x : A |- B : type

- `parametricStrict A B`

      G |- parametric A (fn x . B) <: partial (parametric A (fn x . B))
      >>
      G |- A : type
      G, x : A |- B : type

- `parametricfutTotal A B M`

      G |- halts M
      >>
      G |- M : parametricfut A (fn x . B)

- `parametricfutTotal' A B`

      G |- total (parametricfut A (fn x . B)) ext (() , fn x . ())
      >>
      promote(G) |- A : type
      G, x (later) : A |- B : type

- `parametricfutStrict A B`

      G |- parametricfut A (fn x . B) <: partial (parametricfut A (fn x . B))
      >>
      promote(G) |- A : type
      G, x (later) : A |- B : type

- `existsTotal A B M`

      G |- halts M
      >>
      G |- M : exists (x : A) . B

- `existsTotal' A B`

      G |- total (exists (x : A) . B) ext fn x . ()
      >>
      G |- A : type
      G, x : A |- B : type

- `existsStrict A B`

      G |- (exists (x : A) . B) <: partial (exists (x : A) . B)
      >>
      G |- A : type
      G, x : A |- B : type

- `prodTotal A B M`

      G |- halts M
      >>
      G |- M : A & B

- `prodTotal' A B`

      G |- total (A & B) ext fn x . ()
      >>
      G |- A : type
      G |- B : type

- `prodStrict A B`

      G |- (A & B) <: partial (A & B)
      >>
      G |- A : type
      G |- B : type

- `dprodTotal A B M`

      G |- halts M
      >>
      G |- M : dprod A B

- `dprodTotal' A B`

      G |- total (dprod A B) ext (() , fn x . ())
      >>
      G |- A : type
      G |- B : type

- `dprodStrict A B`

      G |- dprod A B <: partial (dprod A B)
      >>
      G |- A : type
      G |- B : type

- `sumTotal A B M`

      G |- halts M
      >>
      G |- M : A % B

- `sumTotal' A B`

      G |- total (A % B) ext fn x . ()
      >>
      G |- A : type
      G |- B : type

- `sumStrict A B`

      G |- (A % B) <: partial (A % B)
      >>
      G |- A : type
      G |- B : type

- `futureTotal A M`

      G |- halts M
      >>
      G |- M : future A

- `futureTotal' A`

      G |- total (future A) ext fn x . ()
      >>
      promote(G) |- A : type

- `futureStrict A`

      G |- future A <: partial (future A)
      >>
      promote(G) |- A : type

- `setTotal' A B`

      G |- total {x : A | B} ext (() , fn x . ())
      >>
      G, x : A |- B : type
      G |- total A

- `setStrict A B`

      G |- {x : A | B} <: partial {x : A | B}
      >>
      G, x : A |- B : type
      G |- A <: partial A

- `isetTotal' A B`

      G |- total (iset A (fn x . B)) ext (() , fn x . ())
      >>
      G, x : A |- B : type
      G |- total A

- `isetStrict A B`

      G |- iset A (fn x . B) <: partial (iset A (fn x . B))
      >>
      G, x : A |- B : type
      G |- A <: partial A

- `quotientTotal' A B`

      G |- total (quotient (x y : A) . B) ext (() , fn x . ())
      >>
      G |- (quotient (x y : A) . B) : type
      G, x : A, y : A |- B : type
      G |- total A

- `natTotal M`

      G |- halts M
      >>
      G |- M : nat

- `natTotal'`

      G |- total nat ext fn x . ()

- `natStrict`

      G |- nat <: partial nat

- `typeHalts A`

      G |- halts A
      >>
      G |- A : type

- `reduceSeqTotal A M N`

      G |- sequal (seq M (fn x . N)) [M / x]N
      >>
      G |- M : A
      G |- total A

- `haltsTotal A M`

      G |- halts M
      >>
      G |- M : A
      G |- total A

- `uptypeForm A`

      G |- uptype A : type
      >>
      G |- A : type

- `uptypeEq A B`

      G |- uptype A = uptype B : type
      >>
      G |- A = B : type

- `uptypeFormUniv A I`

      G |- uptype A : univ I
      >>
      G |- A : univ I

- `uptypeEqUniv A B I`

      G |- uptype A = uptype B : univ I
      >>
      G |- A = B : univ I

- `uptypeTrivialize A`

      G |- uptype A
      >>
      G |- uptype A

- `uptypeExt A M N`

      G |- M = N : uptype A
      >>
      G |- M : uptype A
      G |- N : uptype A

- `uptypeLeft n A B`

      G1, x : (uptype A), G2 |- B ext M
      >>
      G1, [() / x]G2 |- [() / x]B ext M

- `uptypeEeqtp A B`

      G |- uptype B
      >>
      G |- uptype A
      G |- eeqtp A B

- `uptypeUnitary A`

      G |- uptype A
      >>
      G |- A <: unit

- `voidUptype`

      G |- uptype void

- `unitUptype`

      G |- uptype unit

- `boolUptype`

      G |- uptype bool

- `forallUptype A B`

      G |- uptype (forall (x : A) . B)
      >>
      G |- A : type
      G, x : A |- uptype B

- `forallfutUptype A B`

      G |- uptype (forallfut A (fn x . B))
      >>
      promote(G) |- A : type
      G, x (later) : A |- uptype B

- `arrowUptype A B`

      G |- uptype (A -> B)
      >>
      G |- A : type
      G |- uptype B

- `intersectUptype A B`

      G |- uptype (intersect (x : A) . B)
      >>
      G |- A : type
      G, x : A |- uptype B

- `intersectfutUptype A B`

      G |- uptype (intersectfut A (fn x . B))
      >>
      promote(G) |- A : type
      G, x (later) : A |- uptype B

- `existsUptype A B`

      G |- uptype (exists (x : A) . B)
      >>
      G |- uptype A
      G, x : A |- uptype B

- `prodUptype A B`

      G |- uptype (A & B)
      >>
      G |- uptype A
      G |- uptype B

- `dprodUptype A B`

      G |- uptype (dprod A B)
      >>
      G |- uptype A
      G, x : A |- uptype B

- `sumUptype A B`

      G |- uptype (A % B)
      >>
      G |- uptype A
      G |- uptype B

- `futureUptype A`

      G |- uptype (future A)
      >>
      promote(G) |- uptype A

- `eqUptype A M N`

      G |- uptype (M = N : A)
      >>
      G |- M : A
      G |- N : A

- `ofUptype A M`

      G |- uptype (M : A)
      >>
      G |- M : A

- `eqtpUptype A B`

      G |- uptype (A = B : type)
      >>
      G |- A : type
      G |- B : type

- `istpUptype A`

      G |- uptype (A : type)
      >>
      G |- A : type

- `subtypeUptype A B`

      G |- uptype (A <: B)
      >>
      G |- A : type
      G |- B : type

- `setUptype A B`

      G |- uptype {x : A | B}
      >>
      G |- uptype A
      G, x : A |- B : type

- `isetUptype A B`

      G |- uptype (iset A (fn x . B))
      >>
      G |- uptype A
      G, x : A |- B : type

- `muUptype A`

      G |- uptype (mu t . A)
      >>
      G, t : type |- A : type
      G, t : type, x : (uptype t) |- uptype A
      G |- positive (fn t . A)

- `muUptypeUniv A I`

      G |- uptype (mu t . A)
      >>
      G |- I : level
      G, t : (univ I) |- A : univ I
      G, t : (univ I), x : (uptype t) |- uptype A
      G |- positive (fn t . A)

- `recUptype A`

      G |- uptype (rec t . A)
      >>
      G, t (later) : type |- A : type
      G, t (later) : type, x (later) : (uptype t) |- uptype A

- `recUptypeUniv A I`

      G |- uptype (rec t . A)
      >>
      G |- I : level
      G, t (later) : (univ I) |- A : univ I
      G, t (later) : (univ I), x (later) : (uptype t) |- uptype A

- `natUptype`

      G |- uptype nat

- `uptypeFormInv A`

      G |- A : type
      >>
      G |- uptype A : type

- `admissForm A`

      G |- admiss A : type
      >>
      G |- A : type

- `admissEq A B`

      G |- admiss A = admiss B : type
      >>
      G |- A = B : type

- `admissFormUniv A I`

      G |- admiss A : univ I
      >>
      G |- A : univ I

- `admissEqUniv A B I`

      G |- admiss A = admiss B : univ I
      >>
      G |- A = B : univ I

- `admissTrivialize A`

      G |- admiss A
      >>
      G |- admiss A

- `admissExt A M N`

      G |- M = N : admiss A
      >>
      G |- M : admiss A
      G |- N : admiss A

- `admissLeft n A B`

      G1, x : (admiss A), G2 |- B ext M
      >>
      G1, [() / x]G2 |- [() / x]B ext M

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

      G |- admiss (forall (x : A) . B)
      >>
      G |- A : type
      G, x : A |- admiss B

- `forallfutAdmiss A B`

      G |- admiss (forallfut A (fn x . B))
      >>
      promote(G) |- A : type
      G, x (later) : A |- admiss B

- `arrowAdmiss A B`

      G |- admiss (A -> B)
      >>
      G |- A : type
      G |- admiss B

- `intersectAdmiss A B`

      G |- admiss (intersect (x : A) . B)
      >>
      G |- A : type
      G, x : A |- admiss B

- `intersectfutAdmiss A B`

      G |- admiss (intersectfut A (fn x . B))
      >>
      promote(G) |- A : type
      G, x (later) : A |- admiss B

- `existsAdmissUptype A B`

      G |- admiss (exists (x : A) . B)
      >>
      G |- uptype A
      G, x : A |- admiss B

- `prodAdmiss A B`

      G |- admiss (A & B)
      >>
      G |- admiss A
      G |- admiss B

- `dprodAdmissUptype A B`

      G |- admiss (dprod A B)
      >>
      G |- uptype A
      G, x : A |- admiss B

- `sumAdmiss A B`

      G |- admiss (A % B)
      >>
      G |- admiss A
      G |- admiss B

- `futureAdmiss A`

      G |- admiss (future A)
      >>
      promote(G) |- admiss A

- `eqAdmiss A M N`

      G |- admiss (M = N : A)
      >>
      G |- M : A
      G |- N : A

- `ofAdmiss A M`

      G |- admiss (M : A)
      >>
      G |- M : A

- `eqtpAdmiss A B`

      G |- admiss (A = B : type)
      >>
      G |- A : type
      G |- B : type

- `istpAdmiss A`

      G |- admiss (A : type)
      >>
      G |- A : type

- `subtypeAdmiss A B`

      G |- admiss (A <: B)
      >>
      G |- A : type
      G |- B : type

- `recAdmiss A`

      G |- admiss (rec t . A)
      >>
      G, t (later) : type |- A : type
      G, t (later) : type, x (later) : (admiss t) |- admiss A

- `recAdmissUniv A I`

      G |- admiss (rec t . A)
      >>
      G |- I : level
      G, t (later) : (univ I) |- A : univ I
      G, t (later) : (univ I), x (later) : (admiss t) |- admiss A

- `natAdmiss`

      G |- admiss nat

- `admissFormInv A`

      G |- A : type
      >>
      G |- admiss A : type

- `partialType`

      G |- partial : intersect (i : level) . univ i -> univ i

- `haltsType`

      G |- halts : intersect (i : level) . intersect (a : univ i) . partial a -> univ lzero

- `admissType`

      G |- admiss : intersect (i : level) . univ i -> univ i

- `uptypeType`

      G |- uptype : intersect (i : level) . univ i -> univ i

- `seqType`

      G |- seq : intersect (i : level) . intersect (a : univ i) . intersect (b : univ i) . partial a -> (a -> partial b) -> partial b


### Let hypotheses

- `letIntro M`

      G |- C ext let x = M in N
      >>
      G, x = M |- C ext N

- `letSubst n`

      G1, x = M, G2 |- C ext N
      >>
      G1, [M / x]G2 |- [M / x]C ext N

- `letFold n C`

      G1, x = M, G2 |- [M / y]C ext N
      >>
      G1, x = M, G2 |- [x / y]C ext N

- `letUnfold n C`

      G1, x = M, G2 |- [x / y]C ext N
      >>
      G1, x = M, G2 |- [M / y]C ext N

- `letFoldHyp (m+n+1) m H`

      G1, x = M, G2, z : [M / y]H, G3 |- C ext N
      >> 
      G1, x = M, G2, z : [x / y]H, G3 |- C ext N
      (where m = length(G3) and n = length(G2))

- `letUnfoldHyp (m+n+1) m H`

      G1, x = M, G2, z : [x / y]H, G3 |- C ext N
      >> 
      G1, x = M, G2, z : [M / y]H, G3 |- C ext N
      (where m = length(G3) and n = length(G2))


### Integers

- `integerForm`

      G |- integer : type

- `integerEq`

      G |- integer = integer : type

- `integerFormUniv I`

      G |- integer : univ I
      >>
      G |- I : level

- `integerEqUniv I`

      G |- integer = integer : univ I
      >>
      G |- I : level

- `integerIntroOf`

      G |- M : integer
      (where M is an integer literal)

- `integerIntroEq`

      G |- M = M : integer
      (where M is an integer literal)


The remaining integer rules establish the properties of Istari's
native integer operations through an isomorphism to `Integer`, which
defines the integers as a quotient over pairs of natural numbers
(`quotient (x y : nat & nat) . x #1 + y #2 = x #2 + y #1 : nat`).


- `integerToDefType`

      G |- integer_to_Integer : integer -> Integer

- `integerFromDefType`

      G |- integer_from_Integer : Integer -> integer

- `integerIsomorphism1`

      G |- (fn x . integer_from_Integer (integer_to_Integer x)) = (fn x . x) : (integer -> integer)

- `integerIsomorphism2`

      G |- (fn x . integer_to_Integer (integer_from_Integer x)) = (fn x . x) : (Integer -> Integer)

- `pluszSpec`

      G |- plusz 
            = (fn x . fn y . integer_from_Integer (Plusz (integer_to_Integer x) (integer_to_Integer y))) 
            : (integer -> integer -> integer)

- `negzSpec`

      G |- negz 
            = (fn x . integer_from_Integer (Negz (integer_to_Integer x))) 
            : (integer -> integer)

- `eqzbSpec`

      G |- eqzb 
            = (fn x . fn y . Eqzb (integer_to_Integer x) (integer_to_Integer y))
            : (integer -> integer -> bool)

- `leqzbSpec`

      G |- leqzb 
            = (fn x . fn y . Leqzb (integer_to_Integer x) (integer_to_Integer y)) 
            : (integer -> integer -> bool)

- `timeszSpec`

      G |- timesz 
            = (fn x . fn y . integer_from_Integer (Timesz (integer_to_Integer x) (integer_to_Integer y))) 
            : (integer -> integer -> integer)

- `integerTotal M`

      G |- halts M
      >>
      G |- M : integer

- `integerStrict`

      G |- integer <: partial integer

- `integerUptype`

      G |- uptype integer

- `integerAdmiss`

      G |- admiss integer

- `integerSequal M N`

      G |- sequal M N
      >>
      G |- M = N : integer


### Symbols


- `symbolForm`

      G |- symbol : type

- `symbolEq`

      G |- symbol = symbol : type

- `symbolFormUniv I`

      G |- symbol : univ I
      >>
      G |- I : level

- `symbolEqUniv I`

      G |- symbol = symbol : univ I
      >>
      G |- I : level

- `symbolIntroOf`

      G |- M : symbol
      (where M is an symbol literal)

- `symbolIntroEq`

      G |- M = M : symbol
      (where M is an symbol literal)

- `symbol_eqbType`

      G |- symbol_eqb : symbol -> symbol -> bool

- `symbol_eqbSpec1 M N`

      G |- symbol_eqb M N = true : bool
      >>
      G |- M = N : symbol

- `symbol_eqbSpec2 M N`

      G |- M = N : symbol
      >>
      G |- symbol_eqb M N = true : bool

- `symbolTotal M`

      G |- halts M
      >>
      G |- M : symbol

- `symbolStrict`

      G |- symbol <: partial symbol

- `symbolUptype`

      G |- uptype symbol

- `symbolAdmiss`

      G |- admiss symbol

- `symbolSequal M N`

      G |- sequal M N
      >>
      G |- M = N : symbol


### Rewriting

These rules are tailor-made to justify certain transformations in the
rewriter, to improve performance and robustness.  (Some of the
justifying derivations are quite large.)

- `eeqtpRefl A`

      G |- eeqtp A A ext (() , ())
      >>
      G |- A : type

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
      G |- A = B : type

- `weakenSubtypeArrow A B`

      G |- A -> B ext fn x . x
      >>
      G |- A <: B

- `weakenEeqtpIff A B`

      G |- iff A B ext (fn x . x , fn x . x)
      >>
      G |- eeqtp A B

- `compatGuardEqtp1 A B B'`

      G |- (A -g> B) = (A -g> B') : type
      >>
      G |- A : type
      G |- B = B' : type

- `compatSetEqtp0 A A' B`

      G |- {x : A | B} = {x : A' | B} : type
      >>
      G |- A = A' : type
      G, x : A |- B : type

- `forallEeq A A' B B'`

      G |- eeqtp (forall (x : A) . B) (forall (x : A') . B') ext (() , ())
      >>
      G |- eeqtp A A'
      G, x : A |- eeqtp B B'

- `existsEeq A A' B B'`

      G |- eeqtp (exists (x : A) . B) (exists (x : A') . B') ext (() , ())
      >>
      G |- eeqtp A A'
      G, x : A |- eeqtp B B'

- `arrowEeq A A' B B'`

      G |- eeqtp (A -> B) (A' -> B') ext (() , ())
      >>
      G |- eeqtp A A'
      G |- eeqtp B B'

- `prodEeq A A' B B'`

      G |- eeqtp (A & B) (A' & B') ext (() , ())
      >>
      G |- eeqtp A A'
      G |- eeqtp B B'

- `dprodEeq A A' B B'`

      G |- eeqtp (dprod A B) (dprod A' B') ext (() , ())
      >>
      G |- eeqtp A A'
      G, x : A |- eeqtp B B'

- `sumEeq A A' B B'`

      G |- eeqtp (A % B) (A' % B') ext (() , ())
      >>
      G |- eeqtp A A'
      G |- eeqtp B B'

- `futureEeq A A'`

      G |- eeqtp (future A) (future A') ext (() , ())
      >>
      promote(G) |- eeqtp A A'

- `intersectEeq A A' B B'`

      G |- eeqtp (intersect (x : A) . B) (intersect (x : A') . B') ext (() , ())
      >>
      G |- eeqtp A A'
      G, x : A |- eeqtp B B'

- `unionEeq A A' B B'`

      G |- eeqtp (union (x : A) . B) (union (x : A') . B') ext (() , ())
      >>
      G |- eeqtp A A'
      G, x : A |- eeqtp B B'

- `compatGuardEeq1 A B B'`

      G |- eeqtp (A -g> B) (A -g> B') ext (() , ())
      >>
      G |- A : type
      G |- eeqtp B B'

- `compatSetEeq0 A A' B`

      G |- eeqtp {x : A | B} {x : A' | B} ext (() , ())
      >>
      G |- eeqtp A A'
      G, x : A |- B : type

- `compatIsetEeq0 A A' B`

      G |- eeqtp (iset A (fn x . B)) (iset A' (fn x . B)) ext (() , ())
      >>
      G |- eeqtp A A'
      G, x : A |- B : type

- `compatIsetIff1 A B B'`

      G |- eeqtp (iset A (fn x . B)) (iset A (fn x . B')) ext (() , ())
      >>
      G |- A : type
      G, x : A |- iff B B'

- `compatForallSubtype0 A A' B`

      G |- (forall (x : A) . B) <: (forall (x : A') . B)
      >>
      G |- A' <: A
      G, x : A |- B : type

- `compatForallSubtype1 A B B'`

      G |- (forall (x : A) . B) <: (forall (x : A) . B')
      >>
      G |- A : type
      G, x : A |- B <: B'

- `compatExistsSubtype0 A A' B`

      G |- (exists (x : A) . B) <: (exists (x : A') . B)
      >>
      G |- A <: A'
      G, x : A' |- B : type

- `compatExistsSubtype1 A B B'`

      G |- (exists (x : A) . B) <: (exists (x : A) . B')
      >>
      G |- A : type
      G, x : A |- B <: B'

- `compatIntersectSubtype0 A A' B`

      G |- (intersect (x : A) . B) <: (intersect (x : A') . B)
      >>
      G |- A' <: A
      G, x : A |- B : type

- `compatIntersectSubtype1 A B B'`

      G |- (intersect (x : A) . B) <: (intersect (x : A) . B')
      >>
      G |- A : type
      G, x : A |- B <: B'

- `compatUnionSubtype0 A A' B`

      G |- (union (x : A) . B) <: (union (x : A') . B)
      >>
      G |- A <: A'
      G, x : A' |- B : type

- `compatUnionSubtype1 A B B'`

      G |- (union (x : A) . B) <: (union (x : A) . B')
      >>
      G |- A : type
      G, x : A |- B <: B'

- `compatGuardArrow0 A A' B`

      G |- (A -g> B) <: (A' -g> B)
      >>
      G |- A : type
      G |- B : type
      G |- A' -> A

- `compatGuardSubtype1 A B B'`

      G |- (A -g> B) <: (A -g> B')
      >>
      G |- A : type
      G |- B <: B'

- `compatSetSubtype0 A A' B`

      G |- {x : A | B} <: {x : A' | B}
      >>
      G |- A <: A'
      G, x : A' |- B : type

- `compatSetArrow1 A B B'`

      G |- {x : A | B} <: {x : A | B'}
      >>
      G |- A : type
      G, x : A |- B' : type
      G, x : A |- B -> B'

- `compatIsetSubtype0 A A' B`

      G |- iset A (fn x . B) <: iset A' (fn x . B)
      >>
      G |- A <: A'
      G, x : A' |- B : type

- `compatIsetArrow1 A B B'`

      G |- iset A (fn x . B) <: iset A (fn x . B')
      >>
      G |- A : type
      G, x : A |- B' : type
      G, x : A |- B -> B'

- `compatForallIff1 A B B'`

      G |- iff (forall (x : A) . B) (forall (x : A) . B') ext (fn f . fn x . M #1 (f x) , fn f . fn x . M #2 (f x))
      >>
      G |- A : type
      G, x : A |- iff B B' ext M

- `compatExistsIff1 A B B'`

      G |- iff (exists (x : A) . B) (exists (x : A) . B') ext (fn p . (p #1 , [p #1 / x]M #1 (p #2)) , fn p . (p #1 , [p #1 / x]M #2 (p #2)))
      >>
      G |- A : type
      G, x : A |- iff B B' ext M

- `compatArrowIff0 A A' B`

      G |- iff (A -> B) (A' -> B) ext (fn f . fn x . f (M #2 x) , fn f . fn x . f (M #1 x))
      >>
      G |- B : type
      G |- iff A A' ext M

- `compatArrowIff1 A B B'`

      G |- iff (A -> B) (A -> B') ext (fn f . fn x . M #1 (f x) , fn f . fn x . M #2 (f x))
      >>
      G |- A : type
      G |- iff B B' ext M

- `compatProdIff0 A A' B`

      G |- iff (A & B) (A' & B) ext (fn x . (M #1 (x #1) , x #2) , fn x . (M #2 (x #1) , x #2))
      >>
      G |- B : type
      G |- iff A A' ext M

- `compatProdIff1 A B B'`

      G |- iff (A & B) (A & B') ext (fn x . (x #1 , M #1 (x #2)) , fn x . (x #1 , M #2 (x #2)))
      >>
      G |- A : type
      G |- iff B B' ext M

- `compatDprodIff0 A A' B`

      G |- iff (dprod A B) (dprod A' B) ext (fn x . (M #1 (x #1) , x #2) , fn x . (M #2 (x #1) , x #2))
      >>
      G, x : A |- B : type
      G |- iff A A' ext M

- `compatDprodIff1 A B B'`

      G |- iff (dprod A B) (dprod A B') ext (fn x . (x #1 , M #1 (x #2)) , fn x . (x #1 , M #2 (x #2)))
      >>
      G |- A : type
      G |- iff B B' ext M

- `compatSumIff0 A A' B`

      G |- iff (A % B) (A' % B) ext (fn x . sum_case x (fn y . inl (M #1 y)) (fn y . inr y) , fn x . sum_case x (fn y . inl (M #2 y)) (fn y . inr y))
      >>
      G |- B : type
      G |- iff A A' ext M

- `compatSumIff1 A B B'`

      G |- iff (A % B) (A % B') ext (fn x . sum_case x (fn y . inl y) (fn y . inr (M #1 y)) , fn x . sum_case x (fn y . inl y) (fn y . inr (M #2 y)))
      >>
      G |- A : type
      G |- iff B B' ext M

- `compatFutureIff A A'`

      G |- iff (future A) (future A') ext (fn x . letnext x (fn y . next (M #1 y)) , fn x . letnext x (fn y . next (M #2 y)))
      >>
      promote(G) |- iff A A' ext M

- `compatForallArrow1 A B B'`

      G |- (forall (x : A) . B) -> forall (x : A) . B' ext fn f . fn x . M (f x)
      >>
      G |- A : type
      G, x : A |- B -> B' ext M

- `compatExistsArrow1 A B B'`

      G |- (exists (x : A) . B) -> exists (x : A) . B' ext fn p . (p #1 , [p #1 / x]M (p #2))
      >>
      G |- A : type
      G, x : A |- B' : type
      G, x : A |- B -> B' ext M

- `compatArrowArrow0 A A' B`

      G |- (A -> B) -> A' -> B ext fn f . fn x . f (M x)
      >>
      G |- A : type
      G |- B : type
      G |- A' -> A ext M

- `compatArrowArrow1 A B B'`

      G |- (A -> B) -> A -> B' ext fn f . fn x . M (f x)
      >>
      G |- A : type
      G |- B -> B' ext M

- `compatProdArrow0 A A' B`

      G |- A & B -> A' & B ext fn x . (M (x #1) , x #2)
      >>
      G |- B : type
      G |- A -> A' ext M

- `compatProdArrow1 A B B'`

      G |- A & B -> A & B' ext fn x . (x #1 , M (x #2))
      >>
      G |- A : type
      G |- B -> B' ext M

- `compatDprodArrow0 A A' B`

      G |- dprod A B -> dprod A' B ext fn x . (M (x #1) , x #2)
      >>
      G |- B : type
      G |- A -> A' ext M

- `compatDprodArrow1 A B B'`

      G |- dprod A B -> dprod A B' ext fn x . (x #1 , M (x #2))
      >>
      G |- A : type
      G |- B -> B' ext M

- `compatSumArrow0 A A' B`

      G |- A % B -> A' % B ext fn x . sum_case x (fn y . inl (M y)) (fn y . inr y)
      >>
      G |- A' : type
      G |- B : type
      G |- A -> A' ext M

- `compatSumArrow1 A B B'`

      G |- A % B -> A % B' ext fn x . sum_case x (fn y . inl y) (fn y . inr (M y))
      >>
      G |- A : type
      G |- B' : type
      G |- B -> B' ext M

- `compatFutureArrow A A'`

      G |- future A -> future A' ext fn x . letnext x (fn y . next (M y))
      >>
      promote(G) |- A -> A' ext M

- `compatForallEntails1 A B B'`

      G |- forall (x : A) . B' ext fn x . [F x / y]M
      >>
      G, x : A, y : B |- B' ext M
      G |- forall (x : A) . B ext F

- `compatArrowEntails1 A B B'`

      G |- A -> B' ext fn x . [F x / y]M
      >>
      G, y : B |- B' ext M
      G |- A -> B ext F

- `compatProdEntails0 A A' B`

      G |- A' & B ext ([P #1 / x]M , P #2)
      >>
      G, x : A |- A' ext M
      G |- A & B ext P

- `compatProdEntails1 A B B'`

      G |- A & B' ext (P #1 , [P #2 / x]M)
      >>
      G, x : B |- B' ext M
      G |- A & B ext P

- `compatDprodEntails0 A A' B`

      G |- dprod A' B ext ([P #1 / x]M , P #2)
      >>
      G, x : A |- A' ext M
      G |- dprod A B ext P

- `compatDprodEntails1 A B B'`

      G |- dprod A B' ext (P #1 , [P #2 / y]M)
      >>
      G, y : B |- B' ext M
      G |- dprod A B ext P
