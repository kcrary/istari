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
the sake of convenience or performance.  Since the rules are (nearly)
all verified, there is no robustness advantage to minimizing the set
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
[Guarded types](#guarded-types)<br>
[Strong sums](#strong-sums)<br>
[Products](#products)<br>
[Disjoint sums](#disjoint-sums)<br>
[Future modality](#future-modality)<br>
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
[Squash](#squash)<br>
[Quotient types](#quotient-types)<br>
[Impredicative universals](#impredicative-universals)<br>
[Impredicative polymorphism](#impredicative-polymorphism)<br>
[Impredicative existentials](#impredicative-existentials)<br>
[Miscellaneous](#miscellaneous)<br>
[Let hypotheses](#let-hypotheses)<br>
[Integers](#integers)<br>



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


### Guarded types

- `guardForm A B`

      G |- (A -g> B) : type
      >>
      G |- A : type
      G, x : A |- B : type

- `guardEq A A' B B'`

      G |- (A -g> B) = (A' -g> B') : type
      >>
      G |- A = A' : type
      G, x : A |- B = B' : type

- `guardFormUniv A B I`

      G |- (A -g> B) : univ I
      >>
      G |- A : univ I
      G, x : A |- B : univ I

- `guardEqUniv A A' B B' I`

      G |- (A -g> B) = (A' -g> B') : univ I
      >>
      G |- A = A' : univ I
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

      G |- (A & B) = (exists (x : A) . B) : type
      >>
      G |- A = A' : type
      G |- B = B' : type

- `prodExistsEqUniv A A' B B' I`

      G |- (A & B) = (exists (x : A) . B) : univ I
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

      G |- sumcase M (fn x . P) (fn x . R) : [M / y]C
      >>
      G |- M : A % B
      G, x : A |- P : [inl x / y]C
      G, x : B |- R : [inr x / y]C

- `sumElimOfNondep A B C M P R`

      G |- sumcase M (fn x . P) (fn x . R) : C
      >>
      G |- M : A % B
      G, x : A |- P : C
      G, x : B |- R : C

- `sumElimEq A B C M N P Q R S`

      G |- sumcase M (fn x . P) (fn x . R) = sumcase N (fn x . Q) (fn x . S) : [M / y]C
      >>
      G |- M = N : (A % B)
      G, x : A |- P = Q : [inl x / y]C
      G, x : B |- R = S : [inr x / y]C

- `sumElim A B C M`

      G |- [M / y]C ext sumcase M (fn x . P) (fn x . R)
      >>
      G |- M : A % B
      G, x : A |- [inl x / y]C ext P
      G, x : B |- [inr x / y]C ext R

- `sumElimNondep A B C`

      G |- C ext sumcase M (fn x . P) (fn x . R)
      >>
      G |- A % B ext M
      G, x : A |- C ext P
      G, x : B |- C ext R

- `sumElimIstype A B C E M`

      G |- sumcase M (fn x . C) (fn x . E) : type
      >>
      G |- M : A % B
      G, x : A |- C : type
      G, x : B |- E : type

- `sumElimEqtype A B C D E F M N`

      G |- sumcase M (fn x . C) (fn x . E) = sumcase N (fn x . D) (fn x . F) : type
      >>
      G |- M = N : (A % B)
      G, x : A |- C = D : type
      G, x : B |- E = F : type

- `sumLeft n A B C`

      G1, x : (A % B), G2 |- C ext sumcase x (fn y . M) (fn y . N)
      >>
      G1, y : A, [inl y / x]G2 |- [inl y / x]C ext M
      G1, y : B, [inr y / x]G2 |- [inl r / x]C ext N

- `sumcaseType`

      G |- sumcase : intersect (i : level) . intersect (a : univ i) . intersect (b : univ i) . intersect (c : univ i) . a % b -> (a -> c) -> (b -> c) -> c

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

      G |- A <: B
      >>
      G |- A : type
      G |- B : type
      G, x : A |- x : B

- `subtypeExt A B P Q`

      G |- P = Q : (A <: B)
      >>
      G |- P : A <: B
      G |- Q : A <: B

- `subtypeLeft n A B C`

      G1, x : (A <: B), G2 |- C ext M
      >>
      G1, [() / x]G2 |- [() / x]C ext M

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

- `subsumptionLeft n A B C`

      G1, x : A, G2 |- C ext M
      >>
      G1, y : (A : type) |- eeqtp A B
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
      G, x : A |- B : type
      G, x : A |- B' : type
      G, x : A, y : B |- B'
      G, x : A, y : B' |- B

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
      G, x : A, y : B |- B'
      G, x : A, y : B' |- B

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


### Squash

- `squashForm A`

      G |- {A} : type
      >>
      G |- A : type

- `squashEq A B`

      G |- {A} = {B} : type
      >>
      G |- A : type
      G |- B : type
      G, x : A |- B
      G, x : B |- A

- `squashFormUniv A I`

      G |- {A} : univ I
      >>
      G |- A : univ I

- `squashEqUniv A B I`

      G |- {A} = {B} : univ I
      >>
      G |- A : univ I
      G |- B : univ I
      G, x : A |- B
      G, x : B |- A

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

- `eeqtpSymm A B`

      G |- eeqtp A B ext (() , ())
      >>
      G |- eeqtp B A

- `weakenEqtpEeqtp A B`

      G |- eeqtp A B ext (() , ())
      >>
      G |- A = B : type

- `accInd A B I M N R`

      G |- [M / w]B ext fix (fn g . fn x . [fn y . fn r . g y / z]P) M
      >>
      G |- A : univ I
      G |- R : A -> A -> univ I
      G, x : A, z : (forall (y : A) . R y x -> [y / w]B) |- [x / w]B ext P
      G |- M : A
      G |- N : acc A R M


### Let hypotheses

- `letIntro n M`

      G1, G2 |- C ext [M / x]N
      >>
      G1, x = M, G2 |- C ext N

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

      G |- integer_to_def : integer -> Integer

- `integerFromDefType`

      G |- integer_from_def : Integer -> integer

- `integerIsomorphism1`

      G |- (fn x . integer_from_def (integer_to_def x)) = (fn x . x) : (integer -> integer)

- `integerIsomorphism2`

      G |- (fn x . integer_to_def (integer_from_def x)) = (fn x . x) : (Integer -> Integer)

- `pluszSpec`

      G |- plusz 
            = (fn x . fn y . integer_from_def (Plusz (integer_to_def x) (integer_to_def y))) 
            : (integer -> integer -> integer)

- `negzSpec`

      G |- negz 
            = (fn x . integer_from_def (Negz (integer_to_def x))) 
            : (integer -> integer)

- `eqzbSpec`

      G |- eqzb 
            = (fn x . fn y . Eqzb (integer_to_def x) (integer_to_def y))
            : (integer -> integer -> bool)

- `leqzbSpec`

      G |- leqzb 
            = (fn x . fn y . Leqzb (integer_to_def x) (integer_to_def y)) 
            : (integer -> integer -> bool)

- `timeszSpec`

      G |- timesz 
            = (fn x . fn y . integer_from_def (Timesz (integer_to_def x) (integer_to_def y))) 
            : (integer -> integer -> integer)

