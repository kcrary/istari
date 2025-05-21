# Term syntax

Istari employs two types for terms: `Term.term` is the internal
representation of terms, and `ETerm.eterm` is the external
representation.  We usually refer to both of them as just terms,
except when the context requires us to distinguish them.

The main difference between internal and external terms is that
internal terms represent variables using de Bruijn indices, while
external terms use explicit names.  (Istari's de Bruijn indices count
from zero.)  External terms are converted to internal ones by
supplying a data structure (called a *directory*) that maps names onto
indices.  (A few other things are done while converting external terms
to internal ones as well.)


#### The term grammar

The default grammar for terms is as follows.  Capitalized words are
nonterminals; lower case words are keywords.  (**Exception:** `U` and
`Kind` are keywords.)

Forms are listed in increasing order of precedence.  Grouped forms
have the same precedence.  A subterm at the same level of precedence
is given in brackets.  For example, `[Term] + Term` indicates that
addition is left associative, while `Term :: [Term]` indicates that
cons is right associative.

    Term ::=
      fn Bindingsn . [Term]                                          (lambda)
      forall Bindings . [Term]                                       (dependent product)  
      exists Bindings . [Term]                                       (strong dependent sum)
      iforall Bindings . [Term]                                      (impredicative universal)
      iexists Bindings . [Term]                                      (impredicative existential)
      intersect Bindings . [Term]                                    (intersection type)
      union Bindings . [Term]                                        (union type)
      parametric Bindings . [Term]                                   (parametric dependent function)
      weaksum Bindings . [Term]                                      (weak dependent sum)
      foralltp OIdents . [Term]                                      (impredicative polymorphism)
      forallfut Bindings . [Term]                                    (future dependent product)  
      intersectfut Bindings . [Term]                                 (future intersection type)  
      rec Ident . [Term]                                             (recursive type)
      mu Ident . [Term]                                              (inductive type)
      wtype ( Ident : [Term] ) . [Term]                              (W type)
      iset ( Ident : [Term] ) . [Term]                               (intensional set type)
      quotient ( Ident Ident : [Term] ) . [Term]                     (quotient type)
      Term -> [Term]                                                 (ordinary arrow)
      Term -t> [Term]                                                (tarrow kind)
      Term -k> [Term]                                                (karrow kind)
      Term -g> [Term]                                                (guard)
      let Ident = Term in [Term]                                     (let)
      let next Ident = Term in [Term]                                (scoped future elim)
      unpack (Ident, Ident) = Term in [Term]                         (unpack weak sum)
      unpackt (Ident, Ident) = Term in [Term]                        (weak sum predicate)
      seq Ident = Term in [Term]                                     (eager let for partial types)
      seqt Ident = Term in [Term]                                    (eager let for total types)
      case Term of | inl OIdent . [Term] | inr OIdent . [Term]       (sum elim)
      Term : [Term]                                                  (typing)
      Term : type                                                    (type formation)
      fnind ... inductive function ...                               (inductive function)

      if [Term] then [Term] else [Term]                              (if-then-else)

      Term <-> Term                                                  (if-and-only-if)

      Term % [Term]                                                  (sum type)

      Term & [Term]                                                  (product type)
      Term &d [Term]                                                 (semi-dependent product type)
      Term &g [Term]                                                 (coguard type)

      Term = Term : Term                                             (equality)
      Term = Term : type                                             (type equality)
      Term <: Term                                                   (subtyping)
      Term <:> Term                                                  (extensional type equivalence)
      Term != Term : Term                                            (inequality)
      Term <= Term                                                   (natural number inequality)
      Term < Term                                                    (natural number inequality)
      Term <l= Term                                                  (level inequality)
      Term <z= Term                                                  (integer inequality)
      Term <z Term                                                   (integer inequality)
      Term <q= Term                                                  (rational inequality)
      Term <q Term                                                   (rational inequality)

      Term :: [Term]                                                 (cons)

      [Term] + Term                                                  (natural number plus)
      [Term] - Term                                                  (natural number minus)
      [Term] +z Term                                                 (integer plus)
      [Term] -z Term                                                 (integer minus)
      [Term] +q Term                                                 (rational plus)
      [Term] -q Term                                                 (rational minus)

      [Term] * Term                                                  (natural number times)
      [Term] *z Term                                                 (integer times)
      [Term] *q Term                                                 (rational times)
      [Term] |q Term                                                 (rational divide)

      [Term] Term                                                    (application)
      [Term] #1                                                      (first projection)
      [Term] #2                                                      (second projection)
      [Term] #prev                                                   (unscoped future elim)
      [Term] ## Number                                               (#2 ... #2 #1)
      pi1 Term                                                       (first projection)
      pi2 Term                                                       (second projection)
      prev Term                                                      (unscoped future elim)
      next Term                                                      (future intro)
      inl Term                                                       (sum intro)
      inr Term                                                       (sum intro)
      ~z Term                                                        (integer negation)
      U Level                                                        (universe)
      Kind Level                                                     (kind)
      [Term] :> Term                                                 (type annotation)
      [Term] ap Term                                                 (visibilized application)
      [Term] Ap Term                                                 (parametric application)
      [Term] _# Number                                               (application to multiple evars)
      [Term] Ap_# Number                                             (parametric application to multiple evars)
      [Term] __# Number                                              (application to multiple holes)

      ( Term )
      ()                                                             (unit)
      ( Term , ... , Term )                                          (tuple, length at least 2)
      { Ident : Term | Term }                                        (set type)
      { Term }                                                       (squashed type)
      Longident                                                      (identifier)
      Number                                                         (natural number literal)
      _                                                              (evar)
      __                                                             (hole)
      \ ... antiquoted internal term ... \
      ` Longident
      l` LTerm                                                       (literal term)
      level` Level                                                   (level expression)
      z` Number                                                      (integer literal)
      q` Number                                                      (rational literal)

    OIdent ::=
      Ident
      _                                                              (anonymous argument)

    OIdents ::=
      OIdent ... OIdent                                              (length can be zero)

    Binding ::=
      OIdent                                                         (unannotated binding)
      (OIdents : Term)                                               (binding with type supplied)

    Bindings ::=       
      Binding ... Binding                                            (length at least 0)

    Bindingsn ::=       
      Binding ... Binding                                            (length at least 1)

    Level ::=
      Number + [Level]                                               (level plus)

      ( Level )
      Number                                                         (level literal)
      [ Level ... Level ]                                            (level max, length at least 1)
      Ident                                                          (identifier)
      \ ... antiquoted internal term ... \


Notes:

- Note that typing (`M : A`) has lower precedence than equality 
  (`M = N : A`).  Thus, `M : A -> B` asserts that `M` has the type 
  `A -> B`, while `M = N : A -> B` asserts that the equality 
  `M = N : A` implies `B`.

- Similarly, type formation (`A : type`) has lower precedence than type
  equality (`A = B : type`).  Thus `A : type -> C` is an error (since
  `type -> C` is illegal), while `A = B : type -> C` asserts that the
  equality `A = B : type` implies `C`.

- The pair form is `(Term , Term)`, not `(Term, Term)` or
  `(Term,Term)`.  (Observe the whitespace on both sides of the comma.)
  For example, because of how IML [tokenizes
  input](iml.html#tokenization), the `x,` in `(x, y)` forms a single
  token, rather than two, which will result in a syntax error.

- A tick (`` ` ``) before an identifier suppresses the insertion of
  implicit arguments.  (See below.)  It also allows the identifier to
  be any constant name, even if the name collides with a keyword.

- An [antiquoted](iml.html#antiquote) internal term should have the
  type `Term.term`.

- A hole (`__`) is a placeholder used by some tactics (*e.g.,* `so`).
  It is written as two consecutive underscores.

- One can put multiple anonymous arguments into a `Bindings` or
  `Bindingsn` by writing `_# Number`.  The multiplicity can be zero.
  (The requirement that a `Bindingsn` be nonempty can be defeated
  using a zero multiplicity.)

- One can suppress the insertion of implicit arguments throughout an
  entire term using the syntax ``explicit` Term``.  The inner term
  should be parenthesized or otherwise syntactically atomic (that is,
  it should appear in the last grouping of `Term` syntax).

- One can bind additional de Bruijn positions using the syntax
  ``additional` OIdents . Term``.  For example, ``additional` x y . y``
  resolves to index 0; and if `z` resolves to index 3, then
  ``additional` x y . z`` resolves to index 5.

- One can exclude a variable from appearing within a term using the
  syntax ``exclude` Ident in Term``.  This is occasionally useful for
  pruning evar dependencies, to assist unification.

- The syntax for inductive functions appears
  [here](datatypes.html#inductive-functions).


#### Literal terms

The `LTerm` ("literal term") grammar represents internal terms
directly.  It uses de Bruijn indices rather than names and offers very
few conveniences.  It also provides a notation for explicit
substitution.

    LTerm ::=
      fn . [LTerm]                                                   (lambda)

      LTerm = LTerm : LTerm                                          (equality)
      LTerm = LTerm : type                                           (type equality)

      [LTerm] LTerm                                                  (application)
      [LTerm] #1                                                     (first projection)
      [LTerm] #2                                                     (second projection)
      [LTerm] #prev                                                  (unscoped future elim)
      next LTerm                                                     (future intro)

      [LTerm] [ Sub ]                                                (substitution)

      ( LTerm )
      ()                                                             (unit)
      ( LTerm, LTerm )                                               (pair)
      U                                                              (universe w/o argument)
      Number                                                         (de Bruijn index)
      \ ... antiquoted internal term ... \
      ` Longident
      z` Number                                                      (integer literal)

    Sub ::=
      [Sub] o Sub                                                    (composition)

      LTerm . [Sub]                                                  (substitution cons)
      Number . [Sub]                                                 (special case of cons)
      ^ Number                                                       (shift)
      id                                                             (identity, same as ^ 0)
      ( Sub )

Notes:

- The innermost de Bruijn index is 0.

- Literal terms do not insert implicit arguments.  Nevertheless, the
  tick form (`` ` ``) is still useful for using constants whose names
  collide with a keyword.

- In the internal representation for explicit substitutions, there is
  a special case of substitution cons for when the term being consed
  is an index.


#### Parsing functions

Most of the nonterminals above can be parsed by various pervasive
functions: `parseIdent`, `parseIdents`, `parseLongident`,
`parseOIdent`, `parseOIdents`, `parseBinding`, `parseBindings`,
`parseLTerm`, `parseSub`.

These functions are all actually the identity function, but IML is
instructed to parse their argument using the indicated nonterminal.



#### Implicit and invisible arguments

Some constants take implicit and/or invisible arguments:

- Implicit arguments are not seen by the user, but they are present in
  the real term "under the hood."  The process of converting external
  terms to internal terms inserts evars for implicit arguments, which
  are then usually resolved by unification.

  If the user wants to suppress the insertion of implicit arguments
  (for example, because one wants to give them explicitly), one can
  precede the constant with a tick (`` ` ``).

- Invisible arguments, on the other hand, are not present in the real
  term at all, even "under the hood."  They arise when a function has
  a type like `intersect (x : A) . B`.  Such a function has the type
  `B` for any choice for `x` of type `A`, but that choice is not
  passed in to the function at all.

  Sometimes it is necessary to specify a function's invisible argument
  because typechecking is unable to work it out itself.  To do so, one
  employs visibilized application by writing `f ap m` to indicate that
  the `f`'s invisible argument should be filled in with `m`.

  Visibilized application is only a hint for the type checker; such
  arguments are still not passed into the function.  Thus, `f ap m`
  unfolds to just `f`.

For example, `List.map` has type:

    intersect i . forall (a b : U i) . (a -> b) -> list a -> list b

and has two implicit arguments.  Thus, its first argument (`i`) is
invisible, and its second and third arguments (`a` and `b`) are
implicit.  Normally one calls `List.map` with just the explicit
arguments; so `List.map F L` means:

    `List.map _ _ F L

If, instead, one wanted to supply all the arguments, one would write
something like:

    `List.map ap I A B F L

The `ap I` fills in the invisible argument, while the starting tick
suppresses the insertion of evars for implicit arguments, so `A` and
`B` can be supplied.

Note that implicit arguments are inserted first, so 
`List.map ap I F L` would mean:

    `List.map _ _ ap I F L`

which is probably not desired.  But rarely would one want to give
only the invisible arguments explicitly anyway.



#### Opacity

Constants have one of five levels of opacity: soft, firm, soft-strict,
hard, or opaque:

                      OPAQUE
                        |
                       HARD
                     /      \
                FIRM          SOFT_STRICT
                     \      /
                       SOFT


- Hard: the default opacity for a constant with a definition.  The
  constant can be unfolded, and a few tactics (notably `intro` and
  `destruct`) will unfold it automatically.  It is never unfolded
  automatically by unification.  It is not unfolded in typechecking,
  except that it *is* unfolded when necessary to infer the type of a
  spine.  For instance, when inferring the type of `f x y`, if the
  type of `f x` is a hard constant, that constant will be unfolded so
  inference can continue with the next argument.

- Opaque: the constant cannot be unfolded.  Any constant without a
  definition is opaque, but not vice versa; opaque constants can have
  definitions.

- Soft: the constant is automatically unfolded by unification,
  typechecking, and a variety of tactics.  Soft constants are best
  viewed as abbreviations.  Giving a type to a soft constant usually
  serves no purpose (other than documentation) because the typechecker
  automatically unfolds it before determining its type.

- Firm: like a soft constant, except the constant is not unfolded by
  the typechecker in the subject position.  Thus, a firm constant can
  be given a type for the typechecker to use.  This is typically used
  for constants whose purpose is to give
  [assistance to the typechecker](typechecking.html#coping-strategies) 
  (`ann`, `ap`, `fnann`, `manualf`).

- Soft-strict: like a soft constant, except that when unification is
  presented with a constraint equating two terms whose head are the
  same soft-strict constant, unification will unify the corresponding
  terms along the spine, rather than unfolding the constant.

   Note that Istari does not check that this is correct.  Marking a
   constant as soft-strict that is not actually strict will not
   compromise soundness, but it will cause unification to fail
   sometimes when it need not fail.

A constant's opacity can be altered using the function `setOpacity`.
Since opacities can be altered, an opaque constant is not entirely
abstract.  To make a constant abstract, one may delete a constant's
definition, thereby rendering it permanently opaque, using the
function `abstract`.

    (* abbreviated *)
    signature CONSTANT =
       sig
          ...

          datatype opacity = SOFT | FIRM | SOFT_STRICT | HARD | OPAQUE
    
          (* returns the constant's definition if the constant is not OPAQUE *)
          val definition : constant -> term option
    
          val opacity : constant -> opacity
          val setOpacity : constant -> opacity -> unit
    
          (* sets opacity to OPAQUE and deletes the definition (cannot be reversed) *)
          val abstract : constant -> unit
       end

    structure Constant : CONSTANT

The `Constant.setOpacity` function is pervasive and it parses its
first argument as a constant, so a constant's opacity can be easily
set by executing `setOpacity /foo/ Constant.SOFT`, for example.
