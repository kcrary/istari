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
indices.

#### The term grammar

The default grammar for terms is as follows.  Capitalized words are
nonterminals; lower case words are keywords.  (**Exception:** `U` and
`K` are keywords.)  Forms are listed in increasing order of
precedence.  Grouped forms have the same precedence.  Associativity,
when appropriate, is given by an L or R.

    Term ::=
      fn OIdents . Term                                              (lambda)
      forall Bindings . Term                                         (dependent product)  
      exists Bindings . Term                                         (strong dependent sum)
      iforall Bindings . Term                                        (impredicative universal)
      iexists Bindings . Term                                        (impredicative existential)
      intersect Bindings . Term                                      (intersection type)
      foralltp OIdents . Term                                        (impredicative polymorphism)
      rec Ident . Term                                               (recursive type)
      mu Ident . Term                                                (inductive type)
      wtype ( Ident : Term ) . Term                                  (W type)
      quotient ( Ident Ident : Term ) . Term                         (quotient type)
      Term -> Term                                                   (ordinary arrow) R
      Term -t> Term                                                  (tarrow kind) R 
      Term -k> Term                                                  (karrow kind) R
      Term -g> Term                                                  (guard) R
      let Ident = Term in Term                                       (let)
      let next Ident = Term in Term                                  (scoped future elim)
      case Term of | inl OIdent . Term | inr OIdent . Term           (sum elim)
      Term : Term                                                    (typing)
      Term : type                                                    (type formation)

      if Term then Term else Term                                    (if-then-else)

      Term % Term                                                    (sum type) R

      Term & Term                                                    (product type) R

      Term = Term : Term                                             (equality)
      Term = Term : type                                             (type equality)
      Term <: Term                                                   (subtyping)
      Term <:> Term                                                  (extensional type equivalence)
      Term <= Term                                                   (natural number inequality)
      Term < Term                                                    (natural number inequality)
      Term <l= Term                                                  (level inequality)

      Term :: Term                                                   (cons) R

      Term + Term                                                    (natural number plus) L
      Term - Term                                                    (natural number minus) L

      Term Term                                                      (application) L
      Term #1                                                        (first projection)
      Term #2                                                        (second projection)
      Term #prev                                                     (unscoped future elim)
      pi1 Term                                                       (first projection)
      pi2 Term                                                       (second projection)
      prev Term                                                      (unscoped future elim)
      next Term                                                      (future intro)
      inl Term                                                       (sum intro)
      inr Term                                                       (sum intro)
      U Level                                                        (universe)
      K Level                                                        (kind)
      Term :> Term                                                   (type annotation) L
      Term ap Term                                                   (visibilized application) L
      Term _# Number                                                 (application to multiple evars)

      ( Term )
      ()                                                             (unit)
      ( Term , ... , Term )                                          (tuple, length at least 2)
      { Ident : Term | Term }                                        (set type)
      { Term }                                                       (squashed type)
      Longident                                                      (identifier)
      Number                                                         (natural number literal)
      _                                                              (evar)
      __                                                             (marker)
      \ ... antiquoted internal term ... \
      ` Longident
      l` LTerm                                                       (literal term)
      level` Level                                                   (level expression)
      z` Number                                                      (integer literal)

    OIdent ::=
      Ident
      _

    OIdents ::=
      OIdent ... OIdent                                              (length can be zero)

    Binding ::=
      OIdent                                                         (binding using evar for type)
      (OIdent : Term)                                                (binding with type supplied)

    Bindings ::=       
      Binding ... Binding                                            (length can be zero)

    Level ::=
      Number + Level                                                 (level plus)

      ( Level )
      Number                                                         (level literal)
      [ Level ... Level ]                                            (level max, length at least 1)
      Ident                                                          (identifier)
      \ ... antiquoted internal term ... \


Notes:

- Note that the typing and type formation have lower precedence than equality and type equality.

- Note that `fn _ . M` and `fn . M` are two different terms.  The
  former is a lambda that ignores its argument, while the latter takes
  no arguments so it is actually the same as `M`.

- The pair form is `(Term , Term)`, not `(Term, Term)` or
  `(Term,Term)`.  (Observe the whitespace on both sides of the comma.)
  For example, because of how IML [tokenizes
  input](iml.html#tokenization), the `x,` in `(x, y)` forms a single
  token, rather than two, which will result in a syntax error.

- A tick (`` ` ``) before an identifier defeats the insertion of
  implicit arguments.  It also allows the identifier to be any constant
  name, even if the name collides with a keyword.

- An [antiquoted](iml.html#antiquote) internal term should have type `Term.term`.

- A marker (`__`) is not a valid term in the logic.  It is a
  placeholder used by some tactics (*e.g.,* `so`).

- One can bind additional de Bruijn positions using the syntax
  `additional OIdents . Term`.  For example, `additional x y . y`
  resolves to index 0; and if `z` resolves to index 3, then
  `additional x y . z` resolves to index 5.


#### Literal terms

The `LTerm` ("literal term") grammar represents internal terms
directly.  It uses de Bruijn indices rather than names and offers very
few conveniences.  It also provides a notation for explicit
substitution.

    LTerm ::=
      fn . LTerm                                                     (lambda)

      LTerm = LTerm : LTerm                                          (equality)
      LTerm = LTerm : type                                           (type equality)

      LTerm LTerm                                                    (application) L
      LTerm #1                                                       (first projection)
      LTerm #2                                                       (second projection)
      LTerm #prev                                                    (unscoped future elim)
      next LTerm                                                     (future intro)

      LTerm [ Sub ]                                                  (substitution)

      ( LTerm )
      ()                                                             (unit)
      ( LTerm, LTerm )                                               (pair)
      U                                                              (universe w/o argument)
      Number                                                         (de Bruijn index)
      \ ... antiquoted internal term ... \
      ` Longident
      z` Number                                                      (integer literal)

    Sub ::=
      Sub o Sub                                                      (composition) L

      LTerm . Sub                                                    (substitution cons)
      Number . Sub                                                   (special case of cons)
      ^ Number                                                       (shift)
      id                                                             (identity, same as ^0)
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
