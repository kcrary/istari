# Case analysis

Istari includes a library `Case` that supplies a convenient mechanism
to case-analyzing terms and other forms in the logic.

### An example

Suppose we wish to case-analyze the current goal's conclusion, and
isolate the cases where it is `forall`, `->`, or anything else.  The
`forall` constant is just `forall` and it takes two arguments: a type
(the domain), and a function returning a type (the codomain).  The
`->` constant is `arrow` and it takes two types as arguments.

Then we write:

    goalCase
    /
      forall ? (fn . ?) =>
      \(fnc dom cod => ... do the forall thing ...)\

    | arrow ? ? =>
      \(fnc dom cod => ... do the arrow thing ...)\

    | _ =>
      \(fnc => ... do the catch-all thing ...)\
    /

This consists of three clauses, separated by `|`.  In each clause we
typically give a pattern, then `=>`, then code for that case.

Consider the first clause.  It matches against `forall` applies to two
arguments.  The first argument (`?`) matches anything, and produces a
binding.  The second argument (`fn . ?`) matches only lambda, but the
lambda's body (again `?`) may take any form, and produces a second
binding.

The `=>` serves to attach code to that pattern.  The code is
[antiquoted](iml.html#antiquote) IML code.  The parentheses within the
antiquote are not necessary but are good style.  (Also, Emacs is
happier with them.)  The IML code uses the `fnc`
[form](iml.html#anonymous-multi-argument-functions) which takes an
iterated pair as its argument.  The arguments are the bindings
produced by `?` in the pattern, in the order they appeared.

The second clause is similar but simpler.  The third clause is simpler
still, but illustrates the wildcard pattern (`_`), which matches
anything but does not produce a binding.

Note that `goalCase` and its cousins do not build decision trees; they
simply try each clause in order.  This is usually fine, but if
performance is critical one may need to use primitive ML case analysis
instead of `Case`.


### A context example

We can also case analyze the context, instead of the conclusion.
Suppose we wish to find any hypothesis whose type is `forall` or
`->`.  Then we write:

    goalContextCase
    /
      $anyhyp 
        ($tm 
           (
             forall ? (fn . ?) =>
             \(fnc dom cod => fn hyp => ... do the forall thing ...)\
           |
             arrow ? ? =>
             \(fnc dom cod => fn hyp => ... do the arrow thing ...)\
           ))
     /

The `$anyhyp` pattern tells it to match against any hypothesis.  Its
argument is a pattern for hypotheses.  The `$tm` pattern matches
normal hypotheses (by far the most common sort).  The argument to
`$tm` consists of two clauses separated by `|`, similar to the
previous example.

Each clause takes the bindings produced by the pattern, and -- unlike
the previous example -- returns a function.  This is because of the
`$anyhyp` pattern, which expects an `int -> tactic` instead of a
tactic.  Then `$anyhyp` calls that function with the number of the
hypothesis it is matching against (counting backward from 0), so that
the IML code knows what hypothesis it is operating on.

As a syntactic point, the parentheses around the argument to `$anyhyp`
(that is, the parentheses around`$tm (... | ...)`) are not necessary.
Application of case-analysis operators that begin with `$` are right
associative.  So the example could have been written a little more
compactly, beginning with just `$anyhyp $tm`.


### Entry points

There are many entry points into the case-analysis mechanism.  A few
of the most important are:

- `goalCase /[term matcher]/`

  Matches against the current goal's conclusion and returns a tactic,
  which is applied to that goal.  Once it matches the conclusion and
  determines the tactic, it does not backtrack into other clauses,
  even if the tactic fails or some subsequent tactic fails.

- `goalCaseB /[term matcher]/`

  Like `goalCase`, but it will backtrack into other clauses if the
  tactic fails, or if some subsequent tactic fails.

- `termCase /[term]/ /[term matcher]/`

  Like `goalCase`, but matches on a given term rather than the current
  goal's conclusion.

- `termCaseB /[term]/ /[term matcher]/`

  Like `goalCaseB`, but matches on a given term rather than the
  current goal's conclusion.

- `termCaseX /[term]/ /[term matcher]/`

  Like `termCase` but the result can have any type.  If no clauses
  apply, `termCaseX` raises the `NoMatch` exception.

- `goalContextCase /[context matcher]/`

  Like `goalCase`, but matches the current goal's context.

- `goalContextCaseB /[context matcher]/`

  Like `goalCaseB`, but matches the current goal's context.


### Details

The `Case` mechanism consists of collection of matching combinators, a
collection of entry points, and a parser that makes those combinators
nicer to read and write.

The central type is an `('a, 'b, 'c) matcher`.  In this, `'a` is the
type being matched, `'b` is the type of all the bindings we have
collected already, and `'c` is the type of the result.

The most important combinators are:

    val wild : ('a, 'b, 'b) matcher
    val what : ('a, 'b, 'b * 'a) matcher
    val wrap : ('a, 'b, 'c) matcher -> ('c -> 'd) -> ('a, 'b, 'd) matcher
    val alt  : ('a, 'b, 'c) matcher list -> ('a, 'b, 'c) matcher

- `wild` matches `'a` but generates no bindings, so it returns the
  same type as the bindings collected so far (`'b`).  In the parser
  `wild` is written `_`.

- `what` matches `'a` and adds it to the end of the bindings collected
  so far, turning `'b` into `'b * 'a`.  In the parser, `what` is
  written `?`.

- `wrap m f` (where `m` and `f` have the types given above) defers to
  `m` to match `'a`, and hands `m` the bindings collected so far (of
  type `'b`).  When `m` returns a result of type `'c`, `wrap` calls
  `f` to obtain a result of type `d`, which it returns.  In the
  parser, `wrap m f` is written `m => f`.

  Note that successive uses of `what` will result in an
  left-associated iterated pair, making IML's `fnc` form appropriate
  for `f`.

- `alt [m1, ..., mn]` tries each matcher `mi` in turn.  In the parser,
  it is written `m1 | ... | mn`.


##### Matching term heads

    val constant : Term.constant -> (term, 'a, 'a) matcher
    val variable : int -> (term, 'a, 'a) matcher
    val whatConstant : (term, 'a, 'a * Term.constant) matcher
    val whatVar : (term, 'a, 'a * int) matcher
    val whatEvar : (term, 'a, 'a * (Term.ebind * Term.sub)) matcher

- `constant [const c]` matches `c`, producing no bindings.  In the
  parser, this is written as the name of the constant, or using an
  antiquoted expression of type `constant`.

- `variable [number n]` matches the variable with index `n`, producing
  no bindings.

- `whatConstant` matches any constant, producing a binding to that
  constant.  In the parser it is written `const?`.

- `whatVar` matches any variable, producing a binding to its index.
  In the parser it is written `var?`.

- `whatEvar` matches any evar, producing a binding to its `ebind` and
  substitution.  In the parser it is written `evar?`.

##### Matching terms

    val elim    : (term, 'a, 'b) matcher -> (spine, 'b, 'c) matcher -> (term, 'a, 'c) matcher
    val lam     : (term, 'a, 'b) matcher -> (term, 'a, 'b) matcher
    val lamb    : (term, 'a * Term.binder, 'b) matcher -> (term, 'a, 'b) matcher
    val pair    : (term, 'a, 'b) matcher -> (term, 'b, 'c) matcher -> (term, 'a, 'c) matcher
    val next    : (term, 'a, 'b) matcher -> (term, 'a, 'b) matcher
    val triv    : (term, 'a, 'a) matcher
    val marker  : Symbol.symbol -> (term, 'a, 'a) matcher
    val nat     : (term, 'a, 'a * int) matcher
    val integer : (term, 'a, 'a * IntInf.int) matcher

- `elim m1 m2` matches an elimination form; `m1` matches against the
  head and `m2` matches against the
  [spine](primitive-tactics.md#spinal-form).  In the parser it is
  written `m1 @ m2`.

- `lam m` matches a lambda; `m` matches against the body.  In the
  parser it is written `fn . m`.

- `lamb m` also matches a lambda.  First a binding is producer for the
  lambda's binder, then `m` matches against the body.  In the parser
  it is written `fn ? . m`.

- `pair m1 m2` matches a pair; `m1` matches against the left
  constituent and `m2` against the right.  In the parser it is written
  `(m1 , m2)`.  The parser also accepts a tuple longer than two, which
  is interpreted as a right-associated iterated pair.

- `next m` matches a future intro; `m` matches against the body.  In
  the parser it is written `next m`.

- `triv` matches against the `()` term, producing no bindings.  In the
  parser it is written `()`.

- `marker sym` matches against a marker term carrying `sym`, producing
  no bindings.  Normally `sym` is the empty symbol.  In the parser it
  is written `$marker \ sym \`.

- `nat` matches against natural number literals, producing a binding
  of the corresponding int.  In the parser it is written `nat?`.

- `integer` matches against integer literals, producing a binding of
  the corresponding integer.  In the parser it is written `integer?`.

##### Other term combinators

    val unify    : term -> (term, 'a, 'a) matcher
    val whnf     : (term, 'a, 'b) matcher -> (term, 'a, 'b) matcher
    val whnfHard : (term, 'a, 'b) matcher -> (term, 'a, 'b) matcher

- `unify t` matches against any term that unifies with `t`, producing
  no bindings.  In the parser it is written `$unify \ ... antiquoted
  internal term ... \`.

- `whnf m` weak-head normalizes the term being matched before passing
  it to `m`.  In the parser it is written `$whnf m`.

- `whnfHard m` hard weak-head normalizes the term being matched before
  passing it to `m`.  In the parser it is written `$whnfHard m`.



##### Matching spines

    val null : (spine, 'a, 'a) matcher
    val app : (term, 'a, 'b) matcher -> (spine, 'b, 'c) matcher -> (spine, 'a, 'c) matcher
    val pi1 : (spine, 'a, 'b) matcher -> (spine, 'a, 'b) matcher
    val pi2 : (spine, 'a, 'b) matcher -> (spine, 'a, 'b) matcher
    val prev : (spine, 'a, 'b) matcher -> (spine, 'a, 'b) matcher

- `null` matches against the empty spine, producing no bindings.
  In the parser it is written `$nil`.

- `app m1 m2` matches against a spine that begins with application;
  `m1` matches against the argument, and `m2` matches against the rest
  of the spine.  In the parser it is written `$ap m1 m2`.

- `pi1 m` matches against a spine that begins with `#1`; `m` matches
  against the rest of the spine.  In the parser it is written `#1 m`.

- `pi2 m` matches against a spine that begins with `#2`; `m` matches
  against the rest of the spine.  In the parser it is written `#2 m`.

- `prev m` matches against a spine that begins with `#prev`; `m`
  matches against the rest of the spine.  In the parser it is written
  `#prev m`.

Suppose you want to match `arrow` applied to two arguments.  In IML
syntax you were use the combinators thus:

    elim (const (parseConstant /arrow/)) (app what (app what null))

In the parser, you can write it in three different ways.  One is to
transliterate the above:

    arrow @ $ap ? $ap ? $nil

But this pattern (a constant applied to a spine of known length) is so
common that there is an abbreviated syntax:

    arrow ? ?

(Compare this with the example at the top of the page.)  In the
abbreviated syntax, we can also replace the head constant's name with
an antiquoted expression of type `const`:

    \(parseConstant /arrow/)\ ? ?

One typically would use this form when the head constant varies.


##### Matching hypotheses

There is one matching combinator for each sort of hypothesis:

    val tm   : (term, 'a, 'b) matcher -> (hyp, 'a, 'b) matcher
    val tml  : (term, 'a, 'b) matcher -> (hyp, 'a, 'b) matcher
    val tmh  : (term, 'a, 'b) matcher -> (hyp, 'a, 'b) matcher
    val tp   : (hyp, 'a, 'a) matcher
    val tpl  : (hyp, 'a, 'a) matcher
    val lett : (term, 'a, 'b) matcher -> (hyp, 'a, 'b) matcher

In the parser they are written `$tm`, `$tml`, `$tmh`, `$tp`, `$tpl`,
`$let`.


##### Matching contexts

    val hyp    : int -> (hyp, 'a, 'b) matcher -> (context, 'a, 'b) matcher
    val anyhyp : (hyp, 'a, int -> 'b) matcher -> (context, 'a, 'b) matcher

- `hyp i m` is used to match against a specific hypothesis; `m`
  matches against hypothesis number `i` (counting backward from 0).
  In the parser it is written `$hyp n` (when n is known), or (more
  commonly) `$hyp \ ... antiquoted integer expression ... \`.

- `anyhyp m` is used to match against *any* hypothesis; `m` matches
  first against hypothesis 0, then 1, etc.  If `m` fails against all
  hypothesis, `anyhyp m` backtracks.

  The sub-matcher `m` must return a function `int -> 'b`.  That
  function is applied to the hypothesis number to obtain the value to
  return.

**Note:** in both `hyp` and `anyhyp` the hypothesis is shifted to put
it in the same scope that the conclusion sees before it is passed to
`m`.  That is, when matching hypothesis number `i`, the hypothesis
would be shifted `i+1` before matching it.


##### Other generic combinators

    val az    : ('a, 'b * 'a, 'c) matcher -> ('a, 'b, 'c) matcher
    val cond  : ('a, 'b, 'c option) matcher -> ('a, 'b, 'c) matcher
    val tri   : ('a -> 'b) -> ('a -> 'b option)
    val wrapk : ('a, 'b, 'c) matcher -> ('c -> 'd) -> ('a, 'b, 'd) matcher
    val seq   : ('a, 'c, 'd) matcher -> ('b, 'd, 'e) matcher -> ('a * 'b, 'c, 'e) matcher

- `az m` is like an `as` pattern in ML.  It produces a binding for the
  whole item, but it also passes the whole item to a sub-matcher `m`
  for additional matching.  The `az` binding takes place before the
  additional matching, so the `'b` bindings collected already become
  `'b * 'a` when they are handed to `m`.  In the parser, `az m` is
  written `$as m`. (`$az m` is also accepted.)

- `cond m` calls the sub-matcher `m`.  If `m` returns `SOME v` then
  `cond m` returns `v`.  If `m` returns `NONE`, then `cond` backtracks
  to the next applicable clause.

- `tri m` ("try") calls the sub-matcher `m`.  If `m` returns `v` then
  `tri m` returns `SOME v`.  If `m` raises `Backtrack` then `tri m`
  returns `NONE`.

- `wrapk m f` is like `wrap m f`, but if the wrapper `f` raises the
  `Backtrack` exception, `wrapk` backtracks to the next applicable
  clause.  Equivalent to `cond (wrap m (tri f))`.  In the parser,
  `wrapk m f` is written `m =!> f`.

- `seq m1 m2` matches on a pair of type `'a * 'b`.  The left-hand
  component is sent to `m1`, then the right to `m2`.  In the parser,
  `seq m1 m2` is written `m1 ; m2`.


##### Recursive matching

    type ('a, 'c) rmatcher
    val use : ('a, 'c) rmatcher -> ('a, 'b, 'b * 'c) matcher
    val fix : (('a, 'c) rmatcher -> ('a, unit, 'c) matcher) -> ('a, 'b, 'b * 'c) matcher

The `fix` combinator enables recursive matching.  Consider the two
types:

    ('a, 'b, 'b * 'c) matcher
    ('a, unit, 'c) matcher

These types are isomorphic: they both represent a matcher that matches
against `'a`, producing `'c`.  Then think of `('a, 'c) rmatcher` as a
third type that is isomorphic to both of them.  The `use` combinator
employs the isomorphism between the first type and the third.  The `fix`
combinator employs all three; if we blur the distinction between the
three isomorphic types and call them `T`, it has type `(T -> T) -> T`.
Thus we can use it to build recursive matchers.

In the parser `use x` is written `$use \ x \`, and `fix (fn x => m)` is
written `$lit \(fix (fn x => m))\`.


#####  Entry points

The full collection of entry points is:

    (* Returns arbitrary type, raises NoMatch when matching fails. *)
    val termCaseX    : term -> (term, unit, 'a) matcher -> 'a
    val unitCaseX    : (unit, unit, 'a) matcher -> 'a
    val term2CaseX   : term -> term -> (term * term, unit, 'a) matcher -> 'a
    val term3CaseX   : term -> term -> term -> (term * (term * term), unit, 'a) matcher -> 'a
    val spineCaseX   : spine -> (spine, unit, 'a) matcher -> 'a
    val hypCaseX     : hyp -> (hyp, unit, 'a) matcher -> 'a
    val contextCaseX : context -> (context, unit, 'a) matcher -> 'a

    (* Returns a tactic.  Backtracks when matching fails.  Will not try other
       matches when the resulting tactic or subsequent tactics fail. *)
    val termCase        : term -> (term, unit, 'a tacticm) matcher -> 'a tacticm
    val unitCase        : (unit, unit, 'a tacticm) matcher -> 'a tacticm
    val term2Case       : term -> term -> (term * term, unit, 'a tacticm) matcher -> 'a tacticm
    val term3Case       : term -> term -> term -> (term * term * term, unit, 'a tacticm) matcher -> 'a tacticm
    val spineCase       : spine -> (spine, unit, 'a tacticm) matcher -> 'a tacticm
    val hypCase         : hyp -> (hyp, unit, 'a tacticm) matcher -> 'a tacticm
    val contextCase     : context -> (context, unit, 'a tacticm) matcher -> 'a tacticm
    val goalCase        : (term, unit, 'a tacticm) matcher -> 'a tacticm
    val goalContextCase : (context, unit, 'a tacticm) matcher -> 'a tacticm

    (* Returns a tactic.  Backtracks when matching fails.  Tries other matches 
       when the resulting tactic or a subsequent tactic fails. *)
    val termCaseB        : term -> (term, unit, 'a tacticm) matcher -> 'a tacticm
    val unitCaseB        : (unit, unit, 'a tacticm) matcher -> 'a tacticm
    val term2CaseB       : term -> term -> (term * term, unit, 'a tacticm) matcher -> 'a tacticm
    val term3CaseB       : term -> term -> term -> (term * term * term, unit, 'a tacticm) matcher -> 'a tacticm
    val spineCaseB       : spine -> (spine, unit, 'a tacticm) matcher -> 'a tacticm
    val hypCaseB         : hyp -> (hyp, unit, 'a tacticm) matcher -> 'a tacticm
    val contextCaseB     : context -> (context, unit, 'a tacticm) matcher -> 'a tacticm
    val goalCaseB        : (term, unit, 'a tacticm) matcher -> 'a tacticm
    val goalContextCaseB : (context, unit, 'a tacticm) matcher -> 'a tacticm


##### The matcher grammar

The grammar for matchers is as follows.  Capitalized words are
nonterminals; lower case words are keywords.

Forms are listed in increasing order of precedence.  Grouped forms
have the same precedence.  A subterm at the same level of precedence
is given in brackets.  For example, `Match ; [Match]` indicates that
`seq` is right associative.

    Match ::=
      Match | ... | Match                                (alt, length at least 2)
      | Match | ... | Match                              (alt, length at least 2)

      Match ; [Match]                                    (seq)

      Match => \ ... antiquoted function ... \           (wrap)
      Match =!> \ ... antiquoted function ... \          (wrapk)

      $lit \ ... antiquoted matcher ... \
      $as [Match]                                        (az)
      $az [Match]                                        (az)
      $use \ ... antiquoted rmatcher ... \               (use)

      ----------------   terms    ----------------
      Match @ [Match]                                    (elim)
      Constant Spine                                     (elim/constant, length at least 1)
      \ ... antiquoted constant ... \ Spine              (elim/constant, length at least 1)
      $var \ ... antiquoted index ... \ Spine            (elim/var, length at least 1)
      fn . [Match]                                       (lam)
      fn ? . [Match]                                     (lamb)
      next [Match]                                       (next)
      $marker \ ... antiquoted symbol ... \              (marker)
      $unify \ ... antiquoted term ... \                 (unify)
      $whnf [Match]                                      (whnf)
      $whnfHard [Match]                                  (whnfHard)
      ----------------   spines   ----------------
      $nil                                               (null)
      $ap Match [Match]                                  (app)
      #1 [Match]                                         (pi1)
      #2 [Match]                                         (pi2)
      #prev [Match]                                      (prev)
      ---------------- hypotheses ----------------
      $tm [Match]                                        (tm)
      $tml [Match]                                       (tml)
      $tmh [Match]                                       (tmh)
      $tp [Match]                                        (tp)
      $tpl [Match]                                       (tpl)
      $let [Match]                                       (lett)
      ----------------  contexts  ----------------
      $hyp Number [Match]                                (hyp)      
      $hyp \ ... antiquoted number ... \ [Match]         (hyp)
      $anyhyp [Match]                                    (anyhyp)

      ( Match )
      _                                                  (wild)
      ?                                                  (what)
      ()                                                 (triv)
      ----------------   terms    ----------------
      Constant                                           (constant)
      \ ... antiquoted constant ... \                    (constant)
      $var \ ... antiquoted index ... \                  (variable)
      const?                                             (whatConstant)
      var?                                               (whatVar)
      evar?                                              (whatEvar)
      nat?                                               (nat)
      integer?                                           (integer)
      ( Match , ... , Match )                            (pair, length at least 2)

    Spine ::=
                                                         (null)
      Match [Spine]                                      (app)
      #1 [Spine]                                         (pi1)
      #2 [Spine]                                         (pi2)
      #prev [Spine]                                      (prev)
      
Note that a path can be matched in two different ways: the simple form
`Constant Spine`, or the general form `Constant @ Match` where `Match`
matches the spine.  (Variable-headed paths are similar.)  The
simple form is usually more convenient, but unlike the general form,
it provides no facility to bind a variable to the spine itself (or a
suffix of it); it can only bind to the applicands.  The simple form
also provides no facility for matching an unknown head.

One can parse a matcher using `parseMatch`, which is actually the
identity function, but IML is instructed to parse its argument using
the `Match` grammar.  For example, one might write a recursive
matcher:

    $lit \(fix (fn x => parseMatch / ... body ... /))\

