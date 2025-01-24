# Unification

Unification is the process of solving a set of syntactic equations
modulo beta equivalence, binding evars in the process.  It is the
central engine of the prover.  Note that beta equivalence here is
understood to include not just the contraction of conventional beta
redices, but also all installed reductions, as well as calculations on
native terms.

Usually, unification will bind an evar only when that binding is the
unique solution to an equation.  When an equation is ambiguous (that
is, when the solution is not unique), the equation is deferred, in the
hope that some other equation resolves the ambiguity.

For example, suppose we have the equation

    E[x / y] = x

There are two solutions: `E := x` and `E := y`.  Thus, the equation is
deferred, in the hope that some other equation determines `E`.

There are two exceptions [1] to this rule:

1. Consider the equation:

       E x = M x

   where `E` cannot depend on `x`.  There are two solutions: `E := M`
   and `E := fn x . M x`.  These are eta equivalent, but unification
   recognizes only beta equivalence.  (*Definitional equality* does
   recognize a form of eta equivalence appropriate to the type in
   question, but it is not relevant to unification.)  Thus, the two
   solutions are not equivalent.  We resolve the ambiguity in favor of
   the first solution.

2. Consider the equation:

       E[M / x] = M

   where `M` is not a variable.  There are two solutions: `E := M` and
   `E := x`.  We resolve the ambiguity in favor of the first solution.

   (Note that if `M` *is* a variable, the equation is deferred as
   discussed above.)


### Failure modes

When unification fails, the variable `Unify.errorMessage` is set to
explain why:

- `clash`

  The constraints include `M = N` where `M` and `N` have incompatible
  forms, or are paths with different heads.

- `elim clash`

  The constraints include `h spine = h spine'` in which a pair of
  corresponding elimination forms in `spine` and `spine'` are
  incompatible (*e.g.,* application and projection, or different
  projections).

- `pruning failure`

  The contraints include `E = M` where the evar `E` cannot take on
  the value `M` because there is:

  1. a scope violation (`M` contains `x` but `E` is not in the scope
     of `x`), or

  2. an occurs check violation (`M` is not `E` but `M` contains `E`).

- `ambiguous unification`

  Ambiguous equations remain after all solvable equations are solved.

These remaining errors cannot arise from well-typed equations:

- `incompatible spines`

  The constraints include `h spine = h spine'` in which the spines
  have different lengths but are compatible for the duration of the
  shorter one.

- `incompatible spines in evar`

  The constraints include `E M1 ... Mm = E N1 ... Nn` where `m <> n`.

- `evar in incompatible scopes`

  The constraints require the same evar to live in two different
  scopes (without substitution to resolve the issue).


### Discussion

Unification is not complete.  A system of constraints that has a
solution might not be solved, either because of ambiguous constraints,
or because one of the two preferences noted above sent unification
into a blind alley.

We have seen an example of the former.  As an example of the latter,
consider:

    E x = h x
    E = fn x . h x

If the first equation is solved first, then `E` becomes bound to `h`,
and the second equation becomes `h = fn x . h x` which fails.

A similar problem arises when unification settles on a non-unique
solution (such as `E := h` above) but another solution was intended
and the chosen solution creates problems later on.  This is the
**non-principal solution** problem.

Non-principal solutions can be unfortunate because they can lead to
confusion for the user.  The usual practice in higher-order pattern
unification is not to employ them [2].  However, in such settings one
usually enjoys eta equivalence.  That is not the case here.

In our setting, ruling out non-principal solutions would mean that
equations like `E x = M x` are unsolvable, and such equations happen
far too frequently for that to be acceptable.

Equations such as `E[M / x] = M` are less common, but when they do
arise, the `E := M` solution is intended the vast majority of the
time.  This is the behavior of every ML typechecker of which we are
aware [3].  Having already crossed the Rubicon into non-principal
solutions, it seems useful to allow this second sort as well.


### Orphans

On rare occasions, unification may produce the term `orphan`.  This
happens when a variable dependency that is being pruned out appears in
a term, but not in the term's normal form.  Consider:

    E = if true then x else y

where `E` is not in the scope of `y`.  Pruning succeeds because the
right-hand-side's normal form (`x`) does not depend on `y`.  However, for
performance reasons, Istari does not bind `E` to the normal form
but to a substitution instance of the original right-hand-side:

    (if true then x else y)[orphan / y]

(Explicit substitutions usually use much less space than the normal
forms of those substitutions, since the unsubstituted term can share
space with other occurrences of that term.)  When displayed, `E`
is bound to:

    if true then x else orphan

In all cases, orphans can be made to disappear by normalizing the term
in which they appear.


---

[1] The claim that all non-principal solutions fall into these two
categories is not currently proven.  (Nor is it obvious even how
to specify the two categories rigorously in general.)

[2] For example, see: Gille Dowek, Th&eacute;r&egrave;se Hardin, Claude
Kirchner, and Frank Pfenning. Unification via Explicit Substitutions:
The Case of Higher-Order Patterns. In *Joint International Conference
and Symposium on Logic Programming,* 1996.

[3] To see how such equations arise, see: Derek Dreyer, Robert Harper,
Manuel M.T. Chakravarty, and Gabriele Keller. Modular Type Classes.
In *Thirty-Fourth ACM Symposium on Principles of Programming Languages*,
2007. Section 4.6.
