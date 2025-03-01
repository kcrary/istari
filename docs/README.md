# The Istari Proof Assistant

Istari is a tactic-oriented proof assistant based on Martin-Lof type
theory.  It is intended for mathematical developments that involve
computation -- particularly imperative computation -- and dependent types.


### Overview

The Istari workflow is similar to proof assistants such as Coq: one
proves a theorem by building a *proof script*, which consists mostly
of invocations of *tactics*.  Each tactic acts on a current goal, and
generates zero or more new subgoals.

Istari proof scripts and tactics are ordinary ML code, written in a
dialect called IML that is close to Standard ML.  User tactics enjoy
the same access to the prover's internals as the vast majority of the
built-in tactic library.  As in some earlier proof assistants (notably
LCF), user tactics can manipulate proof objects (called validations)
and soundness is ensured using abstract types.

As Istari is based on Martin-Lof type theory, Istari's typing
judgement is a proposition **within** the type theory, rather than an
external mechanism (as is more typical in proof assistants).  This
creates advantages and disadvantages: The main advantage is there is
no distinction between definitional equality and user-established
equalities.  Thus, an equality proven by the user is just as valid for
typechecking purposes as any another.  For example, if `M : A(N)` and
`N = N'`, then `M : A(N')`.  In many proof assistants, this principle
works for definitional equalities but not user-established equalities,
which can create severe challenges when using dependent types.

On the disadvantage side, typechecking is undecidable, since it can
depend on arbitrary mathematical facts.  In practice, the typechecker
usually attends to typechecking obligations, but sometimes one sees
proof goals of the form `M : A`.  Often these indicate type errors,
but sometimes they are true facts that the typechecker was unable to
prove on its own.

In contrast to many Martin-Lof type theories, Istari supports
impredicative quantification (as well as the usual predicative
hierarchy of universes).  Istari is also unique in that it supports
guarded recursive types, and indeed impredicative quantification over
guarded recursive kinds.  Guarded recursive kinds make it possible to
reason about imperative code that uses higher-order state.

The Istari type theory is itself formalized using a different proof
assistant (Coq), and essentially all of the Istari inference rules are
validated using that formalization.

---


### Table of contents:

- [Installation](install.html)

- [Type theory](type-theory.html)

- [IML](iml.html)

- [UI](ui.html)

- [Batch mode](batch.html)

- [Term syntax](terms.html)

- [Theorems](theorems.html)

- [Definitions](definitions.html)

- [Datatypes](datatypes.html)

- [Tactics](tactics.html)

- [Typechecking](typechecking.html)

- [Rewriting](rewriting.html)

- [Reordering](reordering.html)

- [Modules](modules.html)

- [Files](files.html)

- [Registry](registry.html)

- [Case analysis](case.html)

- [Primitive tactics](primitive-tactics.html)

- [Unification](unification.html)

- [Proof irrelevance](proof-irrelevance.html)

- [Library](library.html)

- [IML basis](basis.html)

- [Change log](changelog.html)

- [Copyright](copyright.html)
