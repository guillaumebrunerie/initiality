Introduction
------------

This project aims at giving a formalized proof in Agda of a version of the initiality conjecture.
See tag v2.0 for a proof of initiality for a type theory with Pi-types, Sigma-types, natural
numbers, identity types, binary sum types, the empty and unit types, and an infinite hierarchy of
universes.

This project has been tested to work on Agda 2.6.1 with the `+RTS -M25G -RTS` options (requires 25G
of RAM).

Some design decisions
---------------------

The raw syntax of the type theory is defined using de Bruijn indices for the variables, and terms
are fully annotated. Typing rules are mostly standard, except that we never check that a context is
well-typed, instead we only check that the *type* is well-typed when using the variable rule. There
is moreover a little bit of paranoia in some of the rules.

For the semantics, we state initiality with contextual categories whose additional structure is as
close to the syntax as possible.

Metatheory
----------

We are using standard Agda with the sort `Prop` of strict propositions (needs the `--prop` flag)
(see https://hal.inria.fr/hal-01859964v2/document).
We are also using a few axioms:
- dependent function extensionality (three axioms, for the cases when the domain is a type, a
  proposition, or implicit)
- propositional extensionality, phrased with `Prop`
- existence of quotients for `Prop`-valued equivalence relations, with a definitional computation
  rule (defined using rewrite rules, needs the `--rewriting` flag).

Files
-----

- `common.agda`: basic definitions used throughout the development
- `typetheory.agda`: raw syntax of the type theory
- `reflection.agda`: a basic reflection library (used in `syntx.agda`)
- `syntx.agda`: properties of the raw syntax
- `rules.agda`: typing rules and admissible rules
- `contextualcat.agda`: models of the type theory
- `contextualcatmor.agda`: morphisms between models of the type theory
- `quotients.agda`: quotients (postulated)
- `termmodel-common.agda`: preliminary definitions and helper functions for the term model
- `termmodel-synccat.agda`: the contextual category part of the term model
- `termmodel-X.agda`: the part of the term model related to type former X
- `termmodel.agda`: the full term model
- `partialinterpretation.agda`: the partial interpretation function
- `interpretationsubstitution.agda`: commutation of substitution and the interpretation function
- `interpretationweakening.agda`: commutation of weakening and the interpretation function
- `totality.agda`: totality of the partial interpretation function
- `initiality-existence.agda`: existence part of the proof of initiality of the term model
- `initiality-uniqueness.agda`: uniqueness part of the proof of initiality of the term model
