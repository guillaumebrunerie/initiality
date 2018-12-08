Introduction
------------

This project aims at giving a formalized proof in Agda of a version of the initiality conjecture. A
complete proof for a type theory with only Pi-types and a base dependent type is available at commit
8e52bc0. We are now working on extending the type theory.

It requires a quite recent version of the master branch of Agda (to have the `variable` keyword,
`Prop` and various issues fixed). For instance commit agda/agda@8774611 works.

Metatheory
----------

We are using standard Agda with the sort `Prop` of strict propositions
(see https://hal.inria.fr/hal-01859964v2/document) and sized types.
The other axioms that we are using are:
- dependent function extensionality (three axioms, for the cases when the domain is a type, a
  proposition, or implicit)
- propositional extensionality, phrased with `Prop`
- existence of quotients for `Prop`-valued equivalence relations
The flag `--prop` is required to enable `Prop`, the flag `--rewriting` is required to have quotients
that compute. The flag `--without-K` is not required, but it’s nice to see that everything compiles
with it.

Files
-----

- `common.agda`: very basic definitions used everywhere
- `reflection.agda`: some basic definition for using reflection (used in a few places in `syntx.agda`)
- `quotients.agda`: quotients (postulated)
- `syntx.agda`: raw syntax of the type theory
- `rules.agda`: typing rules and admissible rules
- `contextualcat.agda`: the models of the type theory and morphisms between them
- `termmodel.agda`: the term model
- `partialinterpretation.agda`: the partial interpretation function
- `totality.agda`: totality of the partial interpretation function
- `initiality.agda`: initiality of the term model
