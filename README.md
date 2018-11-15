Introduction
------------

A formalized proof in Agda of a version of the initiality conjecture for a type theory with
Pi-types, a base type called U, and a dependent type called El. This is work in progress.

It requires a quite recent version of the master branch of Agda (to have the `variable` keyword,
`Prop` and all sorts of fancy stuff).

Metatheory
----------

We are using standard Agda with the sort `Prop` of strict propositions
(see https://hal.inria.fr/hal-01859964v2/document) and sized types.
The other axioms that we are using are:
- dependent function extensionality (three axioms, for the cases when the domain is a set, a
  proposition, or implicit)
- propositional extensionality, phrased with `Prop`
- existence of quotients for `Prop`-valued equivalence relations
The flag `--prop` enables `Prop`, the flag `--rewriting` is used for adding definitional reduction
rules for the quotients. Almost everything compiles with `--without-K` as well, except for the
`PathOver-refl-from` lemma, but it’s not yet clear to me whether it actually requires K.

Files
-----

- `common.agda`: very basic definitions used everywhere
- `quotients.agda`: quotients (postulated)
- `syntx.agda`: raw syntax of the type theory
- `rules.agda`: typing rules and admissible rules
- `contextualcat.agda`: the models of the type theory and morphisms between them
- `termmodel.agda`: the term model
- `partialinterpretation.agda`: the partial interpretation function
- `totality.agda`: totality of the partial interpretation function
- `initiality.agda`: initiality of the term model