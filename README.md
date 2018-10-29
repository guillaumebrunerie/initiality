Introduction
------------

A formalized proof in Agda of a version of the initiality conjecture for a type theory with
Pi-types, a base type called U, and a dependent type called El. This is work in progress.

It requires a quite recent version of the master branch of Agda (to have the `variable` keyword,
`Prop` and all sorts of fancy stuff).

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
