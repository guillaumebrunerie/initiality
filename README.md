Introduction
------------

This project aims at giving a formalized proof in Agda of a version of the initiality conjecture. A
complete proof for a type theory with only Pi-types and a base dependent type is available at commit
[8e52bc0](https://github.com/guillaumebrunerie/initiality/tree/8e52bc0b50f3e572d4cd9911889f52ae4ae7d5c9). We
are now working on extending the type theory to a type theory with Pi-types, Sigma-types, natural
numbers, identity types, and an infinite hierarchy of universes.

It requires a quite recent version of the master branch of Agda (to have the `variable` keyword,
`Prop` and various issues fixed). For instance commit
[764038c](https://github.com/agda/agda/tree/764038cf20dae68b463801fd049113011b4ade03) from January
2019 should work.

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

We are using standard Agda with the sort `Prop` of strict propositions
(see https://hal.inria.fr/hal-01859964v2/document).
The other axioms that we are using are:
- dependent function extensionality (three axioms, for the cases when the domain is a type, a
  proposition, or implicit)
- propositional extensionality, phrased with `Prop`
- existence of quotients for `Prop`-valued equivalence relations, with definitional computation rules

Explanation of the flags
------------------------

* the flag `--prop` is required to enable `Prop`
* the flag `--rewriting` is required to have quotients that compute
* the flag `--without-K` is not required, but it’s nice to see that everything compiles with it
* the flag `-v tc.unquote:10` adds some debug output when running Agda from the command line, it can be used to see the full code of the functions defined by reflection
* the flag `--allow-unsolved-metas` is used only if some file is incomplete but we want to compile another file depending on it anyway. It should not be used in a finished proof!

Files
-----

- `common.agda`: basic definitions used in several places
- `typetheory.agda`: raw syntax of the type theory
- `reflection.agda`: some definitions for using reflection (used in `syntx.agda`)
- `syntx.agda`: properties of the raw syntax
- `rules.agda`: typing rules and admissible rules
- `contextualcat.agda`: the models of the type theory and morphisms between them
- `quotients.agda`: quotients (postulated)
- `termmodel.agda`: the term model
- `partialinterpretation.agda`: the partial interpretation function
- `totality.agda`: totality of the partial interpretation function
- `initiality.agda`: initiality of the term model
