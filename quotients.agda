{-# OPTIONS --irrelevant-projections --type-in-type --rewriting #-}

open import common

is-prop : (A : Set) → Set
is-prop A = (a a' : A) → a ≡ a'

postulate
  #TODO# : {A : Set} → A

postulate
  prop-ext : {A B : Set} .(_ : is-prop A) .(_ : is-prop B) .(f : A → B) .(g : B → A) → A ≡ B

record EquivRel (A : Set) : Set₁ where
  field
    _≃_ : A → A → Set
    ._≃-is-prop_ : (a b : A) → is-prop (a ≃ b)
    .ref : (a : A) → a ≃ a
    .sym : {a b : A} → a ≃ b → b ≃ a
    .tra : {a b c : A} → a ≃ b → b ≃ c → a ≃ c

postulate
  _//_ : (A : Set) (R : EquivRel A) → Set

module _ {A : Set} {R : EquivRel A} where
  open EquivRel R

  postulate
    proj : A → A // R
    eq : {a b : A} (r : a ≃ b) → proj a ≡ proj b
    //-rec : (B : Set) (d : A → B) (eq* : (a b : A) (r : a ≃ b) → d a ≡ d b) → A // R → B
    //-beta : {B : Set} {d : A → B} {eq* : (a b : A) (r : a ≃ b) → d a ≡ d b} {a : A}
            → //-rec B d eq* (proj a) ≡ d a
    //-elimId : {B : Set} (f g : A // R → B) (d : (a : A) → f (proj a) ≡ g (proj a)) → (x : A // R) → f x ≡ g x

{-# REWRITE //-beta #-}

module _ {A : Set} {R : EquivRel A} where
  open EquivRel R

  _≃'_ : (a : A) (c : A // R) → Set
  _≃'_ a = //-rec _ (λ b → a ≃ b) (λ b c r → prop-ext (a ≃-is-prop b) (a ≃-is-prop c) (λ z → tra z r) λ z → tra z (sym r))

  .reflect' : {a : A} (c : A // R) → proj a ≡ c → a ≃' c
  reflect' {a} c refl = ref a

  .reflect : {a b : A} → proj a ≡ proj b → a ≃ b
  reflect {b = b} p = reflect' (proj b) p
