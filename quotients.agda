{-# OPTIONS --irrelevant-projections --type-in-type --rewriting #-}

open import common

{- Equivalence relations -}

is-prop : (A : Set) → Set
is-prop A = (a a' : A) → a ≡ a'

record EquivRel (A : Set) : Set₁ where
  field
    _≃_ : A → A → Set
    ._≃-is-prop_ : (a b : A) → is-prop (a ≃ b)
    .ref : (a : A) → a ≃ a
    .sym : {a b : A} → a ≃ b → b ≃ a
    .tra : {a b c : A} → a ≃ b → b ≃ c → a ≃ c

{- Quotients -}

postulate
  _//_ : (A : Set) (R : EquivRel A) → Set

module _ {A : Set} {R : EquivRel A} where
  open EquivRel R

  postulate
    {- Introduction rules -}

    proj : A → A // R
    eq : {a b : A} (r : a ≃ b) → proj a ≡ proj b

    {- Elimination rules -}

    //-rec : (B : Set) (d : A → B) (eq* : (a b : A) (r : a ≃ b) → d a ≡ d b) → A // R → B
    //-elimId : {B : Set} (f g : A // R → B) (d : (a : A) → f (proj a) ≡ g (proj a)) → (x : A // R) → f x ≡ g x

    -- This is wrong!
    //-elimPiId : {B : Set} {f g : A // R → B} {C : (x : A // R) → .(_ : f x ≡ g x) → Set}
                → ((a : A) → (.(p : f (proj a) ≡ g (proj a)) → C (proj a) p))
                → ((x : A // R) → (.(p : f x ≡ g x) → C x p))

    -- This is wrong!
    //-elimPiIdR : {B : Set} {f g : A // R → B} {C : (x : A // R) → (_ : f x ≡ g x) → Set}
                → ((a : A) → ((p : f (proj a) ≡ g (proj a)) → C (proj a) p))
                → ((x : A // R) → ((p : f x ≡ g x) → C x p))

    {- Reduction rules -}

    //-beta : {B : Set} {d : A → B} {eq* : (a b : A) (r : a ≃ b) → d a ≡ d b} {a : A}
            → //-rec B d eq* (proj a) ≡ d a

    //-elimPiIdBeta : {B C : Set} {f g : A // R → B}
                → {h : (a : A) → (.(_ : f (proj a) ≡ g (proj a)) → C)}
                → {a : A} {p : f (proj a) ≡ g (proj a)} → //-elimPiId {f = f} {g = g} h (proj a) p ≡ h a p

{-# REWRITE //-beta #-}
{-# REWRITE //-elimPiIdBeta #-}

{- Other helper functions (iterated elimination principles) -}

module _ {A A' : Set} {R : EquivRel A} {R' : EquivRel A'}
         {B : Set} {f g : A // R → A' // R' → B}
         {P : (x : A // R) (y : A' // R') (p : f x y ≡ g x y) → Set}
         (d : (a : A) (a' : A') (p : f (proj a) (proj a') ≡ g (proj a) (proj a')) → P (proj a) (proj a') p) where

  //-elimPiIdR2 : (x : A // R) (y : A' // R') (p : f x y ≡ g x y) → P x y p
  //-elimPiIdR2 x = //-elimPiIdR (λ a' → aux a' x) where

    aux : (a' : A') (x : A // R) (p : f x (proj a') ≡ g x (proj a')) → P x (proj a') p
    aux a' = //-elimPiIdR (λ a → d a a')

module _ {A A' : Set} {R : EquivRel A} {R' : EquivRel A'}
         {B : Set} {f g : A // R → A' // R' → B}
         {P : (x : A // R) (y : A' // R') .(p : f x y ≡ g x y) → Set}
         (d : (a : A) (a' : A') .(p : f (proj a) (proj a') ≡ g (proj a) (proj a')) → P (proj a) (proj a') p) where

  //-elimPiId2 : (x : A // R) (y : A' // R') .(p : f x y ≡ g x y) → P x y p
  //-elimPiId2 x = //-elimPiId (λ a' → aux a' x) where

    aux : (a' : A') (x : A // R) .(p : f x (proj a') ≡ g x (proj a')) → P x (proj a') p
    aux a' = //-elimPiId (λ a → d a a')

module _ {A A' A'' : Set} {R : EquivRel A} {R' : EquivRel A'} {R'' : EquivRel A''}
         {B : Set} {f g : A // R → A' // R' → A'' // R'' → B}
         {P : (x : A // R) (y : A' // R') (z : A'' // R'') .(p : f x y z ≡ g x y z) → Set}
         (d : (a : A) (a' : A') (a'' : A'') .(p : f (proj a) (proj a') (proj a'') ≡ g (proj a) (proj a') (proj a'')) → P (proj a) (proj a') (proj a'') p) where

  //-elimPiId3 : (x : A // R) (y : A' // R') (z : A'' // R'') .(p : f x y z ≡ g x y z) → P x y z p
  //-elimPiId3 x y = //-elimPiId (λ a'' → aux a'' x y) where

    aux : (a'' : A'') (x : A // R) (y : A' // R') .(p : f x y (proj a'') ≡ g x y (proj a'')) → P x y (proj a'') p
    aux a'' = //-elimPiId2 (λ a a' → d a a' a'')

{- Effectiveness of quotients, using propositional extensionality -}

postulate
  prop-ext : {A B : Set} .(_ : is-prop A) .(_ : is-prop B) .(f : A → B) .(g : B → A) → A ≡ B

module _ {A : Set} {R : EquivRel A} where
  open EquivRel R

  _≃'_ : (a : A) (c : A // R) → Set
  _≃'_ a = //-rec _ (λ b → a ≃ b) (λ b c r → prop-ext (a ≃-is-prop b) (a ≃-is-prop c) (λ z → tra z r) λ z → tra z (sym r))

  .reflect' : {a : A} (c : A // R) → proj a ≡ c → a ≃' c
  reflect' {a} c refl = ref a

  .reflect : {a b : A} → proj a ≡ proj b → a ≃ b
  reflect {b = b} p = reflect' (proj b) p
