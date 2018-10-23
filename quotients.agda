{-# OPTIONS --irrelevant-projections --rewriting #-}

open import common

postulate
  _//_ : (A : Set) (R : A → A → Set) → Set

module _ {A : Set} {R : A → A → Set} where

  postulate
    proj : A → A // R
    eq : {a b : A} (r : R a b) → proj a ≡ proj b
    //-rec : (B : Set) (d : A → B) (eq* : (a b : A) (r : R a b) → d a ≡ d b) → A // R → B
    //-beta : {B : Set} {d : A → B} {eq* : (a b : A) (r : R a b) → d a ≡ d b} {a : A}
            → //-rec B d eq* (proj a) ≡ d a
    //-elimId : {B : Set} (f g : A // R → B) (d : (a : A) → f (proj a) ≡ g (proj a)) → (x : A // R) → f x ≡ g x

{-# REWRITE //-beta #-}
