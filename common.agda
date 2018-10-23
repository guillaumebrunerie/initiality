{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat public renaming (Nat to ℕ) hiding (_==_)
open import Agda.Builtin.Unit public renaming (⊤ to Unit)
open import Agda.Builtin.Sigma public
open import Agda.Builtin.List public
open import Agda.Builtin.Bool public

{-# BUILTIN REWRITE _≡_ #-}

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

len : {A : Set} → List A → ℕ
len [] = zero
len (_ ∷ l) = suc (len l)

_&&_ : Bool → Bool → Bool
true && x = x
false && x = false

if_then_else_ : {A : Set} → Bool → A → A → A
if true then t else e = t
if false then t else e = e

! : {A : Set} {a b : A} → a ≡ b → b ≡ a
! refl = refl

_∙_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ∙ refl = refl

ap : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
ap f refl = refl

data Empty : Set where

data Fin : ℕ → Set where
  last : {n : ℕ} → Fin (suc n)
  prev : {n : ℕ} → Fin n → Fin (suc n)
