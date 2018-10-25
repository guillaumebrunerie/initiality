{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat public renaming (Nat to ℕ) hiding (_==_)
open import Agda.Builtin.Unit public renaming (⊤ to Unit)
open import Agda.Builtin.Sigma public
open import Agda.Builtin.List public
open import Agda.Builtin.Bool public

{-# BUILTIN REWRITE _≡_ #-}

infixr 42 _×_

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

{- Irrelevant Σ-types -}

record Σ' (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst' : A
    .snd' : B fst'
open Σ' public

infixr 42 _×'_

_×'_ : (A B : Set) → Set
A ×' B = Σ' A (λ _ → B)

{- Operations on equality proofs -}

! : {A : Set} {a b : A} → a ≡ b → b ≡ a
! refl = refl

_∙_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ∙ refl = refl

ap : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
ap f refl = refl

{- Finite sets -}

data Fin : ℕ → Set where
  last : {n : ℕ} → Fin (suc n)
  prev : {n : ℕ} → Fin n → Fin (suc n)

_-F_ : (n : ℕ) (k : Fin n) → ℕ
n -F last = n
suc n -F prev k = n -F k

{- Partiality monad -}

record Partial (A : Set) : Set₁ where
  constructor makePartial
  field
    prop : Set
--    prop-is-prop : (a b : prop) → a ≡ b
    inj : prop → A
open Partial

return : {A : Set} → A → Partial A
return x = makePartial Unit {-(λ _ _ → refl)-} (λ _ → x)

_>>=_ : {A B : Set} → Partial A → (A → Partial B) → Partial B
prop (a >>= f) = Σ (prop a) (λ x → prop (f (inj a x)))
--prop-is-prop (a >>= f) (a₀ , b₀) (a₁ , b₁) = {!!}
inj (a >>= f) (a₀ , b₀) = inj (f (inj a a₀)) b₀

assume : (P : Set) → Partial P
assume p = makePartial p (λ x → x)

{- Helper functions for irrelevance -}

ap-irr : {A C : Set} {B : A → Set} (f : (a : A) .(b : B a) → C) {a a' : A} (p : a ≡ a') .{b : B a} .{b' : B a'} → f a b ≡ f a' b'
ap-irr f refl = refl

ap-irr2 : {A D : Set} {B : A → Set} {C : (a : A) .(_ : B a) → Set} (f : (a : A) .(b : B a) .(c : C a b) → D) {a a' : A} (p : a ≡ a') .{b : B a} .{b' : B a'} .{c : C a b} .{c' : C a' b'} → f a b c ≡ f a' b' c'
ap-irr2 f refl = refl

ap2-irr : {A C D : Set} {B : A → C → Set} (f : (a : A) (c : C) .(b : B a c) → D) {a a' : A} (p : a ≡ a') {c c' : C} (q : c ≡ c') {b : B a c} {b' : B a' c'} → f a c b ≡ f a' c' b'
ap2-irr f refl refl = refl

{- Generalized variables -}

variable
  {n n' m k l} : ℕ
