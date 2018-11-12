{-# OPTIONS --rewriting --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Nat public renaming (Nat to ℕ) hiding (_==_)
open import Agda.Builtin.List public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Size public

{- Relevant equality (used only in a few places, where we need to transport along it) -}

data _≡R_ {l} {A : Set l} (a : A) : A → Set where
  reflR : a ≡R a

!R : {A : Set} {a a' : A} → a ≡R a' → a' ≡R a
!R reflR = reflR

apR : {A B : Set} (f : A → B) {a a' : A} → a ≡R a' → f a ≡R f a'
apR f reflR = reflR

{- Rewriting -}

abstract
  _↦_ : ∀ {l} {A : Set l} → A → A → Set
  a ↦ b = a ≡R b
{-# BUILTIN REWRITE _↦_ #-}

{- Prop things -}

infixr 42 _×_

record Σ (A : Prop) (B : A → Prop) : Prop where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

infixr 4 _,_

_×_ : (A B : Prop) → Prop
A × B = Σ A (λ _ → B)

record Unit : Prop where
  constructor tt

{- Prop-valued equality -}
infix 4 _≡_
data _≡_ {l} {A : Set l} (x : A) : A → Prop where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

ap : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
ap f refl = refl

_∙_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ∙ refl = refl

infixr 4 _∙_

! : {A : Set} {a b : A} → a ≡ b → b ≡ a
! refl = refl

{- Boxing -}

record Box {l} (P : Prop l) : Set l where
  constructor box
  field
    unbox : P
open Box public

-- -- Not used
-- data Squash {l} (A : Set l) : Prop l where
--   sq : A → Squash A

{- Finite sets -}

data Fin : ℕ → Set where
  last : {n : ℕ} → Fin (suc n)
  prev : {n : ℕ} → Fin n → Fin (suc n)

_-F_ : (n : ℕ) (k : Fin n) → ℕ
n -F last = n
suc n -F prev k = n -F k


{- Partiality monad -}

record Partial (A : Set) : Set₁ where
  field
    isDefined : Prop
    totalify : isDefined → A
open Partial public

return : {A : Set} → A → Partial A
isDefined (return x) = Unit
totalify (return x) tt = x

_>>=_ : {A B : Set} → Partial A → (A → Partial B) → Partial B
isDefined (a >>= f) = Σ (isDefined a) (λ x → isDefined (f (totalify a x)))
totalify (a >>= f) (a₀ , b₀) = totalify (f (totalify a a₀)) b₀

assume : (P : Prop) → Partial (Box P)
isDefined (assume P) = P
unbox (totalify (assume P) x) = x

{- Helper functions for proof irrelevance -}

ap-irr : {A C : Set} {B : A → Prop} (f : (a : A) (b : B a) → C) {a a' : A} (p : a ≡ a') {b : B a} {b' : B a'} → f a b ≡ f a' b'
ap-irr f refl = refl

ap-irr2 : {A D : Set} {B : A → Prop} {C : (a : A) (_ : B a) → Prop} (f : (a : A) (b : B a) (c : C a b) → D) {a a' : A} (p : a ≡ a') {b : B a} {b' : B a'} {c : C a b} {c' : C a' b'} → f a b c ≡ f a' b' c'
ap-irr2 f refl = refl

ap2-irr : {A C D : Set} {B : A → C → Prop} (f : (a : A) (c : C) (b : B a c) → D) {a a' : A} (p : a ≡ a') {c c' : C} (q : c ≡ c') {b : B a c} {b' : B a' c'} → f a c b ≡ f a' c' b'
ap2-irr f refl refl = refl

{- Generalized variables -}

variable
  {n n' m k l} : ℕ

{- Axioms that we use -}

-- Dependent function extensionality
postulate
  funext  : ∀ {l l'} {A : Set l}  {B : A → Set l'} {f g : (a : A) → B a} (h : (x : A) → f x ≡ g x) → f ≡ g

-- Function extensionality for function with domain Prop
postulate
  funextP : ∀ {l l'} {A : Prop l} {B : Set l'} {f g : A → B} (h : (x : A) → f x ≡ g x) → f ≡ g

-- Propositional extensionality, using Prop
postulate
  prop-ext : {A B : Prop} (f : A → B) (g : B → A) → A ≡ B
