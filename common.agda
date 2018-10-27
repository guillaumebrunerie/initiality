{-# OPTIONS --rewriting --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Equality public renaming (_≡_ to _≡R_; refl to reflR)
open import Agda.Builtin.Nat public renaming (Nat to ℕ) hiding (_==_)
open import Agda.Builtin.Sigma public
open import Agda.Builtin.List public
open import Agda.Builtin.Bool public

{-# BUILTIN REWRITE _≡R_ #-}

record Unit : Prop where
  constructor tt

infixr 42 _×_

record _×_ (A B : Prop) : Prop where
  constructor _,_
  field
    fst : A
    snd : B
open _×_ public

{- Irrelevant Σ-types -}

record Σ' (A : Set) (B : A → Prop) : Set where
  constructor _,_
  field
    fst' : A
    snd' : B fst'
open Σ' public

_×R_ : (A B : Set) → Set
A ×R B = Σ A (λ _ → B)

{- Operations on relevant equality proofs -}

!R : {A : Set} {a b : A} → a ≡R b → b ≡R a
!R reflR = reflR

_∙R_ : {A : Set} {a b c : A} → a ≡R b → b ≡R c → a ≡R c
reflR ∙R reflR = reflR

apR : {A B : Set} (f : A → B) {a b : A} → a ≡R b → f a ≡R f b
apR f reflR = reflR

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
    totalify : .isDefined → A
open Partial public

record UnitP : Prop where
  constructor tt

record ΣP (A : Prop) (B : A → Prop) : Prop where
  constructor _,_
  field
    fst : A
    snd : B fst
open ΣP public

{- Prop-valued equality -}
infix 4 _≡P_
data _≡P_ {l} {A : Set l} (x : A) : A → Prop where
  reflP : x ≡P x

record Setify {l} (P : Prop) : Set l where
  constructor makeSetify
  field
    getProp : P
open Setify public

pattern refl = makeSetify reflP

{- Set-valued, proof irrelevant equality -}
infix 4 _≡_

_≡_ : ∀ {l} {A : Set l} (x y : A) → Set l
x ≡ y = Setify (x ≡P y)

toS : {A : Set} {x y : A} → x ≡R y → x ≡ y
getProp (toS reflR) = reflP

ap : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
getProp (ap f refl) = reflP

_∙_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
getProp (refl ∙ refl) = reflP

! : {A : Set} {a b : A} → a ≡ b → b ≡ a
getProp (! refl) = reflP

_∙P_ : {A : Set} {a b c : A} → a ≡P b → b ≡P c → a ≡P c
reflP ∙P reflP = reflP

!P : {A : Set} {a b : A} → a ≡P b → b ≡P a
!P reflP = reflP

return : {A : Set} → A → Partial A
isDefined (return x) = UnitP
totalify (return x) tt = x

_>>=_ : {A B : Set} → Partial A → (A → Partial B) → Partial B
isDefined (a >>= f) = ΣP (isDefined a) (λ x → isDefined (f (totalify a x)))
totalify (a >>= f) (a₀ , b₀) = totalify (f (totalify a a₀)) b₀

toSetify : ∀ {l} {P : Prop} → .P → Setify {l} P
getProp (toSetify x) = x

assume : (P : Prop) → Partial (Setify {lzero} P)
isDefined (assume p) = p
totalify (assume p) = toSetify

{- Helper functions for irrelevance -}

.ap-irr : {A C : Set} {B : A → Set} (f : (a : A) .(b : B a) → C) {a a' : A} (p : a ≡ a') .{b : B a} .{b' : B a'} → f a b ≡ f a' b'
getProp (ap-irr f refl) = reflP

apP-irr : {A C : Set} {B : A → Prop} (f : (a : A) .(b : B a) → C) {a a' : A} (p : a ≡ a') .{b : B a} .{b' : B a'} → f a b ≡ f a' b'
getProp (apP-irr f refl) = reflP

apR-irr : {A C : Set} {B : A → Set} (f : (a : A) .(b : B a) → C) {a a' : A} (p : a ≡R a') .{b : B a} .{b' : B a'} → f a b ≡R f a' b'
apR-irr f reflR = reflR

.ap-irr2 : {A D : Set} {B : A → Set} {C : (a : A) .(_ : B a) → Set} (f : (a : A) .(b : B a) .(c : C a b) → D) {a a' : A} (p : a ≡ a') .{b : B a} .{b' : B a'} .{c : C a b} .{c' : C a' b'} → f a b c ≡ f a' b' c'
getProp (ap-irr2 f refl) = reflP

.apP-irr2 : {A D : Set} {B : A → Prop} {C : (a : A) .(_ : B a) → Prop} (f : (a : A) .(b : B a) .(c : C a b) → D) {a a' : A} (p : a ≡ a') .{b : B a} .{b' : B a'} .{c : C a b} .{c' : C a' b'} → f a b c ≡ f a' b' c'
getProp (apP-irr2 f refl) = reflP

.ap2-irr : {A C D : Set} {B : A → C → Set} (f : (a : A) (c : C) .(b : B a c) → D) {a a' : A} (p : a ≡ a') {c c' : C} (q : c ≡ c') {b : B a c} {b' : B a' c'} → f a c b ≡ f a' c' b'
getProp (ap2-irr f refl refl) = reflP

.apP2-irr : {A C D : Set} {B : A → C → Set} (f : (a : A) (c : C) .(b : B a c) → D) {a a' : A} (p : a ≡ a') {c c' : C} (q : c ≡ c') {b : B a c} {b' : B a' c'} → f a c b ≡P f a' c' b'
apP2-irr f refl refl = reflP

{- Generalized variables -}

variable
  {n n' m k l} : ℕ
