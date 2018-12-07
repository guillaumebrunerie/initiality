{-# OPTIONS --rewriting --prop --without-K #-}

open import Agda.Primitive public
open import Agda.Builtin.Nat public renaming (Nat to ℕ) hiding (_==_; _<_)
open import Agda.Builtin.List public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Size public

{- Relevant equality (used only in a few places, when we need to transport along it) -}

data _≡R_ {l} {A : Set l} (a : A) : A → Set l where
  reflR : a ≡R a

!R : {A : Set} {a a' : A} → a ≡R a' → a' ≡R a
!R reflR = reflR

apR : {A B : Set} (f : A → B) {a a' : A} → a ≡R a' → f a ≡R f a'
apR f reflR = reflR


{- Rewriting -}

abstract
  _↦_ : ∀ {l} {A : Set l} → A → A → Set l
  a ↦ b = a ≡R b
{-# BUILTIN REWRITE _↦_ #-}


{- Constructions for Prop -}

record Σ (A : Prop) (B : A → Prop) : Prop where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

infixr 4 _,_

_×_ : (A B : Prop) → Prop
A × B = Σ A (λ _ → B)

infixr 42 _×_

record Unit : Prop where
  constructor tt


{- Prop-valued equality -}

data _≡_ {l} {A : Set l} (x : A) : A → Prop l where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≡_

ap : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
ap f refl = refl

_∙_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ∙ refl = refl

infixr 4 _∙_

! : {A : Set} {a b : A} → a ≡ b → b ≡ a
! refl = refl

squash≡ : {A : Set} {a b : A} → a ≡R b → a ≡ b
squash≡ reflR = refl

{- Lifting from Prop to Set -}

record Box {l} (P : Prop l) : Set l where
  constructor box
  field
    unbox : P
open Box public


{- Finite sets -}

data Fin : ℕ → Set where
  last : {n : ℕ} → Fin (suc n)
  prev : {n : ℕ} → Fin n → Fin (suc n)

_-F'_ : (n : ℕ) (k : Fin (suc n)) → ℕ
n -F' last = n
suc n -F' prev k = n -F' k

_-F_ : (n : ℕ) (k : Fin n) → ℕ
n -F k = suc (n -F' prev k)

{- Monads -}

record Monad {ℓ ℓ'} (M : Set ℓ → Set ℓ') : Set (lsuc ℓ ⊔ ℓ') where
  field
    return : {A : Set ℓ} → A → M A
    _>>=_ : {A B : Set ℓ} → M A → (A → M B) → M B

  _>>_ : {A B : Set ℓ} → M A → M B → M B
  a >> b = a >>= (λ _ → b)

open Monad {{…}} public

{- The partiality monad -}

record Partial (A : Set) : Set₁ where
  field
    isDefined : Prop
    _$_ : isDefined → A
  infix 5 _$_
open Partial public

instance
  PartialityMonad : Monad Partial
  isDefined (return {{ PartialityMonad }} x) = Unit
  _$_ (return {{ PartialityMonad }} x) tt = x
  isDefined (_>>=_ {{ PartialityMonad }} a f) = Σ (isDefined a) (λ x → isDefined (f (a $ x)))
  _$_ (_>>=_ {{ PartialityMonad }} a f) x = f (a $ fst x) $ snd x

assume : (P : Prop) → Partial (Box P)
isDefined (assume P) = P
unbox (_$_ (assume P) x) = x


{- Helper functions for proof irrelevance -}

ap-irr : {A C : Set} {B : A → Prop} (f : (a : A) (b : B a) → C) {a a' : A} (p : a ≡ a') {b : B a} {b' : B a'} → f a b ≡ f a' b'
ap-irr f refl = refl

ap-irr2 : {A D : Set} {B : A → Prop} {C : (a : A) (_ : B a) → Prop} (f : (a : A) (b : B a) (c : C a b) → D) {a a' : A} (p : a ≡ a') {b : B a} {b' : B a'} {c : C a b} {c' : C a' b'} → f a b c ≡ f a' b' c'
ap-irr2 f refl = refl

ap2-irr : {A C D : Set} {B : A → C → Prop} (f : (a : A) (c : C) (b : B a c) → D) {a a' : A} (p : a ≡ a') {c c' : C} (q : c ≡ c') {b : B a c} {b' : B a' c'} → f a c b ≡ f a' c' b'
ap2-irr f refl refl = refl

{- Axioms -}

postulate
  -- Dependent function extensionality
  funext  : ∀ {l l'} {A : Set l}  {B : A → Set l'} {f g : (a : A) → B a} (h : (x : A) → f x ≡ g x) → f ≡ g

  -- Dependent function extensionality for function with domain Prop, does not seem to follow from [funext]
  funextP : ∀ {l l'} {A : Prop l} {B : A → Set l'} {f g : (a : A) → B a} (h : (x : A) → f x ≡ g x) → f ≡ g

  -- Dependent function extensionality for implicit function spaces
  funextI : ∀ {l l'} {A : Set l} {B : A → Set l'} {f g : {a : A} → B a} (h : (x : A) → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})

  -- Propositional extensionality
  prop-ext : {A B : Prop} (f : A → B) (g : B → A) → A ≡ B


{- Generalized variables -}

variable
  {n n' m k l} : ℕ

{- Well-founded induction on ℕ -}

data _<_ : ℕ → ℕ → Prop where
 <-refl : n < suc n
 <-suc : n < m → n < suc m

data Acc (n : ℕ) : Prop where
  acc : ({k : ℕ} → (k < n) → Acc k) → Acc n

<-+ : (m : ℕ) → m + n ≡ k → n < suc k
<-+ zero refl = <-refl
<-+ (suc m) refl = <-suc (<-+ m refl)

<-pos : (n m : ℕ) → 0 < m → n < (m + n)
<-pos n zero ()
<-pos n (suc m) e = <-+ m refl

suc-pos : (n : ℕ) → 0 < suc n
suc-pos zero = <-refl
suc-pos (suc n) = <-suc (suc-pos n)

WO-Nat : (n : ℕ) → Acc n
WO-lemma : (n k : ℕ) → (k < n) → Acc k

WO-Nat n = acc (λ e → WO-lemma n _ e)

WO-lemma zero k ()
WO-lemma (suc n) .n <-refl = WO-Nat n
WO-lemma (suc n) k (<-suc e) = WO-lemma n k e

{- Lemmas about addition -}

+-zero : (n : ℕ) → n ≡ n + zero
+-zero zero = refl
+-zero (suc n) = ap suc (+-zero n)

+-suc : (n m : ℕ) → suc (n + m) ≡ n + suc m
+-suc zero m = refl
+-suc (suc n) m = ap suc (+-suc n m)

+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm zero m = +-zero m
+-comm (suc n) m = ap suc (+-comm n m) ∙ +-suc m n

+-assoc : (n m k : ℕ) → n + m + k ≡ n + (m + k)
+-assoc zero m k = refl
+-assoc (suc n) m k = ap suc (+-assoc n m k)

{- Equational reasoning -}

infix  2 _∎
infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p1 ⟩ p2 = p1 ∙ p2

_∎ : ∀ {i} {A : Set i} (x : A) → x ≡ x
_∎ _ = refl
