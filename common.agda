{-# OPTIONS --rewriting --prop #-}

open import Agda.Primitive public
open import Agda.Builtin.Nat public renaming (Nat to ℕ) hiding (_==_; _<_)
open import Agda.Builtin.List public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Unit public

{- Rewriting -}

abstract
  _↦_ : ∀ {l} {A : Set l} → A → A → Set l
  a ↦ b = Id a b where
    data Id (a : _) : _ → Set _ where
      refl : Id a a
{-# BUILTIN REWRITE _↦_ #-}


{- Basic records -}

record Σ (A : Prop) (B : A → Prop) : Prop where
  no-eta-equality
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

record ΣS {l} {l'} (A : Set l) (B : A → Prop l') : Set (l ⊔ l') where
  constructor _,_
  field
    fst : A
    snd : B fst
open ΣS public

infixr 4 _,_

record _∧_ (A B : Prop) : Prop where
  constructor _,_
  field
    fst : A
    snd : B
open _∧_ public

infixr 42 _∧_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _∧_ public

infixr 42 _×_

record True : Prop where
  constructor tt


{- Prop-valued equality -}

data _≡_ {l} {A : Set l} (x : A) : A → Prop l where
  instance refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≡_


Σ= : ∀ {l} {l'} {A : Set l} {B : A → Prop l'} {a a' : A} {b : B a} {b' : B a'} → a ≡ a' → _≡_ {A = ΣS _ _} (a , b) (a' , b')
Σ= refl = refl

ap : ∀ {l l'} {A : Set l} {B : Set l'} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
ap f refl = refl

_∙_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ∙ refl = refl

infixr 4 _∙_

! : {A : Set} {a b : A} → a ≡ b → b ≡ a
! refl = refl

{- Lifting from Prop to Set -}

record Box {l} (P : Prop l) : Set l where
  constructor box
  field
    unbox : P
open Box public

{- Generalized variables -}

variable
  {n n' m k l} : ℕ

{- Finite sets

There are two different use cases for finite sets:
- to specify a certain variable in a context of length [n] ([n] many choices)
- to specify where we want to weaken a context of length [n] ([suc n] many choices)
Instead of using [Fin n] and [Fin (suc n)], we define two different datatypes so that we
don’t mix them up.
-}

data VarPos : ℕ → Set where
  last : VarPos (suc n)
  prev : VarPos n → VarPos (suc n)

-- Size of the context before (and excluding) that variable
_-VarPos'_ : (n : ℕ) → VarPos n → ℕ
(suc m) -VarPos' last = m
(suc m) -VarPos' prev k = m -VarPos' k

-- Size of the context before (and including) that variable
_-VarPos_ : (n : ℕ) → VarPos n → ℕ
n -VarPos k = suc (n -VarPos' k)


data WeakPos : ℕ → Set where
  last : WeakPos n
  prev : WeakPos n → WeakPos (suc n)

-- Size of the context before that position
_-WeakPos_ : (n : ℕ) → WeakPos n → ℕ
n -WeakPos last = n
suc n -WeakPos prev k = n -WeakPos k

data _≤WP_ : WeakPos n → WeakPos n → Prop where
  last≤ : {k : WeakPos n} → k ≤WP last
  prev≤ : {k k' : WeakPos n} → k ≤WP k' → prev k ≤WP prev k'

-- Every position of length [n] is a position of length [suc n]
injWeakPos : {n : ℕ} → WeakPos n → WeakPos (suc n)
injWeakPos last = last
injWeakPos (prev k) = prev (injWeakPos k)

-- Position of the new variable in the weakened context
WeakPosToVarPos : {n : ℕ} → WeakPos n → VarPos (suc n)
WeakPosToVarPos last = last
WeakPosToVarPos (prev k) = prev (WeakPosToVarPos k)

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
  isDefined (return {{ PartialityMonad }} x) = True
  return {{ PartialityMonad }} x Partial.$ tt = x
  isDefined (_>>=_ {{ PartialityMonad }} a f) = Σ (isDefined a) (λ x → isDefined (f (a $ x)))
  _>>=_ {{ PartialityMonad }} a f Partial.$ x = f (a $ fst x) $ snd x

assume : (P : Prop) → Partial (Box P)
isDefined (assume P) = P
unbox (assume P Partial.$ x) = x


{- Helper functions for proof irrelevance -}

ap-irr : {A C : Set} {B : A → Prop} (f : (a : A) (b : B a) → C) {a a' : A} (p : a ≡ a') {b : B a} {b' : B a'} → f a b ≡ f a' b'
ap-irr f refl = refl

ap-irr2 : {A D : Set} {B : A → Prop} {C : (a : A) (_ : B a) → Prop} (f : (a : A) (b : B a) (c : C a b) → D) {a a' : A} (p : a ≡ a') {b : B a} {b' : B a'} {c : C a b} {c' : C a' b'} → f a b c ≡ f a' b' c'
ap-irr2 f refl = refl

ap2-irr : {A C D : Set} {B : A → C → Prop} (f : (a : A) (c : C) (b : B a c) → D) {a a' : A} (p : a ≡ a') {c c' : C} (q : c ≡ c') {b : B a c} {b' : B a' c'} → f a c b ≡ f a' c' b'
ap2-irr f refl refl = refl

ap3-irr2 : {A B C D : Set} {E : A → B → C → Prop} {F : A → B → C → Prop} (h : (a : A) (b : B) {c : C} (p : E a b c) (q : F a b c) → D) {a a' : A} (p : a ≡ a') {b b' : B} (q : b ≡ b') {c c' : C} (r : c ≡ c') {e : E a b c} {e' : E a' b' c'} {f : F a b c} {f' : F a' b' c'} → h a b {c = c} e f ≡ h a' b' {c = c'} e' f'
ap3-irr2 h refl refl refl = refl
  

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
