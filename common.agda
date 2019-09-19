{-# OPTIONS --rewriting --prop --without-K #-}

open import Agda.Primitive public
open import Agda.Builtin.Nat public renaming (Nat to ℕ) hiding (_==_; _<_)
open import Agda.Builtin.List public
open import Agda.Builtin.Bool public

{- Relevant equality (used only in a few places, when we need to transport along it) -}

data _≡R_ {l} {A : Set l} (a : A) : A → Set l where
  reflR : a ≡R a


_R∙_ : ∀ {l} {A : Set l} {a b c : A} →  a ≡R b → b ≡R c → a ≡R c
_R∙_ reflR reflR = reflR

infixr 4 _R∙_

!R : {A : Set} {a a' : A} → a ≡R a' → a' ≡R a
!R reflR = reflR

apR : ∀ {l l'} {A : Set l} {B : Set l'} (f : A → B) {a a' : A} → a ≡R a' → f a ≡R f a'
apR f reflR = reflR


transportR : {B : ℕ → Set} {n n' : ℕ} (b : B n) → n ≡R n' → B n'
transportR b reflR = b

transportR-apR : {B : ℕ → Set} {n n' : ℕ} (b : B (suc n)) → (p : n ≡R n') → transportR {B = B} b (apR suc p) ≡R transportR b p 
transportR-apR b reflR = reflR



{- Rewriting -}

abstract
  _↦_ : ∀ {l} {A : Set l} → A → A → Set l
  a ↦ b = a ≡R b
{-# BUILTIN REWRITE _↦_ #-}


{- Constructions for Prop -}

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

record ΣSS {l} {l'} (A : Set l) (B : A → Set l') : Set (l ⊔ l') where
  constructor _,_
  field
    fst : A
    snd : B fst
open ΣSS public

infixr 4 _,_


_×_ : (A B : Prop) → Prop
A × B = Σ A (λ _ → B)

infixr 42 _×_

record Unit : Prop where
  constructor tt


data UnitR : Set where
  starU : UnitR

UnitR-contr : (a : UnitR) → starU ≡R a
UnitR-contr starU = reflR

data EmptyR : Set where
  

characΣSS= : {B : ℕ → Set} {n n' : ℕ} {b : B n} {b' : B n'} → ΣSS._,_ {B = B} n b ≡R (n' , b') → ΣSS (n ≡R n') (λ p → transportR {B = B} b p ≡R b')
characΣSS= reflR = (reflR , reflR)


ΣSS= : {B : ℕ → Set} {n : ℕ} {b : B n} {b' : B n} → b ≡R b' →  ΣSS._,_ {B = B} n b ≡R (n , b')
ΣSS= reflR = reflR



{- Prop-valued equality -}

data _≡_ {l} {A : Set l} (x : A) : A → Prop l where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≡_


Σ= : ∀ {l} {l'} {A : Set l} {B : A → Prop l'} {a a' : A} {b : B a} {b' : B a'} → a ≡R a' → (a ΣS., b) ≡R (a' , b')
Σ= reflR = reflR

ap : {A B : Set} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
ap f refl = refl

{-
--hack
postulate
  ‗ : {P : Prop} → P

𝄪 : {P : Prop} → P → P
𝄪 p = ‗

conc : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
conc refl refl = refl

_∙_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
p ∙ q = 𝄪 (conc p q)
-}

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

{- General remarks about the use of Fin
There are two different use cases for finite numbers:
- to specify a certain variable of a context
- to specify a spot where we want to weaken in a context
Assuming the context is of length [n], in the first case we will use [Fin n]
(as there are n possible variables), but in the second case we will use
[Fin (suc n)] (as there are n+1 possible places where we could weaken)
In the second case we use [n -F' k] to compute the length of the prefix
before the spot where we want to weaken, and in the first case we use [n -F k]
to compute the length of the prefix including the variable.
Given a variable at [k], then [prev k] is the spot weakening before that variable.
-}


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


{- Generalized variables -}

variable
  {n n' m k l} : ℕ

{- Well-founded induction on ℕ and connection to Fin -}

data _<_ : ℕ → ℕ → Prop where
 <-refl : n < suc n
 <-suc : n < m → n < suc m



data Acc (n : ℕ) : Prop where
  acc : ({k : ℕ} → (k < n) → Acc k) → Acc n


suc-ref-< : suc k < suc n → k < n
suc-ref-< {k} {suc k} <-refl = <-refl
suc-ref-< {k} {zero} (<-suc ())
suc-ref-< {k} {suc n} (<-suc le) = <-suc (suc-ref-< le)

suc-pres-< : k < n → suc k < suc n
suc-pres-< {k} {suc k} <-refl = <-refl
suc-pres-< {k} {suc n} (<-suc le) = <-suc (suc-pres-< le)


<-= : k < m → m ≡R n → k < n
<-= le reflR = le


<-+ : (m : ℕ) → m + n ≡ k → n < suc k
<-+ zero refl = <-refl
<-+ (suc m) refl = <-suc (<-+ m refl)

<-pos : (n m : ℕ) → 0 < m → n < (m + n)
<-pos n zero ()
<-pos n (suc m) e = <-+ m refl

suc-pos : (n : ℕ) → 0 < suc n
suc-pos zero = <-refl
suc-pos (suc n) = <-suc (suc-pos n)

Bounded-Fin : (k : ΣS ℕ (λ k → k < n)) → Fin n
Bounded-Fin {n = zero} (k , ())
Bounded-Fin {suc n} (zero , le) = last
Bounded-Fin {suc n} (suc k , le) = prev (Bounded-Fin (k , suc-ref-< le)) 

Fin-Bounded : Fin n → ΣS ℕ (λ k → k < n)
Fin-Bounded last = 0 , suc-pos _
Fin-Bounded (prev k) = (suc (fst (Fin-Bounded k)) , suc-pres-< (snd (Fin-Bounded k)))


lastsig : ΣS ℕ (λ k → k < suc n)
lastsig = (zero , suc-pos _)

prevsig : (k : ΣS ℕ (λ k → k < n)) → ΣS ℕ (λ k → k < suc n)
prevsig (n , le) = (suc n , suc-pres-< le)


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


{- Some results about natural numbers using ≡R -}

n+0 : (n : ℕ) → n ≡R (n + zero)
n+0 0 = reflR
n+0 (suc n) = apR suc (n+0 n)

n+suc : (n m : ℕ) → suc (n + m) ≡R (n + suc m)
n+suc 0 m = reflR
n+suc (suc n) m = apR suc (n+suc n m)

+-commR : (n m : ℕ) → (n + m) ≡R (m + n)
+-commR zero m = n+0 m
+-commR (suc n) m = apR suc (+-commR n m) R∙ n+suc m n

suc-inj : _≡R_ {A = ℕ} (suc m) (suc n) → m ≡R n
suc-inj reflR = reflR

suc^ : (m : ℕ) → ℕ → ℕ
suc^ zero n = n
suc^ (suc m) n = suc (suc^ m n)

suc^+ : suc^ m (suc n) ≡R suc (n + m)
suc^+ {zero} {n} = apR suc (n+0 n)
suc^+ {suc m} {n} = apR suc (suc^+ R∙ n+suc _ _)

suc^-pres-< : k < n → suc^ m k < suc^ m n
suc^-pres-< {k} {n} {zero} le = le
suc^-pres-< {k} {n} {suc m} le = suc-pres-< (suc^-pres-< le)

prev^sig : (m : ℕ) → (k : ΣS ℕ (λ k → k < suc n)) → ΣS ℕ (λ k → k < suc (n + m))
prev^sig {n = n} m (k , le) = (suc^ m k , <-= (suc^-pres-< le) suc^+)

-- standaard code-decode proof that nat is a set
code : ℕ → ℕ → Set
code zero zero = UnitR
code zero (suc n) = EmptyR
code (suc m) zero = EmptyR
code (suc m) (suc n) = code m n

code-is-prop : (m n : ℕ) → (p q : code m n) → p ≡R q
code-is-prop zero zero starU starU = reflR
code-is-prop zero (suc n) () ()
code-is-prop (suc m) zero () ()
code-is-prop (suc m) (suc n) p q = code-is-prop m n p q

r : (n : ℕ) → code n n
r zero = starU
r (suc n) = r n

encode : (m n : ℕ) → m ≡R n → code m n
encode m n p = transportR {B = code m} (r m) p

decode : (m n : ℕ) → code m n → m ≡R n
decode zero zero c = reflR
decode zero (suc n) ()
decode (suc m) zero () 
decode (suc m) (suc n) c = apR suc (decode m n c)

decode-encode : (m n : ℕ) → (p : m ≡R n) → decode m n (encode m n p) ≡R p
decode-encode zero zero reflR = reflR
decode-encode (suc m) (suc m) reflR = apR (apR suc) (decode-encode m m reflR)

encode-decode : (m n : ℕ) → (c : code m n) → encode m n (decode m n c) ≡R c
encode-decode zero zero c = UnitR-contr c
encode-decode zero (suc n) () 
encode-decode (suc m) zero ()
encode-decode (suc m) (suc n) c = transportR-apR (r m) (decode m n c) R∙ encode-decode m n c

nat-is-set : (m n : ℕ) → (p q : m ≡R n) → p ≡R q
nat-is-set m n p q = !R (decode-encode m n p) R∙ apR (decode m n) (code-is-prop m n (encode m n p) (encode m n q)) R∙ decode-encode m n q

axiomK-nat : (n : ℕ) (p : n ≡R n) → p ≡R reflR
axiomK-nat n p = nat-is-set n n p reflR

--This allows one to proof the following about sigma types where the first component is n:ℕ
sndΣSSℕR : {B : ℕ → Set } {n : ℕ} {b b' : B n} → ΣSS._,_ {B = B} n b ≡R (n , b') → b ≡R b'
sndΣSSℕR {B = B} {n} {b} {b'} p = apR (transportR {B = B} b) (!R (axiomK-nat n (fst (characΣSS= p)))) R∙ (snd (characΣSS= p)) 
