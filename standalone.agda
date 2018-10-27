{-# OPTIONS --irrelevant-projections --type-in-type --rewriting #-}

open import common
open import contextualcat
open import quotients

open CCat hiding (Mor)

{- Syntax of term- and type-expressions, using de Bruijn indices -}

data TyExpr : ℕ → Set
data TmExpr : ℕ → Set

data TyExpr where
  pi : (A : TyExpr n) (B : TyExpr (suc n)) → TyExpr n
  uu : TyExpr n
  el : (v : TmExpr n) → TyExpr n

data TmExpr where
  var : (v : Fin n) → TmExpr n
  lam : (A : TyExpr n) (B : TyExpr (suc n)) (u : TmExpr (suc n)) → TmExpr n
  app : (A : TyExpr n) (B : TyExpr (suc n)) (f : TmExpr n) (a : TmExpr n) → TmExpr n

{- Contexts and context morphisms -}

data Ctx : ℕ → Set where
  ◇ : Ctx 0
  _,_ : {n : ℕ} (Γ : Ctx n) → TyExpr n → Ctx (suc n)

data Mor (n : ℕ) : ℕ → Set where
  ◇ : Mor n 0
  _,_ : {m : ℕ} → Mor n m → TmExpr n → Mor n (suc m)

CtxExt : (n m : ℕ) → Set
CtxExt n 0 = Unit
CtxExt n (suc m) = Σ (TyExpr n) (λ A → CtxExt (suc n) m)

_++Ctx_ : {n m : ℕ} (Γ : Ctx n) → CtxExt n m → Ctx (n ++ℕ m)
_++Ctx_ {m = 0} Γ tt = Γ
_++Ctx_ {m = suc m} Γ (A , Δ) = (Γ , A) ++Ctx Δ

{- Weakening -}

weakenTy' : (l : ℕ) → TyExpr (l + n) → TyExpr (l + suc n)
weakenTm' : (l : ℕ) → TmExpr (l + n) → TmExpr (l + suc n)
weakenVar' : (l  : ℕ) → Fin (l + n) → Fin (l + suc n)

weakenTy' l (pi A B) = pi (weakenTy' l A) (weakenTy' (suc l) B)
weakenTy' l uu = uu
weakenTy' l (el v) = el (weakenTm' l v)

weakenTm' l (var x) = var (weakenVar' l x)
weakenTm' l (lam A B u) = lam (weakenTy' l A) (weakenTy' (suc l) B) (weakenTm' (suc l) u)
weakenTm' l (app A B f a) = app (weakenTy' l A) (weakenTy' (suc l) B) (weakenTm' l f) (weakenTm' l a)

weakenVar' 0 v = prev v
weakenVar' (suc l₁) last = last
weakenVar' (suc l₁) (prev v) = prev (weakenVar' l₁ v)

weakenTy : TyExpr n → TyExpr (suc n)
weakenTy = weakenTy' 0

weakenTm : TmExpr n → TmExpr (suc n)
weakenTm = weakenTm' 0

{- Substitution -}

substTy : TyExpr (suc m + n) → TmExpr n → TyExpr (m + n)
substTm : TmExpr (suc m + n) → TmExpr n → TmExpr (m + n)
substVar : Fin (suc m + n) → TmExpr n → TmExpr (m + n)

substTy (pi A B) u = pi (substTy A u) (substTy B u)
substTy uu u = uu
substTy (el v) u = el (substTm v u)

substTm (var x) u = substVar x u
substTm (lam A B v) u = lam (substTy A u) (substTy B u) (substTm v u)
substTm (app A B f a) u = app (substTy A u) (substTy B u) (substTm f u) (substTm a u)

substVar {m = zero}  last u = u
substVar {m = suc m} last u = var last
substVar {m = zero}  (prev x) u = var x
substVar {m = suc m} (prev x) u = weakenTm (substVar x u)

weakenMor : Mor n m → Mor (suc n) m
weakenMor ◇ = ◇
weakenMor (δ , u) = weakenMor δ , weakenTm u

{- Total substitutions -}

infix 42 _[_]Ty
infix 42 _[_]Tm

shiftMor : Mor n m → Mor (suc n) (suc m)
shiftMor δ = weakenMor δ , var last

_[_]Ty : {n m : ℕ} → TyExpr n → (δ : Mor m n) → TyExpr m
_[_]Tm : {n m : ℕ} → TmExpr n → (δ : Mor m n) → TmExpr m

pi A B [ δ ]Ty = pi (A [ δ ]Ty) (B [ (weakenMor δ , var last) ]Ty)
uu [ δ ]Ty = uu
el v [ δ ]Ty = el (v [ δ ]Tm)

var last [ (δ , u) ]Tm = u
var (prev x) [ (δ , u) ]Tm = var x [ δ ]Tm
lam A B u [ δ ]Tm = lam (A [ δ ]Ty) (B [ shiftMor δ ]Ty) (u [ shiftMor δ ]Tm)
app A B f a [ δ ]Tm = app (A [ δ ]Ty) (B [ shiftMor δ ]Ty) (f [ δ ]Tm) (a [ δ ]Tm)

_[_]Mor : {n m k : ℕ} → Mor n k → (δ : Mor m n) → Mor m k
◇ [ δ ]Mor = ◇
(γ , u) [ δ ]Mor = (γ [ δ ]Mor , u [ δ ]Tm)

{- The different forms of (pre)judgments. Maybe the judgments for contexts and context morphisms could be defined later. -}
data Judgment : Set where
  _⊢_ : (Γ : Ctx n) → TyExpr n → Judgment
  _⊢_:>_ : (Γ : Ctx n) → TmExpr n → TyExpr n → Judgment
  _⊢_==_ : (Γ : Ctx n) → TyExpr n → TyExpr n → Judgment
  _⊢_==_:>_ : (Γ : Ctx n) → TmExpr n → TmExpr n → TyExpr n → Judgment

{- Derivability of judgments, the typing rules of the type theory -}
data Derivable : Judgment → Set

⊢_ : Ctx n → Set
⊢ ◇ = Unit
⊢ (Γ , A) = (⊢ Γ) × Derivable (Γ ⊢ A)

⊢_==_ : Ctx n → Ctx n → Set
⊢ ◇ == ◇ = Unit
⊢ (Γ , A) == (Γ' , A') = (⊢ Γ == Γ') ×' Derivable (Γ ⊢ A == A')

_⊢_∷>_ : (Γ : Ctx n) → Mor n m → Ctx m → Set
Γ ⊢ ◇ ∷> ◇ = Unit
Γ ⊢ (δ , u) ∷> (Δ , A) = (Γ ⊢ δ ∷> Δ) × Derivable (Γ ⊢ u :> A [ δ ]Ty)

_⊢_==_∷>_ : (Γ : Ctx n) → Mor n m → Mor n m → Ctx m → Set
Γ ⊢ ◇ == ◇ ∷> ◇ = Unit
Γ ⊢ (δ , u) == (δ' , u') ∷> (Δ , A) = (Γ ⊢ δ == δ' ∷> Δ) × Derivable (Γ ⊢ u == u' :> A [ δ ]Ty)

data Derivable where

  -- Variable rule
  VarLast : {Γ : Ctx n} {A : TyExpr n}
          → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ var last :> weakenTy A)

  VarPrev : {Γ : Ctx n} {B : TyExpr n} {k : Fin n} {A : TyExpr n}
          → Derivable (Γ ⊢ var k :> A)
          → Derivable ((Γ , B) ⊢ var (prev k) :> weakenTy A)

  -- Congruence for variables
  VarLastCong : {Γ : Ctx n} {A : TyExpr n}
          → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ var last == var last :> weakenTy A)

  VarPrevCong : {Γ : Ctx n} {B : TyExpr n} {k k' : Fin n} {A : TyExpr n}
          → Derivable (Γ ⊢ var k == var k' :> A)
          → Derivable ((Γ , B) ⊢ var (prev k) == var (prev k') :> weakenTy A)

  -- Symmetry and transitivity for types
  TySymm : {Γ : Ctx n} {A B : TyExpr n}
         → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B == A)
  TyTran : {Γ : Ctx n} {A B C : TyExpr n}
         → Derivable (Γ ⊢ A == B)→ Derivable (Γ ⊢ B == C) → Derivable (Γ ⊢ A == C)

  -- Symmetry and transitivity for terms
  TmSymm : {Γ : Ctx n} {u v : TmExpr n} {A : TyExpr n}
         → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ v == u :> A)
  TmTran : {Γ : Ctx n} {u v w : TmExpr n} {A : TyExpr n}
         → Derivable (Γ ⊢ u == v :> A)→ Derivable (Γ ⊢ v == w :> A) → Derivable (Γ ⊢ u == w :> A)

  -- Conversion rule
  Conv : {Γ : Ctx n} {u : TmExpr n} {A B : TyExpr n}
       → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u :> B)
  ConvEq : {Γ : Ctx n} {u u' : TmExpr n} {A B : TyExpr n}
       → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u == u' :> B)

  -- Substitution rules
  SubstTy : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ A) → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty)
  SubstTm : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ u :> A) → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm :> A [ δ ]Ty)
  SubstTyEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ ]Ty)
  SubstTmEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u' [ δ ]Tm :> A [ δ ]Ty)
  SubstTySubstEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m}
       → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
  SubstTmSubstEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m}
       → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u' [ δ' ]Tm :> A [ δ' ]Ty)

  -- Rules for Pi
  Pi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)}
     → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ pi A B)
  PiCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)}
     → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ pi A B == pi A' B')

  -- Rules for lambda
  Lam : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)}
      → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ lam A B u :> pi A B)
  LamCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr (suc n)}
      → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable ((Γ , A) ⊢ u == u' :> B) → Derivable (Γ ⊢ lam A B u == lam A' B' u' :> pi A B)

  -- Rules for app
  App : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f a : TmExpr n}
      → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ f :> pi A B) → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ app A B f a :> substTy B a)
  AppCong : {n : ℕ} {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {f f' a a' : TmExpr n}
      → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ f == f' :> pi A B) → Derivable (Γ ⊢ a == a' :> A) → Derivable (Γ ⊢ app A B f a == app A' B' f' a' :> substTy B a)

  -- Beta-reduction
  Beta : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)} {a : TmExpr n}
       → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ a :> A)
       → Derivable (Γ ⊢ app A B (lam A B u) a == substTm u a :> substTy B a)

  -- Rules for UU
  UU : {Γ : Ctx n}
     → Derivable (Γ ⊢ uu)
  UUCong : {Γ : Ctx n}
     → Derivable (Γ ⊢ uu == uu)

  -- Rules for El
  El : {Γ : Ctx n} {v : TmExpr n}
     → Derivable (Γ ⊢ v :> uu) → Derivable (Γ ⊢ el v)
  ElCong : {Γ : Ctx n} {v v' : TmExpr n}
     → Derivable (Γ ⊢ v == v' :> uu) → Derivable (Γ ⊢ el v == el v')

TyRefl : {Γ : Ctx n} {A : TyExpr n} → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A)
TmRefl : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u == u :> A)

TyRefl (SubstTy dA dδ) = SubstTyEq (TyRefl dA) dδ
TyRefl (Pi dA dB) = PiCong (TyRefl dA) (TyRefl dB)
TyRefl UU = UUCong
TyRefl (El dv) = ElCong (TmRefl dv)

TmRefl (VarLast dA) = VarLastCong dA
TmRefl (VarPrev du) = VarPrevCong (TmRefl du)
TmRefl (Conv du dA=) = ConvEq (TmRefl du) dA=
TmRefl (SubstTm du dδ) = SubstTmEq (TmRefl du) dδ
TmRefl (Lam dA dB du) = LamCong (TyRefl dA) (TyRefl dB) (TmRefl du)
TmRefl (App dA dB df da) = AppCong (TyRefl dA) (TyRefl dB) (TmRefl df) (TmRefl da)

{-
ConvTyEq : {Γ Δ : Ctx n} {A B : TyExpr n} → Derivable (Γ ⊢ A == B) → (⊢ Γ == Δ) → Derivable (Δ ⊢ A == B)
ConvTyEq dA= dΓ= = {!!}

ConvMorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} → (Γ ⊢ δ == δ' ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ == δ' ∷> Δ')
ConvMorEq dδ= dΓ= dΔ= = {!!}
-}

CtxRefl : {Γ : Ctx n} → ⊢ Γ → ⊢ Γ == Γ
CtxRefl {Γ = ◇} tt = tt
CtxRefl {Γ = Γ , A} (dΓ , dA) = (CtxRefl dΓ , TyRefl dA)

{-
CtxSymm : {Γ Δ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Γ
CtxSymm {Γ = ◇} {Δ = ◇} tt = tt
CtxSymm {Γ = Γ , A} {Δ , B} (dΓ= , dA=) = (CtxSymm dΓ= , ConvTyEq (TySymm dA=) dΓ=)

CtxTran : {Γ Δ Θ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Θ → ⊢ Γ == Θ
CtxTran {Γ = ◇} {Δ = ◇} {Θ = ◇} tt tt = tt
CtxTran {Γ = Γ , A} {Δ , B} {Θ , C} (dΓ= , dA=) (dΔ= , dB=) = (CtxTran dΓ= dΔ= , TyTran dA= (ConvTyEq dB= (CtxSymm dΓ=)))
-}

MorRefl : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} → Γ ⊢ δ ∷> Δ → Γ ⊢ δ == δ ∷> Δ
MorRefl {Δ = ◇} {◇} tt = tt
MorRefl {Δ = Δ , B} {δ , u} (dδ , du) = (MorRefl dδ , TmRefl du)

MorSymm : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ ∷> Δ
MorSymm {Δ = ◇} {◇} {◇} _ tt = tt
MorSymm {Δ = Δ , B} {δ , u} {δ' , u'} (dΔ , dB) (dδ , du) = (MorSymm dΔ dδ) , (ConvEq (TmSymm du) (SubstTySubstEq (TyRefl dB) dδ))

MorTran : {Γ : Ctx n} {Δ : Ctx m} {δ δ' δ'' : Mor n m} → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ'' ∷> Δ → Γ ⊢ δ == δ'' ∷> Δ
MorTran {Δ = ◇} {◇} {◇} {◇} _ tt tt = tt
MorTran {Δ = Δ , B} {δ , u} {δ' , u'} {δ'' , u''} (dΔ , dB) (dδ , du) (dδ' , du') = (MorTran dΔ dδ dδ') , TmTran du (ConvEq du' (SubstTySubstEq (TyRefl dB) (MorSymm dΔ dδ)))

record DCtx (n : ℕ) : Set where
  constructor _,_
  field
    fst : Ctx n
    .snd : (⊢ fst)
open DCtx

DMor : ℕ → ℕ → Set
DMor n m = Σ (DCtx n × DCtx m) (λ {((Γ , _) , (Δ , _)) → Σ' (Mor n m) (λ δ → (Γ ⊢ δ ∷> Δ))})

transport : {A : Set} (B : A → Set) {a a' : A} (p : a ≡ a') → B a → B a'
transport B refl x = x

idMorGen : ∀ n m → Mor (n ++ℕ m) n
idMorGen 0 _ = ◇
idMorGen (suc n) m =
  idMorGen n (suc m) , var (last ++F m)

idMorAlt : ∀ n → Mor n n
idMorAlt n = idMorGen n 0

weakenTm* : ∀ k → TmExpr (n ++ℕ k) → TmExpr (suc n ++ℕ k)
weakenTm* 0 = weakenTm
weakenTm* (suc k) = weakenTm* k

weakenedVarGen : ∀ (k : Fin (suc n)) m
  → weakenTm* m (var (k ++F m)) ≡ var (k ++F suc m)
weakenedVarGen k 0 = refl
weakenedVarGen k (suc m) = weakenedVarGen (prev k) m

weakenMor* : ∀ k → Mor (n ++ℕ k) m → Mor (suc n ++ℕ k) m
weakenMor* k ◇ = ◇
weakenMor* k (δ , u) = weakenMor* k δ , weakenTm* k u

weakenMor*-0 : ∀ (δ : Mor n m)
  → weakenMor* {n = n} {m = m} 0 δ ≡ weakenMor {n = n} {m = m} δ
weakenMor*-0 ◇ = refl
weakenMor*-0 {m = suc m} (δ , u) rewrite weakenMor*-0 {m = m} δ = refl

weakenMor*-suc : ∀ k (δ : Mor (suc n ++ℕ k) m)
  → weakenMor* {n = n} {m = m} (suc k) δ ≡ weakenMor* {n = suc n} {m = m} k δ
weakenMor*-suc k ◇ = refl
weakenMor*-suc k (δ , u) rewrite weakenMor*-suc k δ = refl

weakenedIdMorGen : ∀ n m →
    weakenMor* {n = n} m (idMorGen n m)
  ≡ idMorGen n (suc m)
weakenedIdMorGen 0 m = refl
weakenedIdMorGen (suc n) m =
  ap (λ x → x , weakenTm* m (var (last ++F m)))
    (! (weakenMor*-suc m (idMorGen n (suc m))))
  ∙ (ap (λ x → x , weakenTm* m (var (last ++F m)))
    (weakenedIdMorGen n (suc m))
  ∙ (ap (λ x → idMorGen n (suc (suc m)) , x)
    (weakenedVarGen last m)))

shiftedIdMorAlt : ∀ n →
  shiftMor (idMorAlt n) ≡ idMorAlt (suc n)
shiftedIdMorAlt n =
  ap (λ x → x , var last)
    (! (weakenMor*-0 (idMorAlt n)))
  ∙ ap (λ x → x , var last)
    (weakenedIdMorGen n 0)

idMor : ∀ n → Mor n n
idMor 0 = ◇
idMor (suc n) = shiftMor (idMor n)

idMor≡idMorAlt : ∀ n → idMor n ≡ idMorAlt n
idMor≡idMorAlt 0 = refl
idMor≡idMorAlt (suc n) rewrite idMor≡idMorAlt n | shiftedIdMorAlt n = refl

_!_++Ty'_ : ∀ l₀ (A : TyExpr (l₀ + n)) m → TyExpr (l₀ + (n ++ℕ m))
l₀ ! A ++Ty' 0 = A
l₀ ! A ++Ty' suc m = l₀ ! weakenTy' l₀ A ++Ty' m

_!_++Tm'_ : ∀ l₀ (u : TmExpr (l₀ + n)) m → TmExpr (l₀ + (n ++ℕ m))
l₀ ! u ++Tm' 0 = u
l₀ ! u ++Tm' suc m = l₀ ! weakenTm' l₀ u ++Tm' m

_++Ty_ : ∀ (A : TyExpr n) m → TyExpr (n ++ℕ m)
A ++Ty m = 0 ! A ++Ty' m

_++Tm_ : ∀ (A : TmExpr n) m → TmExpr (n ++ℕ m)
u ++Tm m = 0 ! u ++Tm' m

var++Derivable : ∀ (Γ : Ctx n) (Δ : CtxExt n m) (k : Fin n) (A : TyExpr n)
  → Derivable (Γ ⊢ var k :> A)
  → Derivable ((Γ ++Ctx Δ) ⊢ var (k ++F m) :> (A ++Ty m))
var++Derivable {m = 0} Γ Δ k A Γ⊢k = Γ⊢k
var++Derivable {m = suc m} Γ (B , Δ) k A Γ⊢k =
  var++Derivable {m = m} (Γ , B) Δ (prev k) (weakenTy A) (VarPrev Γ⊢k)

shiftMor^ : ∀ l (δ : Mor n k) → Mor (l + n) (l + k)
shiftMor^ 0 δ = δ
shiftMor^ (suc l) δ = shiftMor (shiftMor^ l δ)

var++Tm : ∀ (k : Fin n) m → var (k ++F m) ≡ var k ++Tm m
var++Tm k 0 = refl
var++Tm k (suc m) = var++Tm (prev k) m

var[idGen]Tm : ∀ (k : Fin n) m → var k [ idMorGen n m ]Tm ≡ var k ++Tm m
var[idGen]Tm last m = var++Tm last m
var[idGen]Tm (prev k) m = var[idGen]Tm k (suc m)

{- ultimate dark induction magic -}

weakenTy'' : (l₀ l₁ : ℕ) → TyExpr (l₀ + (l₁ + n)) → TyExpr (l₀ + (l₁ + suc n))
weakenTm'' : (l₀ l₁ : ℕ) → TmExpr (l₀ + (l₁ + n)) → TmExpr (l₀ + (l₁ + suc n))
weakenVar'' : (l₀ l₁  : ℕ) → Fin (l₀ + (l₁ + n)) → Fin (l₀ + (l₁ + suc n))

weakenTy'' l₀ l₁ (pi A B) = pi (weakenTy'' l₀ l₁ A) (weakenTy'' (suc l₀) l₁ B)
weakenTy'' l₀ l₁ uu = uu
weakenTy'' l₀ l₁ (el v) = el (weakenTm'' l₀ l₁ v)

weakenTm'' l₀ l₁ (var x) = var (weakenVar'' l₀ l₁ x)
weakenTm'' l₀ l₁ (lam A B u) = lam (weakenTy'' l₀ l₁ A) (weakenTy'' (suc l₀) l₁ B) (weakenTm'' (suc l₀) l₁ u)
weakenTm'' l₀ l₁ (app A B f a) = app (weakenTy'' l₀ l₁ A) (weakenTy'' (suc l₀) l₁ B) (weakenTm'' l₀ l₁ f) (weakenTm'' l₀ l₁ a)

weakenVar'' 0 l v = weakenVar' l v
weakenVar'' (suc l₀) l₁ last = last
weakenVar'' (suc l₀) l₁ (prev v) = prev (weakenVar'' l₀ l₁ v)

weakenVar'WeakenVar'' : ∀ l₀ l₁ (v : Fin (l₀ + (l₁ + n)))
  → weakenTm' l₀ (weakenTm'' l₀ l₁ (var v)) ≡ weakenTm'' l₀ (suc l₁) (weakenTm' l₀ (var v))
weakenVar'WeakenVar'' 0 l v = refl
weakenVar'WeakenVar'' (suc l₀) l₁ last = refl
weakenVar'WeakenVar'' (suc l₀) l₁ (prev v) = ap weakenTm (weakenVar'WeakenVar'' l₀ l₁ v)

weakenTy'WeakenTy'' : ∀ l₀ l₁ (u : TyExpr (l₀ + (l₁ + n)))
  → weakenTy' l₀ (weakenTy'' l₀ l₁ u) ≡ weakenTy'' l₀ (suc l₁) (weakenTy' l₀ u)
weakenTm'WeakenTm'' : ∀ l₀ l₁ (u : TmExpr (l₀ + (l₁ + n)))
  → weakenTm' l₀ (weakenTm'' l₀ l₁ u) ≡ weakenTm'' l₀ (suc l₁) (weakenTm' l₀ u)

weakenTm'WeakenTm'' l₀ l₁ (var v) = weakenVar'WeakenVar'' l₀ l₁ v
weakenTm'WeakenTm'' l₀ l₁ (lam A B u) rewrite weakenTy'WeakenTy'' l₀ l₁ A | weakenTy'WeakenTy'' (suc l₀) l₁ B | weakenTm'WeakenTm'' (suc l₀) l₁ u = refl
weakenTm'WeakenTm'' l₀ l₁ (app A B f a) rewrite weakenTy'WeakenTy'' l₀ l₁ A | weakenTy'WeakenTy'' (suc l₀) l₁ B | weakenTm'WeakenTm'' l₀ l₁ f | weakenTm'WeakenTm'' l₀ l₁ a = refl

weakenTy'WeakenTy'' l₀ l₁ (pi A B) rewrite weakenTy'WeakenTy'' l₀ l₁ A | weakenTy'WeakenTy'' (suc l₀) l₁ B = refl
weakenTy'WeakenTy'' l₀ l₁ uu = refl
weakenTy'WeakenTy'' l₀ l₁ (el u) rewrite weakenTm'WeakenTm'' l₀ l₁ u = refl

transport-last : ∀ (p : suc n ≡ suc n') → transport Fin p last ≡ last
transport-last refl = refl

transport-prev : ∀ (p : n ≡ n') (v : Fin n) → transport Fin (ap suc p) (prev v) ≡ prev (transport Fin p v)
transport-prev refl v = refl

weakenVar'≡weakenVar'' : ∀ l₀ l₁ (v : Fin ((l₀ + l₁) + n))
  → transport Fin (+-assoc l₀ l₁ (suc n)) (weakenVar' (l₀ + l₁) v)
  ≡ weakenVar'' l₀ l₁ (transport Fin (+-assoc l₀ l₁ n) v)
weakenVar'≡weakenVar'' 0 0 v = refl
weakenVar'≡weakenVar'' 0 (suc l₁) last = refl
weakenVar'≡weakenVar'' 0 (suc l₁) (prev v) = ap prev (weakenVar'≡weakenVar'' 0 l₁ v)
weakenVar'≡weakenVar'' {n = n} (suc l₀) l₁ last
  rewrite transport-last (+-assoc (suc l₀) l₁ (suc n))
  | transport-last (+-assoc (suc l₀) l₁ n)
  = refl
weakenVar'≡weakenVar'' {n = n} (suc l₀) l₁ (prev v)
  rewrite transport-prev (+-assoc l₀ l₁ (suc n)) (weakenVar' (l₀ + l₁) v)
  | transport-prev (+-assoc l₀ l₁ n) v
  | weakenVar'≡weakenVar'' l₀ l₁ v
  = refl

transport-pi : ∀ (p : n ≡ n') (A : TyExpr n) (B : TyExpr (suc n))
  → transport TyExpr p (pi A B) ≡ pi (transport TyExpr p A) (transport TyExpr (ap suc p) B)
transport-pi refl A B = refl

transport-uu : ∀ (p : n ≡ n')  → transport TyExpr p uu ≡ uu
transport-uu refl = refl

transport-el : ∀ (p : n ≡ n') (v : TmExpr n)
  → transport TyExpr p (el v) ≡ el (transport TmExpr p v)
transport-el refl v = refl

transport-var : ∀ (p : n ≡ n') (v : Fin n)
  → transport TmExpr p (var v) ≡ var (transport Fin p v)
transport-var refl v = refl

transport-lam : ∀ (p : n ≡ n') (A : TyExpr n) (B : TyExpr (suc n)) (u : TmExpr (suc n))
  → transport TmExpr p (lam A B u)
  ≡ lam (transport TyExpr p A) (transport TyExpr (ap suc p) B) (transport TmExpr (ap suc p) u)
transport-lam refl A B u = refl

transport-app : ∀ (p : n ≡ n') (A : TyExpr n) (B : TyExpr (suc n)) (f : TmExpr n) (a : TmExpr n)
  → transport TmExpr p (app A B f a)
  ≡ app (transport TyExpr p A) (transport TyExpr (ap suc p) B) (transport TmExpr p f) (transport TmExpr p a)
transport-app refl A B f a = refl

weakenTy'≡weakenTy'' : ∀ l₀ l₁ (A : TyExpr ((l₀ + l₁) + n))
  → transport TyExpr (+-assoc l₀ l₁ (suc n)) (weakenTy' (l₀ + l₁) A)
  ≡ weakenTy'' l₀ l₁ (transport TyExpr (+-assoc l₀ l₁ n) A)
weakenTm'≡weakenTm'' : ∀ l₀ l₁ (u : TmExpr ((l₀ + l₁) + n))
  → transport TmExpr (+-assoc l₀ l₁ (suc n)) (weakenTm' (l₀ + l₁) u)
  ≡ weakenTm'' l₀ l₁ (transport TmExpr (+-assoc l₀ l₁ n) u)

weakenTy'≡weakenTy'' {n = n} l₀ l₁ (pi A B)
  rewrite transport-pi (+-assoc l₀ l₁ (suc n)) (weakenTy' (l₀ + l₁) A) (weakenTy' (suc l₀ + l₁) B)
  | transport-pi (+-assoc l₀ l₁ n) A B
  | weakenTy'≡weakenTy'' l₀ l₁ A
  | weakenTy'≡weakenTy'' (suc l₀) l₁ B
  = refl
weakenTy'≡weakenTy'' {n = n} l₀ l₁ uu
  rewrite transport-uu (+-assoc l₀ l₁ (suc n))
  | transport-uu (+-assoc l₀ l₁ n)
  = refl
weakenTy'≡weakenTy'' {n = n} l₀ l₁ (el v)
  rewrite transport-el (+-assoc l₀ l₁ (suc n)) (weakenTm' (l₀ + l₁) v)
  | transport-el (+-assoc l₀ l₁ n) v
  | weakenTm'≡weakenTm'' l₀ l₁ v
  = refl

weakenTm'≡weakenTm'' {n = n} l₀ l₁ (var v)
  rewrite transport-var (+-assoc l₀ l₁ (suc n)) (weakenVar' (l₀ + l₁) v)
  | transport-var (+-assoc l₀ l₁ n) v
  | weakenVar'≡weakenVar'' l₀ l₁ v
  = refl
weakenTm'≡weakenTm'' {n = n} l₀ l₁ (lam A B u)
  rewrite transport-lam (+-assoc l₀ l₁ (suc n)) (weakenTy' (l₀ + l₁) A) (weakenTy' (suc l₀ + l₁) B) (weakenTm' (suc l₀ + l₁) u)
  | transport-lam (+-assoc l₀ l₁ n) A B u
  | weakenTy'≡weakenTy'' l₀ l₁ A
  | weakenTy'≡weakenTy'' (suc l₀) l₁ B
  | weakenTm'≡weakenTm'' (suc l₀) l₁ u
  = refl
weakenTm'≡weakenTm'' {n = n} l₀ l₁ (app A B f a)
  rewrite transport-app (+-assoc l₀ l₁ (suc n)) (weakenTy' (l₀ + l₁) A) (weakenTy' (suc l₀ + l₁) B) (weakenTm' (l₀ + l₁) f) (weakenTm' (l₀ + l₁) a)
  | transport-app (+-assoc l₀ l₁ n) A B f a
  | weakenTy'≡weakenTy'' l₀ l₁ A
  | weakenTy'≡weakenTy'' (suc l₀) l₁ B
  | weakenTm'≡weakenTm'' l₀ l₁ f
  | weakenTm'≡weakenTm'' l₀ l₁ a
  = refl

weakenTm'≡weakenTm''0 : ∀ l (u : TmExpr (l + n))
  → weakenTm' l u ≡ weakenTm'' 0 l u
weakenTm'≡weakenTm''0 l = weakenTm'≡weakenTm'' 0 l

weakenTmWeakenTm' : ∀ l (u : TmExpr (l + n))
  → weakenTm (weakenTm' l u) ≡ weakenTm' (suc l) (weakenTm u)
weakenTmWeakenTm' l u
  rewrite weakenTm'≡weakenTm''0 l u
  | weakenTm'≡weakenTm''0 (suc l) (weakenTm u)
  = weakenTm'WeakenTm'' 0 l u

weaken++Tm' : ∀ l (u : TmExpr (l + n)) m
  → weakenTm (l ! u ++Tm' m) ≡ (suc l ! weakenTm u ++Tm' m)
weaken++Tm' l u 0 = refl
weaken++Tm' l u (suc m) =
    weaken++Tm' l (weakenTm' l u) m
  ∙ ap (λ u → suc l ! u ++Tm' m) (weakenTmWeakenTm' l u)

var[weaken]Tm : ∀ (v : Fin n) (δ : Mor m n)
  → var v [ weakenMor δ ]Tm ≡ weakenTm (var v [ δ ]Tm)
var[weaken]Tm last (δ , u) = refl
var[weaken]Tm (prev v) (δ , u) = var[weaken]Tm v δ

var[shiftedIdGen]Tm : ∀ l (v : Fin (l + n)) m
  → var v [ shiftMor^ l (idMorGen n m) ]Tm ≡ (l ! var v ++Tm' m)
var[shiftedIdGen]Tm 0 = var[idGen]Tm
var[shiftedIdGen]Tm {n = n} (suc l) last 0 = refl
var[shiftedIdGen]Tm {n = n} (suc l) last (suc m) =
  var[shiftedIdGen]Tm {n = suc n} (suc l) last m
var[shiftedIdGen]Tm {n = n} (suc l) (prev v) m rewrite
  var[weaken]Tm v (shiftMor^ l (idMorGen n m)) |
  var[shiftedIdGen]Tm {n = n} l v m |
  weaken++Tm' l (var v) m
  = refl

pi++Ty' : ∀ l (A : TyExpr (l + n)) (B : TyExpr (suc l + n)) m
  → l ! pi A B ++Ty' m ≡ pi (l ! A ++Ty' m) (suc l ! B ++Ty' m)
pi++Ty' l A B 0 = refl
pi++Ty' l A B (suc m) = pi++Ty' l (weakenTy' l A) (weakenTy' (suc l) B) m

uu++Ty' : ∀ {n : ℕ} l m → l ! uu {n = l + n} ++Ty' m ≡ uu
uu++Ty' l 0 = refl
uu++Ty' l (suc m) = uu++Ty' l m

el++Ty' : ∀ l (v : TmExpr (l + n)) m
  → l ! el v ++Ty' m ≡ el (l ! v ++Tm' m)
el++Ty' l v 0 = refl
el++Ty' l v (suc m) = el++Ty' l (weakenTm' l v) m

lam++Tm' : ∀ l (A : TyExpr (l + n)) (B : TyExpr (suc l + n)) (u : TmExpr (suc l + n)) m
  → l ! lam A B u ++Tm' m ≡ lam (l ! A ++Ty' m) (suc l ! B ++Ty' m) (suc l ! u ++Tm' m)
lam++Tm' l A B u 0 = refl
lam++Tm' l A B u (suc m) = lam++Tm' l (weakenTy' l A) (weakenTy' (suc l) B) (weakenTm' (suc l) u) m

app++Tm' : ∀ l (A : TyExpr (l + n)) (B : TyExpr (suc l + n)) (f a : TmExpr (l + n)) m
  → l ! app A B f a ++Tm' m ≡ app (l ! A ++Ty' m) (suc l ! B ++Ty' m) (l ! f ++Tm' m) (l ! a ++Tm' m)
app++Tm' l A B f a 0 = refl
app++Tm' l A B f a (suc m) = app++Tm' l (weakenTy' l A) (weakenTy' (suc l) B) (weakenTm' l f) (weakenTm' l a) m

[shiftedIdGen]Ty : ∀ l A m → A [ shiftMor^ l (idMorGen n m) ]Ty ≡ (l ! A ++Ty' m)
[shiftedIdGen]Tm : ∀ l u m → u [ shiftMor^ l (idMorGen n m) ]Tm ≡ (l ! u ++Tm' m)

[shiftedIdGen]Ty l (pi A B) m rewrite
  [shiftedIdGen]Ty l A m |
  [shiftedIdGen]Ty (suc l) B m |
  pi++Ty' l A B m
  = refl
[shiftedIdGen]Ty {n = n} l uu m rewrite
  uu++Ty' {n = n} l m
  = refl
[shiftedIdGen]Ty l (el v) m rewrite
  [shiftedIdGen]Tm l v m |
  el++Ty' l v m
  = refl

[shiftedIdGen]Tm l (var v) m = var[shiftedIdGen]Tm l v m
[shiftedIdGen]Tm l (lam A B u) m rewrite
  [shiftedIdGen]Ty l A m |
  [shiftedIdGen]Ty (suc l) B m |
  [shiftedIdGen]Tm (suc l) u m |
  lam++Tm' l A B u m
  = refl
[shiftedIdGen]Tm l (app A B f a) m rewrite
  [shiftedIdGen]Ty l A m |
  [shiftedIdGen]Ty (suc l) B m |
  [shiftedIdGen]Tm l f m |
  [shiftedIdGen]Tm l a m |
  app++Tm' l A B f a m
  = refl

idMorGenDerivable : ∀ {Γ : Ctx n} (⊢Γ : ⊢ Γ) (Δ : CtxExt n m)
  → (Γ ++Ctx Δ) ⊢ idMorGen n m ∷> Γ
idMorGenDerivable {n = 0} {Γ = ◇} tt Δ = tt
idMorGenDerivable {n = suc n} {m} {Γ = (Γ , A)} (⊢Γ , Γ⊢A) Δ
  rewrite [shiftedIdGen]Ty 0 A (suc m) =
  idMorGenDerivable ⊢Γ (A , Δ) , var++Derivable (Γ , A) Δ last (weakenTy A) (VarLast Γ⊢A)

.idMorAltDerivable : ∀ {Γ : Ctx n} → ⊢ Γ → Γ ⊢ idMorAlt n ∷> Γ
idMorAltDerivable ⊢Γ = idMorGenDerivable ⊢Γ tt

.idMorDerivable : ∀ {Γ : Ctx n} → ⊢ Γ → Γ ⊢ idMor n ∷> Γ
idMorDerivable {n = n} ⊢Γ rewrite idMor≡idMorAlt n = idMorAltDerivable ⊢Γ
