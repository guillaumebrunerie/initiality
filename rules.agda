{-# OPTIONS --irrelevant-projections --type-in-type --rewriting --allow-unsolved-metas #-}

open import common
open import syntx

{- The four different forms of (pre)judgments. -}

data Judgment : Set where
  _⊢_ : (Γ : Ctx n) → TyExpr n → Judgment
  _⊢_:>_ : (Γ : Ctx n) → TmExpr n → TyExpr n → Judgment
  _⊢_==_ : (Γ : Ctx n) → TyExpr n → TyExpr n → Judgment
  _⊢_==_:>_ : (Γ : Ctx n) → TmExpr n → TmExpr n → TyExpr n → Judgment

data _∋_:>_ : {n : ℕ} (Γ : Ctx n) → Fin n → TyExpr n → Set where
  last : {Γ : Ctx n} {A : TyExpr n} → (Γ , A) ∋ last :> weakenTy A
  prev : {Γ : Ctx n} {x : Fin n} {A B : TyExpr n} → (Γ ∋ x :> A) → (Γ , B) ∋ prev x :> weakenTy A

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
Γ ⊢ (δ , u) ∷> (Δ , A) = (Γ ⊢ δ ∷> Δ) ×' Derivable (Γ ⊢ u :> A [ δ ]Ty)

_⊢_==_∷>_ : (Γ : Ctx n) → Mor n m → Mor n m → Ctx m → Set
Γ ⊢ ◇ == ◇ ∷> ◇ = Unit
Γ ⊢ (δ , u) == (δ' , u') ∷> (Δ , A) = (Γ ⊢ δ == δ' ∷> Δ) ×' Derivable (Γ ⊢ u == u' :> A [ δ ]Ty)

data Derivable where

  -- Variable rule
  VarRule : {Γ : Ctx n} {x : Fin n} {A : TyExpr n}
          → (Γ ∋ x :> A) → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ var x :> A)

  -- Congruence for variables
  VarCong : {Γ : Ctx n} {x : Fin n} {A : TyExpr n}
          → (Γ ∋ x :> A) → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ var x == var x :> A)

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

  -- Beta-reduction
  Beta : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)} {a : TmExpr n}
       → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ a :> A)
       → Derivable (Γ ⊢ app A B (lam A B u) a == substTm u a :> substTy B a)

  -- Substitution rules
  SubstTy : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m}
       → .(_ : Derivable (Δ ⊢ A)) → .(_ : Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty)
  SubstTm : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ u :> A) → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm :> A [ δ ]Ty)
  SubstTyEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ : Mor n m}
       → .(_ : Derivable (Δ ⊢ A == A')) → .(_ : Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ ]Ty)
  SubstTmEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u' [ δ ]Tm :> A [ δ ]Ty)
  SubstTySubstEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m}
       → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
  SubstTmSubstEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m}
       → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u' [ δ' ]Tm :> A [ δ' ]Ty)

  -- Weakening rules
  WeakTy : {Γ : Ctx n} {T : TyExpr n} {A : TyExpr n}
       → Derivable (Γ ⊢ A) → Derivable ((Γ , T) ⊢ weakenTy A)
  WeakTm : {Γ : Ctx n} {T : TyExpr n} {u : TmExpr n} {A : TyExpr n}
       → Derivable (Γ ⊢ u :> A) → Derivable ((Γ , T) ⊢ weakenTm u :> weakenTy A)
  WeakTyEq : {Γ : Ctx n} {T : TyExpr n} {A A' : TyExpr n}
       → Derivable (Γ ⊢ A == A') → Derivable ((Γ , T) ⊢ weakenTy A == weakenTy A')
  WeakTmEq : {Γ : Ctx n} {T : TyExpr n} {u u' : TmExpr n} {A : TyExpr n}
       → Derivable (Γ ⊢ u == u' :> A) → Derivable ((Γ , T) ⊢ weakenTm u == weakenTm u' :> weakenTy A)

{- Congruence with respect to the type in derivability of term expressions -}

.congTm : {Γ : Ctx n} {A A' : TyExpr n} {u : TmExpr n} → A ≡ A' → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u :> A')
congTm refl d = d

.congTmEq : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A ≡ A' → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u == u' :> A')
congTmEq refl d = d

{- Admissible rules -}

SubstMor : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ : Mor m k} {δ : Mor n m}
       → (Δ ⊢ θ ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ θ [ δ ]Mor ∷> Θ)
SubstMor {Θ = ◇} {θ = ◇} tt dδ = tt
SubstMor {Θ = Θ , C} {θ = θ , w} (dθ , dw) dδ = (SubstMor dθ dδ , congTm ([]Ty-assoc _ θ C) (SubstTm dw dδ))

.TyRefl : {Γ : Ctx n} {A : TyExpr n} → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A)
.TmRefl : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u == u :> A)

TyRefl (Pi dA dB) = PiCong (TyRefl dA) (TyRefl dB)
TyRefl UU = UUCong
TyRefl (El dv) = ElCong (TmRefl dv)
TyRefl (SubstTy dA dδ) = SubstTyEq (TyRefl dA) dδ
TyRefl (WeakTy dA) = WeakTyEq (TyRefl dA)

TmRefl (VarRule x∈ dA) = VarCong x∈ dA
TmRefl (Conv du dA=) = ConvEq (TmRefl du) dA=
TmRefl (SubstTm du dδ) = SubstTmEq (TmRefl du) dδ
TmRefl (Lam dA dB du) = LamCong (TyRefl dA) (TyRefl dB) (TmRefl du)
TmRefl (App dA dB df da) = AppCong (TyRefl dA) (TyRefl dB) (TmRefl df) (TmRefl da)
TmRefl (WeakTm du) = WeakTmEq (TmRefl du)

ConvTyEq : {Γ Δ : Ctx n} {A B : TyExpr n} → Derivable (Γ ⊢ A == B) → (⊢ Γ == Δ) → Derivable (Δ ⊢ A == B)
ConvTyEq dA= dΓ= = {!!}

.ConvMor : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ : Mor n m} → (Γ ⊢ δ ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ ∷> Δ')
ConvMor dδ dΓ= dΔ= = {!!}

ConvMorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} → (Γ ⊢ δ == δ' ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ == δ' ∷> Δ')
ConvMorEq dδ= dΓ= dΔ= = {!!}

CtxRefl : {Γ : Ctx n} → ⊢ Γ → ⊢ Γ == Γ
CtxRefl {Γ = ◇} tt = tt
CtxRefl {Γ = Γ , A} (dΓ , dA) = (CtxRefl dΓ , TyRefl dA)

CtxSymm : {Γ Δ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Γ
CtxSymm {Γ = ◇} {Δ = ◇} tt = tt
CtxSymm {Γ = Γ , A} {Δ , B} (dΓ= , dA=) = (CtxSymm dΓ= , ConvTyEq (TySymm dA=) dΓ=)

CtxTran : {Γ Δ Θ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Θ → ⊢ Γ == Θ
CtxTran {Γ = ◇} {Δ = ◇} {Θ = ◇} tt tt = tt
CtxTran {Γ = Γ , A} {Δ , B} {Θ , C} (dΓ= , dA=) (dΔ= , dB=) = (CtxTran dΓ= dΔ= , TyTran dA= (ConvTyEq dB= (CtxSymm dΓ=)))

.MorRefl : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} → Γ ⊢ δ ∷> Δ → Γ ⊢ δ == δ ∷> Δ
MorRefl {Δ = ◇} {◇} tt = tt
MorRefl {Δ = Δ , B} {δ , u} (dδ , du) = (MorRefl dδ , TmRefl du)

MorSymm : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ ∷> Δ
MorSymm {Δ = ◇} {◇} {◇} _ tt = tt
MorSymm {Δ = Δ , B} {δ , u} {δ' , u'} (dΔ , dB) (dδ , du) = (MorSymm dΔ dδ) , (ConvEq (TmSymm du) (SubstTySubstEq (TyRefl dB) dδ))

MorTran : {Γ : Ctx n} {Δ : Ctx m} {δ δ' δ'' : Mor n m} → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ'' ∷> Δ → Γ ⊢ δ == δ'' ∷> Δ
MorTran {Δ = ◇} {◇} {◇} {◇} _ tt tt = tt
MorTran {Δ = Δ , B} {δ , u} {δ' , u'} {δ'' , u''} (dΔ , dB) (dδ , du) (dδ' , du') = (MorTran dΔ dδ dδ') , TmTran du (ConvEq du' (SubstTySubstEq (TyRefl dB) (MorSymm dΔ dδ)))

WeakMor : {Γ : Ctx n} {Δ : Ctx m} {T : TyExpr n} {δ : Mor n m} → Γ ⊢ δ ∷> Δ → (Γ , T) ⊢ weakenMor δ ∷> Δ
WeakMor {Δ = ◇} {δ = ◇} tt = tt
WeakMor {Δ = Δ , B} {δ = δ , u} (dδ , du) = (WeakMor dδ , congTm (weaken[]Ty B δ last) (WeakTm du))

.idMorDerivable : {n : ℕ} {Γ : Ctx n} (_ : ⊢ Γ) → (Γ ⊢ idMor n ∷> Γ)
idMorDerivable {Γ = ◇} tt = tt
idMorDerivable {Γ = Γ , A} (dΓ , dA) = WeakMor (idMorDerivable dΓ) , congTm (ap weakenTy (! ([idMor]Ty A)) ∙ weaken[]Ty A (idMor _) last) (VarRule last (WeakTy dA))
