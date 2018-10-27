{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

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
data Derivable : Judgment → Prop

⊢_ : Ctx n → Prop
⊢ ◇ = Unit
⊢ (Γ , A) = (⊢ Γ) × Derivable (Γ ⊢ A)

⊢_==_ : Ctx n → Ctx n → Prop
⊢ ◇ == ◇ = Unit
⊢ (Γ , A) == (Γ' , A') = (⊢ Γ == Γ') × Derivable (Γ ⊢ A) × Derivable (Γ' ⊢ A') × Derivable (Γ ⊢ A == A')

_⊢_∷>_ : (Γ : Ctx n) → Mor n m → Ctx m → Prop
Γ ⊢ ◇ ∷> ◇ = Unit
Γ ⊢ (δ , u) ∷> (Δ , A) = (Γ ⊢ δ ∷> Δ) × Derivable (Γ ⊢ u :> A [ δ ]Ty)

_⊢_==_∷>_ : (Γ : Ctx n) → Mor n m → Mor n m → Ctx m → Prop
Γ ⊢ ◇ == ◇ ∷> ◇ = Unit
Γ ⊢ (δ , u) == (δ' , u') ∷> (Δ , A) = (Γ ⊢ δ == δ' ∷> Δ) × Derivable (Γ ⊢ u == u' :> A [ δ ]Ty)

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
         → Derivable (Γ ⊢ A == B)→ Derivable (Γ ⊢ B == C) → Derivable (Γ ⊢ B) → Derivable (Γ ⊢ A == C)

  -- Symmetry and transitivity for terms
  TmSymm : {Γ : Ctx n} {u v : TmExpr n} {A : TyExpr n}
         → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ v == u :> A)
  TmTran : {Γ : Ctx n} {u v w : TmExpr n} {A : TyExpr n}
         → Derivable (Γ ⊢ u == v :> A)→ Derivable (Γ ⊢ v == w :> A) → Derivable (Γ ⊢ u == w :> A)

  -- Conversion rule
  Conv : {Γ : Ctx n} {u : TmExpr n} {A B : TyExpr n}
       → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ u :> B)
  ConvEq : {Γ : Ctx n} {u u' : TmExpr n} {A B : TyExpr n}
       → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ u == u' :> B)

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
      → (dA : Derivable (Γ ⊢ A)) (dB : Derivable ((Γ , A) ⊢ B)) (df : Derivable (Γ ⊢ f :> pi A B)) (da : Derivable (Γ ⊢ a :> A)) → Derivable (Γ ⊢ app A B f a :> B [ idMor n , a ]Ty)
  AppCong : {n : ℕ} {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {f f' a a' : TmExpr n}
      → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ f == f' :> pi A B) → Derivable (Γ ⊢ a == a' :> A) → Derivable (Γ ⊢ app A B f a == app A' B' f' a' :> B [ idMor n , a ]Ty)

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

.congTy : {Γ : Ctx n} {A A' : TyExpr n} → A ≡R A' → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A')
congTy reflR d = d

.congTyEq : {Γ : Ctx n} {A A' B B' : TyExpr n} → A ≡R A' → B ≡R B' → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A' == B')
congTyEq reflR reflR d = d

.congTm : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A ≡R A' → u ≡R u' → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u' :> A')
congTm reflR reflR d = d

.congTmEq : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A ≡R A' → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u == u' :> A')
congTmEq reflR d = d

congMor : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} → Γ ≡R Γ' → Δ ≡R Δ' → δ ≡R δ' → Γ ⊢ δ ∷> Δ → Γ' ⊢ δ' ∷> Δ'
congMor reflR reflR reflR d = d

{- Admissible rules -}

SubstMor : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ : Mor m k} {δ : Mor n m}
       → (Δ ⊢ θ ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ θ [ δ ]Mor ∷> Θ)
SubstMor {Θ = ◇} {θ = ◇} tt dδ = tt
SubstMor {Θ = Θ , C} {θ = θ , w} (dθ , dw) dδ = (SubstMor dθ dδ , congTm ([]Ty-assoc _ θ C) reflR (SubstTm dw dδ))

.TyRefl : {Γ : Ctx n} {A : TyExpr n} → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A)
.TmRefl : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u == u :> A)

TyRefl (Pi dA dB) = PiCong (TyRefl dA) (TyRefl dB)
TyRefl UU = UUCong
TyRefl (El dv) = ElCong (TmRefl dv)
TyRefl (SubstTy dA dδ) = SubstTyEq (TyRefl dA) dδ
TyRefl (WeakTy dA) = WeakTyEq (TyRefl dA)

TmRefl (VarRule x∈ dA) = VarCong x∈ dA
TmRefl (Conv du dA dA=) = ConvEq (TmRefl du) dA dA=
TmRefl (SubstTm du dδ) = SubstTmEq (TmRefl du) dδ
TmRefl (Lam dA dB du) = LamCong (TyRefl dA) (TyRefl dB) (TmRefl du)
TmRefl (App dA dB df da) = AppCong (TyRefl dA) (TyRefl dB) (TmRefl df) (TmRefl da)
TmRefl (WeakTm du) = WeakTmEq (TmRefl du)

WeakMor : {Γ : Ctx n} {Δ : Ctx m} {T : TyExpr n} {δ : Mor n m} → Γ ⊢ δ ∷> Δ → (Γ , T) ⊢ weakenMor δ ∷> Δ
WeakMor {Δ = ◇} {δ = ◇} tt = tt
WeakMor {Δ = Δ , B} {δ = δ , u} (dδ , du) = (WeakMor dδ , congTm (weaken[]Ty B δ last) reflR (WeakTm du))

.idMorDerivable : {Γ : Ctx n} (_ : ⊢ Γ) → (Γ ⊢ idMor n ∷> Γ)
idMorDerivable {Γ = ◇} tt = tt
idMorDerivable {Γ = Γ , A} (dΓ , dA) = WeakMor (idMorDerivable dΓ) , congTm (apR weakenTy (!R ([idMor]Ty A)) ∙R weaken[]Ty A (idMor _) last) reflR (VarRule last (WeakTy dA))

eqMorDer : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' → Γ' ⊢ idMor n ∷> Γ
eqMorDer {Γ = ◇} dΓ= = tt
eqMorDer {Γ = Γ , A} {Γ' = Γ' , A'} (dΓ= , dA , dA' , dA=) = WeakMor (eqMorDer dΓ=) , Conv (VarRule last (WeakTy dA')) (TyTran {!!} {!!} {!!}) (WeakTy dA')

CtxRefl : {Γ : Ctx n} → ⊢ Γ → ⊢ Γ == Γ
CtxRefl {Γ = ◇} tt = tt
CtxRefl {Γ = Γ , A} (dΓ , dA) = (CtxRefl dΓ , dA , dA , TyRefl dA)

CtxEqCtx1 : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' → ⊢ Γ
CtxEqCtx1 {Γ = ◇} {Γ' = ◇} tt = tt
CtxEqCtx1 {Γ = Γ , A} {Γ' = Γ' , A'} (dΓ= , dA , dA' , dA=) = CtxEqCtx1 dΓ= , dA

CtxEqCtx2 : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' → ⊢ Γ'
CtxEqCtx2 {Γ = ◇} {Γ' = ◇} tt = tt
CtxEqCtx2 {Γ = Γ , A} {Γ' = Γ' , A'} (dΓ= , dA , dA' , dA=) = CtxEqCtx2 dΓ= , dA'

.ConvMor : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ : Mor n m} → (Γ ⊢ δ ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ ∷> Δ')
ConvTm : {Γ Δ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ u :> A)

ConvMor {Δ = ◇} {Δ' = ◇} {δ = ◇} dδ dΓ= dΔ= = tt
ConvMor {Δ = Δ , B} {Δ' = Δ' , B'} {δ = δ , u} (dδ , du) dΓ= (dΔ= , dB , dB' , dB=) = (ConvMor dδ dΓ= dΔ=) , ConvTm (Conv du (SubstTyEq dB= dδ) (SubstTy dB dδ)) dΓ=

ConvTm du dΓ= = congTm ([idMor]Ty _) ([idMor]Tm _) (SubstTm du (eqMorDer dΓ=))

.ConvTyEq : {Γ Δ : Ctx n} {A B : TyExpr n} → Derivable (Γ ⊢ A == B) → (⊢ Γ == Δ) → Derivable (Δ ⊢ A == B)
ConvTyEq {n = n} dA= dΓ= = congTyEq ([idMor]Ty _) ([idMor]Ty _) (SubstTyEq dA= (eqMorDer dΓ= ))

ConvMorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} → (Γ ⊢ δ == δ' ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ == δ' ∷> Δ')
ConvMorEq dδ= dΓ= dΔ= = {!congMorEq!}

ConvTy : {Γ Δ : Ctx n} {A : TyExpr n} → Derivable (Γ ⊢ A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ A)
ConvTy dA dΓ= = congTy ([idMor]Ty _) (SubstTy dA (eqMorDer dΓ=))

CtxSymm : {Γ Δ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Γ
CtxSymm {Γ = ◇} {Δ = ◇} tt = tt
CtxSymm {Γ = Γ , A} {Δ , B} (dΓ= , dA , dB , dA=) = (CtxSymm dΓ= , dB , dA , ConvTyEq (TySymm dA=) dΓ=)

CtxTran : {Γ Δ Θ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Θ → ⊢ Γ == Θ
CtxTran {Γ = ◇} {Δ = ◇} {Θ = ◇} tt tt = tt
CtxTran {Γ = Γ , A} {Δ , B} {Θ , C} (dΓ= , dA , dB , dA=) (dΔ= , dB' , dC , dB=) = (CtxTran dΓ= dΔ= , dA , dC , TyTran dA= (ConvTyEq dB= (CtxSymm dΓ=)) (ConvTy dB (CtxSymm dΓ=)))

.MorRefl : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} → Γ ⊢ δ ∷> Δ → Γ ⊢ δ == δ ∷> Δ
MorRefl {Δ = ◇} {◇} tt = tt
MorRefl {Δ = Δ , B} {δ , u} (dδ , du) = (MorRefl dδ , TmRefl du)

MorSymm : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ ∷> Δ
MorSymm {Δ = ◇} {◇} {◇} _ tt = tt
MorSymm {Δ = Δ , B} {δ , u} {δ' , u'} (dΔ , dB) (dδ , du) = (MorSymm dΔ dδ , ConvEq (TmSymm du) (SubstTySubstEq (TyRefl dB) dδ) (SubstTy dB {! dδ!}))

MorTran : {Γ : Ctx n} {Δ : Ctx m} {δ δ' δ'' : Mor n m} → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ'' ∷> Δ → Γ ⊢ δ == δ'' ∷> Δ
MorTran {Δ = ◇} {◇} {◇} {◇} _ tt tt = tt
MorTran {Δ = Δ , B} {δ , u} {δ' , u'} {δ'' , u''} (dΔ , dB) (dδ , du) (dδ' , du') = (MorTran dΔ dδ dδ') , TmTran du (ConvEq du' (SubstTySubstEq (TyRefl dB) (MorSymm dΔ dδ)) (SubstTy dB {!!}))

-- TyEqTy1 : {Γ : Ctx n} {A B : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A)
-- TyEqTy2 : {Γ : Ctx n} {A B : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B)

-- TyEqTy1 = {!!} 

-- TyEqTy2 dΓ (TySymm dA=) = TyEqTy1 dΓ dA=
-- TyEqTy2 dΓ (TyTran dA= dB=) = TyEqTy2 dΓ dB=
-- TyEqTy2 dΓ (PiCong dA= dB=) = Pi (TyEqTy2 dΓ dA=) (ConvTy (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) ((CtxRefl dΓ) , dA=))
-- TyEqTy2 dΓ UUCong = UU
-- TyEqTy2 dΓ (ElCong dv=) = El {!!}
-- TyEqTy2 dΓ (SubstTyEq dA= dδ) = SubstTy (TyEqTy2 {!!} dA=) dδ
-- TyEqTy2 dΓ (SubstTySubstEq dA= dδ=) = SubstTy (TyEqTy2 {!!} dA=) {!!}
-- TyEqTy2 (dΓ , _) (WeakTyEq dA=) = WeakTy (TyEqTy2 dΓ dA=)

-- TmTy : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A)
-- TmTy dΓ (VarRule x∈ dA) = dA
-- TmTy dΓ (Conv du dA= dA) = TyEqTy2 dΓ dA=
-- TmTy dΓ (Lam dA dB du) = Pi dA dB
-- TmTy dΓ (App dA dB df da) = SubstTy dB ((idMorDerivable dΓ) , congTm (! ([idMor]Ty _)) da)
-- TmTy dΓ (SubstTm du dδ) = SubstTy (TmTy {!!} du) dδ
-- TmTy (dΓ , dA) (WeakTm du) = WeakTy (TmTy dΓ du)
