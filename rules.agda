{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import common
open import syntx
 
{- The four different forms of (pre)judgments. -}

data Judgment : Set where
  _⊢_ : (Γ : Ctx n) → TyExpr n → Judgment
  _⊢_:>_ : (Γ : Ctx n) → TmExpr n → TyExpr n → Judgment
  _⊢_==_ : (Γ : Ctx n) → TyExpr n → TyExpr n → Judgment
  _⊢_==_:>_ : (Γ : Ctx n) → TmExpr n → TmExpr n → TyExpr n → Judgment


{- Derivability of judgments, the typing rules of the type theory -}

data Derivable : Judgment → Prop where

  -- Variable rules
  VarLast : {Γ : Ctx n} {A : TyExpr n}
    → Derivable (Γ ⊢ A)
    → Derivable ((Γ , A) ⊢ var last :> weakenTy A)
  VarPrev : {Γ : Ctx n} {B : TyExpr n} {k : Fin n} {A : TyExpr n}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ var k :> A)
    → Derivable ((Γ , B) ⊢ var (prev k) :> weakenTy A)
          
  -- Congruence for variables
  VarLastCong : {Γ : Ctx n} {A : TyExpr n}
    → Derivable (Γ ⊢ A)
    → Derivable ((Γ , A) ⊢ var last == var last :> weakenTy A)
  VarPrevCong : {Γ : Ctx n} {B : TyExpr n} {k k' : Fin n} {A : TyExpr n}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ var k == var k' :> A)
    → Derivable ((Γ , B) ⊢ var (prev k) == var (prev k') :> weakenTy A)
          
  -- Symmetry and transitivity for types
  TySymm : {Γ : Ctx n} {A B : TyExpr n}
    → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B == A)
  TyTran : {Γ : Ctx n} {A B C : TyExpr n}
    → Derivable (Γ ⊢ B) → Derivable (Γ ⊢ A == B)→ Derivable (Γ ⊢ B == C) → Derivable (Γ ⊢ A == C)

  -- Symmetry and transitivity for terms
  TmSymm : {Γ : Ctx n} {u v : TmExpr n} {A : TyExpr n}
    → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ v == u :> A)
  TmTran : {Γ : Ctx n} {u v w : TmExpr n} {A : TyExpr n}
    → Derivable (Γ ⊢ u == v :> A)→ Derivable (Γ ⊢ v == w :> A) → Derivable (Γ ⊢ u == w :> A)

  -- Conversion rules
  Conv : {Γ : Ctx n} {u : TmExpr n} {A B : TyExpr n} → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u :> B)
  ConvEq : {Γ : Ctx n} {u u' : TmExpr n} {A B : TyExpr n} → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u == u' :> B)

  -- Rules for Pi
  Pi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} 
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ pi A B)
  PiCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ pi A B == pi A' B')

  -- Rules for lambda
  Lam : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B)
    → Derivable (Γ ⊢ lam A B u :> pi A B)
  LamCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr (suc n)}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable ((Γ , A) ⊢ u == u' :> B)
    → Derivable (Γ ⊢ lam A B u == lam A' B' u' :> pi A B)

  -- Rules for app
  App : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ f :> pi A B) → Derivable (Γ ⊢ a :> A)
    → Derivable (Γ ⊢ app A B f a :> substTy B a)
  AppCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {f f' a a' : TmExpr n}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ f == f' :> pi A B) → Derivable (Γ ⊢ a == a' :> A)
    → Derivable (Γ ⊢ app A B f a == app A' B' f' a' :> substTy B a)

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
  Beta : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)} {a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ a :> A)
    → Derivable (Γ ⊢ app A B (lam A B u) a == substTm u a :> substTy B a)


{- Derivability of contexts, context equality, context morphisms, and context morphism equality -}

⊢_ : Ctx n → Prop
⊢ ◇ = Unit
⊢ (Γ , A) = (⊢ Γ) × Derivable (Γ ⊢ A)

⊢_==_ : Ctx n → Ctx n → Prop
⊢ ◇ == ◇ = Unit
⊢ (Γ , A) == (Γ' , A') = (⊢ Γ == Γ') × Derivable (Γ ⊢ A) × Derivable (Γ' ⊢ A') × Derivable (Γ ⊢ A == A') × Derivable (Γ' ⊢ A == A')

_⊢_∷>_ : (Γ : Ctx n) → Mor n m → Ctx m → Prop
Γ ⊢ ◇ ∷> ◇ = Unit
Γ ⊢ (δ , u) ∷> (Δ , A) = (Γ ⊢ δ ∷> Δ) × Derivable (Γ ⊢ u :> A [ δ ]Ty) 

_⊢_==_∷>_ : (Γ : Ctx n) → Mor n m → Mor n m → Ctx m → Prop
Γ ⊢ ◇ == ◇ ∷> ◇ = Unit
Γ ⊢ (δ , u) == (δ' , u') ∷> (Δ , A) = (Γ ⊢ δ == δ' ∷> Δ) × Derivable (Γ ⊢ u == u' :> A [ δ ]Ty)


{- Congruence with respect to the type in derivability of term expressions -}

congTy : {Γ : Ctx n} {A A' : TyExpr n} → A ≡ A' → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A')
congTy refl dA = dA

congTyEq : {Γ : Ctx n} {A A' B B' : TyExpr n} → A ≡ A' → B ≡ B' → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A' == B')
congTyEq refl refl dA= = dA=

congTm : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A ≡ A' → u ≡ u' → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u' :> A')
congTm refl refl du = du

congTmEqTy : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A ≡ A' → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u == u' :> A')
congTmEqTy refl du= = du=

congTmEqTm : {Γ : Ctx n} {A : TyExpr n} {u u' v v' : TmExpr n} → u ≡ v → u' ≡ v' → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ v == v' :> A)
congTmEqTm refl refl du= = du=

congMor : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} → Γ ≡ Γ' → Δ ≡ Δ' → δ ≡ δ' → Γ ⊢ δ ∷> Δ → Γ' ⊢ δ' ∷> Δ'
congMor refl refl refl dδ = dδ

congMorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' θ θ' : Mor n m} → Γ ≡ Γ' → Δ ≡ Δ' → δ ≡ δ' → θ ≡ θ' → Γ ⊢ δ == θ ∷> Δ → Γ' ⊢ δ' == θ' ∷> Δ'
congMorEq refl refl refl refl dδ= = dδ=


{- Reflexivity rules -}

TyRefl : {Γ : Ctx n} {A : TyExpr n} → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A)
TmRefl : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u == u :> A)

TyRefl (Pi dA dB) = PiCong dA (TyRefl dA) (TyRefl dB)
TyRefl UU = UUCong
TyRefl (El dv) = ElCong (TmRefl dv)

TmRefl (VarLast dA) = VarLastCong dA
TmRefl (VarPrev dA dk) = VarPrevCong dA (TmRefl dk) 
TmRefl (Conv dA du dA=) = ConvEq dA (TmRefl du) dA=
TmRefl (Lam dA dB du) = LamCong dA (TyRefl dA) (TyRefl dB) (TmRefl du)
TmRefl (App dA dB df da) = AppCong dA (TyRefl dA) (TyRefl dB) (TmRefl df) (TmRefl da)

congTyRefl : {Γ : Ctx n} {A A' : TyExpr n} → Derivable (Γ ⊢ A) → A ≡ A' → Derivable (Γ ⊢ A == A')
congTyRefl dA refl = TyRefl dA

congTmRefl : {Γ : Ctx n} {A : TyExpr n} {u u' : TmExpr n} → Derivable (Γ ⊢ u :> A) → u ≡ u' → Derivable (Γ ⊢ u == u' :> A)
congTmRefl du refl = TmRefl du

CtxRefl : {Γ : Ctx n} → ⊢ Γ → ⊢ Γ == Γ
CtxRefl {Γ = ◇} tt = tt
CtxRefl {Γ = Γ , A} (dΓ , dA) = (CtxRefl dΓ , dA , dA , TyRefl dA , TyRefl dA)

MorRefl : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ δ == δ ∷> Δ)
MorRefl {Δ = ◇} {δ = ◇} dδ = tt
MorRefl {Δ = Δ , B} {δ = δ , u} (dδ , du) = MorRefl dδ , TmRefl du

congMorRefl : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → δ ≡ δ' → Γ ⊢ δ ∷> Δ → Γ ⊢ δ == δ' ∷> Δ
congMorRefl refl dδ = MorRefl dδ


{- Substitution and weakening are admissible -}

SubstTy : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → Derivable (Γ ⊢ A [ δ ]Ty)
SubstTm : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ u :> A) → Γ ⊢ δ ∷> Δ → Derivable (Γ ⊢ u [ δ ]Tm :> A [ δ ]Ty)
SubstTyEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ A == A') → Γ ⊢ δ ∷> Δ → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ ]Ty)
SubstTmEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u' [ δ ]Tm :> A [ δ ]Ty)
SubstTyMorEq : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m} → Derivable (Δ ⊢ A) → (Γ ⊢ δ ∷> Δ)
       → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A [ δ' ]Ty)
SubstTmMorEq : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m} →  Derivable (Δ ⊢ u :> A) → (Γ ⊢ δ ∷> Δ) 
       → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u [ δ' ]Tm :> A [ δ ]Ty)
       

WeakTy' : (k : Fin (suc n)) {Γ : Ctx n} (T : TyExpr (n -F' k)) {A : TyExpr n}
     → Derivable (Γ ⊢ A) → Derivable (weakenCtx k Γ T ⊢ weakenTy' k A)
WeakTm' : (k : Fin (suc n)) {Γ : Ctx n} (T : TyExpr (n -F' k)) {u : TmExpr n} {A : TyExpr n}
     → Derivable (Γ ⊢ u :> A) → Derivable (weakenCtx k Γ T ⊢ weakenTm' k u :> weakenTy' k A)
WeakTyEq' : (k : Fin (suc n)) {Γ : Ctx n} (T : TyExpr (n -F' k)) {A A' : TyExpr n}
     → Derivable (Γ ⊢ A == A') → Derivable (weakenCtx k Γ T ⊢ weakenTy' k A == weakenTy' k A')
WeakTmEq' : (k : Fin (suc n)) {Γ : Ctx n} (T : TyExpr (n -F' k)) {u u' : TmExpr n} {A : TyExpr n}
     → Derivable (Γ ⊢ u == u' :> A) → Derivable (weakenCtx k Γ T ⊢ weakenTm' k u == weakenTm' k u' :> weakenTy' k A)

WeakMor : {Γ : Ctx n} {Δ : Ctx m} (T : TyExpr n) {δ : Mor n m} → Γ ⊢ δ ∷> Δ → (Γ , T) ⊢ weakenMor δ ∷> Δ
WeakMor {Δ = ◇} _ {δ = ◇} tt = tt
WeakMor {Δ = Δ , B} T  {δ = δ , u} (dδ , du) = (WeakMor T dδ , congTm (weaken[]Ty B δ last) refl (WeakTm' last T du))

WeakMorEq : {Γ : Ctx n } {Δ : Ctx m} (T : TyExpr n) {δ δ' : Mor n m} → (Γ ⊢ δ == δ' ∷> Δ) → ((Γ , T) ⊢ weakenMor δ == weakenMor δ' ∷> Δ)
WeakMorEq {Δ = ◇} _ {δ = ◇} {◇} dδ = tt
WeakMorEq {Δ = Δ , B} T {δ = δ , u} {δ' , u'} (dδ , du) = (WeakMorEq T dδ) , congTmEqTy (weaken[]Ty B δ last) (WeakTmEq' last T du)

weakenDerLast : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} {A : TyExpr m } → Derivable (Δ ⊢ A) → (Γ ⊢ δ ∷> Δ) → Derivable ((Γ , (A [ δ ]Ty)) ⊢ var last :> (A [ weakenMor δ ]Ty))
weakenDerLast {Γ = Γ} {δ = δ} {A = A} dA dδ rewrite ! (weaken[]Ty A δ last) = VarLast (SubstTy dA dδ)


SubstTy {A = pi A B} (Pi dA dB) dδ = Pi (SubstTy dA dδ) (SubstTy dB (WeakMor (A [ _ ]Ty) dδ , weakenDerLast dA dδ))
SubstTy {A = uu} UU dδ = UU
SubstTy {A = el v} (El dA) dδ = El (SubstTm dA dδ)

SubstTm (Conv dA du dA=) dδ = Conv (SubstTy dA dδ) (SubstTm du dδ) (SubstTyEq dA= dδ)
SubstTm {Δ = (Δ , A)} {var last} {δ = δ , u} (VarLast {A = A'} dA) (dδ , du) rewrite weakenTyInsert A δ u = du
SubstTm {Δ = (Δ , B)} {u = var (prev k)} {δ = δ , u} (VarPrev {A = A} _ dk) (dδ , du) rewrite weakenTyInsert A δ u = SubstTm dk dδ
SubstTm {u = lam A B u} (Lam dA dB du) dδ = Lam (SubstTy dA dδ) ((SubstTy dB (WeakMor (A [ _ ]Ty) dδ , weakenDerLast dA dδ))) (SubstTm du (WeakMor (A [ _ ]Ty) dδ , weakenDerLast dA dδ ))
SubstTm {u = app A B f a} {δ = δ} (App dA dB df da) dδ rewrite ! (substCommutes[]Ty B a δ)=  App (SubstTy dA  dδ) (SubstTy dB (WeakMor (A [ δ ]Ty) dδ , weakenDerLast dA dδ)) (SubstTm df dδ) (SubstTm da dδ)


SubstTyEq {A = A} (TySymm dA=) dδ = TySymm (SubstTyEq dA= dδ)
SubstTyEq {A = A} (TyTran dB dA= dB=) dδ = TyTran (SubstTy dB dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= dδ)
SubstTyEq {A = pi A B} (PiCong dA dA= dB=) dδ = PiCong (SubstTy dA  dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor (A [ _ ]Ty) dδ , weakenDerLast dA dδ))
SubstTyEq {A = uu} UUCong dδ = UUCong
SubstTyEq {A = el v} (ElCong dv=) dδ = ElCong (SubstTmEq dv= dδ)

SubstTmEq {δ = δ , u} (VarLastCong {A = A} dA=) (_ , du) rewrite weakenTyInsert A δ u = TmRefl du
SubstTmEq {δ = δ , u} (VarPrevCong {A = A} _ dA=) (dδ , du) rewrite weakenTyInsert A δ u = SubstTmEq dA= dδ 
SubstTmEq (TmSymm du=) dδ = TmSymm (SubstTmEq du= dδ)
SubstTmEq (TmTran du= dv=) dδ = TmTran (SubstTmEq du= dδ) (SubstTmEq dv= dδ)
SubstTmEq (ConvEq dA du= dA=) dδ = ConvEq (SubstTy dA dδ) (SubstTmEq du= dδ) (SubstTyEq dA= dδ) 
SubstTmEq (LamCong dA dA= dB= du=) dδ = LamCong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor _ dδ , weakenDerLast dA dδ)) (SubstTmEq du= ((WeakMor _ dδ) , (weakenDerLast dA dδ)))
SubstTmEq {δ = δ} (AppCong {B = B} {a = a} dA dA= dB= df= da=) dδ rewrite ! (substCommutes[]Ty B a δ)= AppCong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor _ dδ , weakenDerLast dA dδ)) (SubstTmEq df= dδ) (SubstTmEq da= dδ) 
SubstTmEq  {δ = δ} (Beta {B = B} {u = u} {a = a} dA dB du da) dδ rewrite ! (substCommutes[]Ty B a δ) | ! (substCommutes[]Tm u a δ) = Beta (SubstTy dA dδ) (SubstTy dB (WeakMor _ dδ , weakenDerLast dA dδ)) (SubstTm du (WeakMor _ dδ , weakenDerLast dA dδ )) (SubstTm da dδ)


SubstTyMorEq {Δ = Δ} {pi A B} (Pi dA dB) dδ dδ= = PiCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB ((WeakMor (A [ _ ]Ty) dδ) , (weakenDerLast dA dδ)) ((WeakMorEq (A [ _ ]Ty) dδ=) , congTmRefl (weakenDerLast dA dδ) refl))
SubstTyMorEq {A = uu} dA dδ dδ= = UUCong
SubstTyMorEq {A = el v} (El dv) dδ dδ= = ElCong (SubstTmMorEq dv dδ dδ=)

SubstTmMorEq {u = var last} {δ = δ , u} {δ' = δ' , u'} (VarLast {A = A} dA) dδ (dδ= , du=) rewrite weakenTyInsert A δ u = du=
SubstTmMorEq {u = var (prev x)} {δ = δ , u} {δ' = δ' , u'} (VarPrev _ dk) (dδ , du) (dδ= , du=) = congTmEqTy (! (weakenTyInsert _ δ u)) (SubstTmMorEq dk dδ dδ=)
SubstTmMorEq {u = u} (Conv dA du dA=) dδ dδ= = ConvEq (SubstTy dA dδ) (SubstTmMorEq du dδ dδ=) (SubstTyEq dA= dδ)
SubstTmMorEq {u = lam A B u} (Lam dA dB du) dδ dδ= = LamCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB ((WeakMor (A [ _ ]Ty) dδ) , (weakenDerLast dA dδ)) (WeakMorEq (A [ _ ]Ty) dδ= , congTmRefl (weakenDerLast dA dδ) refl)) (SubstTmMorEq du ((WeakMor (A [ _ ]Ty) dδ) , (weakenDerLast dA dδ)) ((WeakMorEq (A [ _ ]Ty) dδ=) , TmRefl (weakenDerLast dA dδ)))
SubstTmMorEq {u = app A B f a} {δ = δ} (App dA dB df da) dδ dδ= rewrite ! (substCommutes[]Ty B a δ) = AppCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB ((WeakMor (A [ δ ]Ty) dδ) , (weakenDerLast dA dδ)) ((WeakMorEq (A [ δ ]Ty) dδ=) , (TmRefl (weakenDerLast dA dδ)))) (SubstTmMorEq df dδ dδ=) (SubstTmMorEq da dδ dδ=)


WeakTy' k T {A = pi A B} (Pi dA dB) = Pi (WeakTy' k T dA) (WeakTy' (prev k) T dB)
WeakTy' k T {A = uu} UU = UU
WeakTy' k T {A = el v} (El dv) = El (WeakTm' k T dv)

WeakTyEq' k T (TySymm dA=) = TySymm (WeakTyEq' k T dA=)
WeakTyEq' k T (TyTran dB dA= dB=) = TyTran (WeakTy' k T dB) (WeakTyEq' k T dA=) (WeakTyEq' k T dB=)
WeakTyEq' k T (PiCong dA dA= dB=) = PiCong (WeakTy' k T dA) (WeakTyEq' k T dA=) (WeakTyEq' (prev k) T dB=)
WeakTyEq' k T UUCong = UUCong
WeakTyEq' k T (ElCong dv=) = ElCong (WeakTmEq' k T dv=)


WeakTm' k T (Conv dA du dA=) = Conv (WeakTy' k T dA) (WeakTm' k T du) (WeakTyEq' k T dA=) 
WeakTm' last {Γ , A} T {u = var x} (VarLast dA) = VarPrev (WeakTy' last A dA) (VarLast dA)
WeakTm' (prev k) T {u = var last} (VarLast {A = A} dA) rewrite ! (weakenTyCommutes k A) = VarLast (WeakTy' k T dA)
WeakTm' last T {u = var (prev x)} (VarPrev dA dk) = VarPrev (WeakTy' last _ dA) (VarPrev dA dk)
WeakTm' (prev k) T {u = var (prev x)} (VarPrev {A = A} dA dk) rewrite ! (weakenTyCommutes k A) = VarPrev (WeakTy' k T dA) (WeakTm' k T dk)
WeakTm' k T {u = lam A B u} (Lam dA dB du) = Lam (WeakTy' k T dA) (WeakTy' (prev k) T dB) (WeakTm' (prev k) T du)
WeakTm' k T {u = app A B f a} (App dA dB df da) rewrite ! (weakenCommutesSubstTy k B a) = App (WeakTy' k T dA) (WeakTy' (prev k) T dB) (WeakTm' k T df) (WeakTm' k T da)

WeakTmEq' last T  {u = var last} {var last} (VarLastCong dA) = VarPrevCong (WeakTy' last _ dA) (VarLastCong dA)
WeakTmEq' (prev k) T {u = var last} {var last} (VarLastCong {A = A} dA) rewrite ! (weakenTyCommutes k A) = VarLastCong (WeakTy' k T dA)
WeakTmEq' last T {u = var (prev x)} (VarPrevCong dA dk=) = VarPrevCong (WeakTy' last _ dA) (WeakTmEq' last _ dk=)
WeakTmEq' (prev k) T {u = var (prev x)} (VarPrevCong {A = A} dA dk=) rewrite ! (weakenTyCommutes k A) = VarPrevCong (WeakTy' k T dA) (WeakTmEq' k T dk=)
WeakTmEq' k T {u = u} (TmSymm du=) = TmSymm (WeakTmEq' k T du=)
WeakTmEq' k T {u = u} (TmTran du= dv=) = TmTran (WeakTmEq' k T du=) (WeakTmEq' k T dv=)
WeakTmEq' k T {u = u} (ConvEq dA du= dA=) = ConvEq (WeakTy' k T dA) (WeakTmEq' k T du=) (WeakTyEq' k T dA=)
WeakTmEq' k T {u = lam A B u} (LamCong dA dA= dB= du=) = LamCong (WeakTy' k T dA) (WeakTyEq' k T dA=) (WeakTyEq' (prev k) T dB=) (WeakTmEq' (prev k) T du=)
WeakTmEq' k T {u = app A B f a} (AppCong dA dA= dB= df= da=) rewrite ! (weakenCommutesSubstTy k B a) = AppCong (WeakTy' k T dA) (WeakTyEq' k T dA=) (WeakTyEq' (prev k) T dB=) (WeakTmEq' k T  df=) (WeakTmEq' k T da=)
WeakTmEq' k T {u = app A B (lam A B u) a} (Beta dA dB du da) rewrite ! (weakenCommutesSubstTy k B a) | ! (weakenCommutesSubstTm k u a)= Beta (WeakTy' k T dA) (WeakTy' (prev k) T dB) (WeakTm' (prev k) T du) (WeakTm' k T da)

WeakTy : {Γ : Ctx n}  (T : TyExpr n) {A : TyExpr n} → Derivable (Γ ⊢ A) → Derivable ((Γ , T) ⊢ weakenTy A)
WeakTm : {Γ : Ctx n} (T : TyExpr n) {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → Derivable ((Γ , T)  ⊢ weakenTm u :> weakenTy A)
WeakTyEq : {Γ : Ctx n} (T : TyExpr n) {A A' : TyExpr n} → Derivable (Γ ⊢ A == A') → Derivable ((Γ , T) ⊢ weakenTy A == weakenTy A')
WeakTmEq : {Γ : Ctx n} (T : TyExpr n) {u u' : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u == u' :> A) → Derivable ((Γ , T) ⊢ weakenTm u == weakenTm u' :> weakenTy A)

WeakTy = WeakTy' last
WeakTm = WeakTm' last
WeakTyEq = WeakTyEq' last
WeakTmEq = WeakTmEq' last


SubstMor : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ : Mor m k} {δ : Mor n m} → (Δ ⊢ θ ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ θ [ δ ]Mor ∷> Θ)
SubstMor {Θ = ◇} {θ = ◇} tt dδ = tt
SubstMor {Θ = Θ , C} {θ = θ , w} (dθ , dw) dδ = (SubstMor dθ dδ , congTm ([]Ty-assoc _ θ C) refl (SubstTm dw dδ))

SubstMorEq : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ θ' : Mor m k} {δ : Mor n m} → (Δ ⊢ θ == θ' ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ' [ δ ]Mor ∷> Θ)
SubstMorEq {Θ = ◇} {θ = ◇} {θ' = ◇} dθ= dδ = tt
SubstMorEq {Θ = Θ , C} {θ = θ , w} {θ' = θ' , w'} (dθ= , dw) dδ = SubstMorEq dθ= dδ , congTmEqTy ([]Ty-assoc _ θ C) (SubstTmEq dw dδ)


SubstMorMorEq : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ : Mor m k} {δ δ' : Mor n m} → (Δ ⊢ θ ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ [ δ' ]Mor ∷> Θ)
SubstMorMorEq {Θ = ◇} {◇} tt dδ dδ= = tt
SubstMorMorEq {Θ = Θ , C} {θ , w} (dθ , dw) dδ dδ= = SubstMorMorEq dθ dδ dδ= , congTmEqTy ([]Ty-assoc _ θ C) (SubstTmMorEq dw dδ dδ=)


{- Derivability of the identity morphism -}

idMorDerivable : {Γ : Ctx n} →  ⊢ Γ → (Γ ⊢ idMor n ∷> Γ)
idMorDerivable {Γ = ◇} tt = tt
idMorDerivable {Γ = Γ , A} (dΓ , dA) = WeakMor A (idMorDerivable dΓ) , congTm (ap weakenTy (! ([idMor]Ty A)) ∙ weaken[]Ty A (idMor _) last) refl (VarLast dA)


{- Conversion rules for types and terms are admissible -}

ConvTy : {Γ Δ : Ctx n} {A : TyExpr n} → Derivable (Γ ⊢ A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ A)
ConvTyEq : {Γ Δ : Ctx n} {A B : TyExpr n} → Derivable (Γ ⊢ A == B) → (⊢ Γ == Δ) → Derivable (Δ ⊢ A == B)
ConvTm : {Γ Δ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ u :> A)
ConvTmEq : {Γ Δ : Ctx n} {A : TyExpr n} {u v : TmExpr n} → Derivable (Γ ⊢ u == v :> A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ u == v :> A)

ConvTy {Γ = Γ} {Δ = Δ} {A = A} (Pi dA dB) dΓ= = Pi (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
ConvTy UU dΓ= = UU
ConvTy (El dv) dΓ= = El (ConvTm dv dΓ=)

ConvTyEq (TySymm dA=) dΓ= = TySymm (ConvTyEq dA= dΓ=)
ConvTyEq (TyTran dB dA= dB=) dΓ= = TyTran (ConvTy dB dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= dΓ=)
ConvTyEq (PiCong dA dA= dB=) dΓ= = PiCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
ConvTyEq UUCong dΓ= = UUCong
ConvTyEq (ElCong dv=) dΓ= = ElCong (ConvTmEq dv= dΓ=)

ConvTm {Δ = Δ , B} {var last} (VarLast {A = A} dA) (dΓ= , dA' , dB , dA= , dA=') = Conv (WeakTy B dB) (VarLast dB) (WeakTyEq B (TySymm dA='))
ConvTm {Γ = Γ , A} {Δ = Δ , B} (VarPrev dA dk) (dΓ= , dA , dB , dA=) = VarPrev (ConvTy dA dΓ=) (ConvTm dk dΓ=)
ConvTm (Conv dA du dA=) dΓ= = Conv (ConvTy dA dΓ=) (ConvTm du dΓ=) (ConvTyEq dA= dΓ=)
ConvTm (Lam dA dB du) dΓ= = Lam (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm du (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
ConvTm (App dA dB df da) dΓ= = App (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm df dΓ=) (ConvTm da dΓ=)

ConvTmEq  {Δ = Δ , B} (VarLastCong {A = A} dA) (dΓ= , dA' , dB , dA= , dA=') = ConvEq (WeakTy B dB) (VarLastCong dB) (WeakTyEq B (TySymm dA='))
ConvTmEq {Γ = Γ , B} {Δ , B'} (VarPrevCong {A = A} dA dk=) (dΓ= , dA , dB , dA=) = VarPrevCong (ConvTy dA dΓ=) (ConvTmEq dk= dΓ=)
ConvTmEq (TmSymm du=) dΓ= = TmSymm (ConvTmEq du= dΓ=)
ConvTmEq (TmTran du= dv=) dΓ= = TmTran (ConvTmEq du= dΓ=) (ConvTmEq dv= dΓ=)
ConvTmEq (ConvEq dA du= dA=) dΓ= = ConvEq (ConvTy dA dΓ=) (ConvTmEq du= dΓ=) (ConvTyEq dA= dΓ=)
ConvTmEq (LamCong dA dA= dB= du=) dΓ= = LamCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq du= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
ConvTmEq (AppCong dA dA= dB= df= da=) dΓ= = AppCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq df= dΓ=) (ConvTmEq da= dΓ=)
ConvTmEq (Beta dA dB du da) dΓ= = Beta (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm du (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm da dΓ=)


{- Various other admissible rules -}

CtxSymm : {Γ Δ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Γ
CtxSymm {Γ = ◇} {Δ = ◇} tt = tt
CtxSymm {Γ = Γ , A} {Δ , B} (dΓ= , dA , dB , dA= , dA=') = (CtxSymm dΓ=) , dB , dA , TySymm dA=' , TySymm dA=

CtxTran : {Γ Δ Θ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Θ → ⊢ Γ == Θ
CtxTran {Γ = ◇} {Δ = ◇} {Θ = ◇} tt tt = tt
CtxTran {Γ = Γ , A} {Δ , B} {Θ , C} (dΓ= , dA , dB , dA= , dA=') (dΔ= , dB' , dC , dB= , dB=') = CtxTran dΓ= dΔ= , dA , dC , TyTran (ConvTy dB (CtxSymm dΓ=)) dA= (ConvTyEq dB= (CtxSymm dΓ=)) , TyTran (ConvTy dB dΔ=) (ConvTyEq dA=' dΔ=) dB='


CtxEqCtx1 : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' → ⊢ Γ
CtxEqCtx1 {Γ = ◇} {Γ' = ◇} tt = tt
CtxEqCtx1 {Γ = Γ , A} {Γ' , A'} (dΓ= , dA , dA' , dA=) = (CtxEqCtx1 dΓ=) , dA

CtxEqCtx2 : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' → ⊢ Γ'
CtxEqCtx2 {Γ = ◇} {Γ' = ◇} tt = tt
CtxEqCtx2 {Γ = Γ , A} {Γ' = Γ' , A'} (dΓ= , dA , dA' , dA=) = CtxEqCtx2 dΓ= , dA'


TyEqTy1 : {Γ : Ctx n} {A B : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A)
TyEqTy2 : {Γ : Ctx n} {A B : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B)
TmEqTm1 : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u :> A)
TmEqTm2 : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u' :> A)

TyEqTy1 dΓ (TySymm dA=) = TyEqTy2 dΓ dA=
TyEqTy1 dΓ (TyTran dB dA= dB=) = TyEqTy1 dΓ dA=
TyEqTy1 dΓ (PiCong dA dA= dB=) = Pi dA (TyEqTy1 (dΓ , dA) dB=)
TyEqTy1 dΓ UUCong = UU
TyEqTy1 dΓ (ElCong dv=) = El (TmEqTm1 dΓ dv=) 

TyEqTy2 dΓ (TySymm dA=) = TyEqTy1 dΓ dA=
TyEqTy2 dΓ (TyTran dB dA= dB=) = TyEqTy2 dΓ dB=
TyEqTy2 dΓ (PiCong dA dA= dB=) = Pi (TyEqTy2 dΓ dA=) (ConvTy (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) ((CtxRefl dΓ) , dA , TyEqTy2 dΓ dA= , dA= , dA=))
TyEqTy2 dΓ UUCong = UU
TyEqTy2 dΓ (ElCong dv=) = El (TmEqTm2 dΓ dv=)

TmEqTm1 dΓ (VarLastCong dA) = VarLast dA
TmEqTm1 (dΓ , dA) (VarPrevCong dA' dk=) = VarPrev dA' (TmEqTm1 dΓ dk=)
TmEqTm1 dΓ (TmSymm du=) = TmEqTm2 dΓ du= 
TmEqTm1 dΓ (TmTran du= dv=) = TmEqTm1 dΓ du=
TmEqTm1 dΓ (ConvEq dA du= dA=) = Conv dA (TmEqTm1 dΓ du=) dA=
TmEqTm1 dΓ (LamCong dA dA= dB= du=) = Lam (TyEqTy1 dΓ dA=) (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 (dΓ , dA) du=)
TmEqTm1 dΓ (AppCong dA dA= dB= df= da=) = App (TyEqTy1 dΓ dA=) (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 dΓ df=) (TmEqTm1 dΓ da=)
TmEqTm1 dΓ (Beta dA dB du da) = App dA dB (Lam dA dB du) da

TmEqTm2 dΓ (VarLastCong dA) = VarLast dA
TmEqTm2 (dΓ , dA) (VarPrevCong dA' dk=) = VarPrev dA' (TmEqTm2 dΓ dk=)
TmEqTm2 dΓ (TmSymm du=) = TmEqTm1 dΓ du=
TmEqTm2 dΓ (TmTran du= dv=) = TmEqTm2 dΓ dv=
TmEqTm2 dΓ (ConvEq dA du= dA=) =  Conv dA (TmEqTm2 dΓ du=) dA=
TmEqTm2 dΓ (LamCong dA dA= dB= du=) = Conv
             (Pi
               (TyEqTy2 dΓ dA=)
               (ConvTy (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) ((CtxRefl dΓ) , dA , TyEqTy2 dΓ dA= , dA= , dA=))
             )
             (Lam
               (TyEqTy2 dΓ dA=)
               (ConvTy (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) ((CtxRefl dΓ) , dA , TyEqTy2 dΓ dA= , dA= , dA=))
               (ConvTm (Conv (TyEqTy1 (dΓ , dA) dB=) (TmEqTm2 (dΓ , dA) du=) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=)))
             (PiCong
               (TyEqTy2 dΓ dA=)
               (TySymm dA=)
               (ConvTyEq (TySymm dB=) (CtxRefl dΓ , dA , ConvTy (TyEqTy2 dΓ dA=) (CtxRefl dΓ) , dA= , dA=))
             )             
TmEqTm2 dΓ (AppCong dA dA= dB= df= da=) = Conv
             (SubstTy (TyEqTy2 (dΓ , dA) dB=) ((idMorDerivable dΓ) , (Conv dA (TmEqTm2 dΓ da=) (congTyEq refl (! ([idMor]Ty _)) (TyRefl dA)))))
             (App
               (TyEqTy2 dΓ dA=)
               (ConvTy (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) ((CtxRefl dΓ) , dA , TyEqTy2 dΓ dA= , dA= , dA=))
               (Conv (Pi dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ df=) (PiCong dA dA= dB=))
               (Conv dA (TmEqTm2 dΓ da=) dA=)
             )
             (TyTran
               (SubstTy (TyEqTy1 (dΓ , dA) dB=) ((idMorDerivable dΓ) , (Conv dA (TmEqTm2 dΓ da=) (congTyEq refl (! ([idMor]Ty _)) (TyRefl dA)))))
               (SubstTyEq
                 (TySymm dB=)
                 ((idMorDerivable dΓ) , (Conv dA (TmEqTm2 dΓ da=) (congTyEq refl (! ([idMor]Ty _)) (TyRefl dA))))
               )
               (SubstTyMorEq
                 (TyEqTy1 (dΓ , dA) dB=)
                 ((idMorDerivable dΓ) , (Conv dA (TmEqTm2 dΓ da=) (congTyEq refl (! ([idMor]Ty _)) (TyRefl dA))))
                 (MorRefl (idMorDerivable dΓ) , congTmEqTy (! ([idMor]Ty _)) (TmSymm da=))
               )
             )
TmEqTm2 dΓ (Beta dA dB du da) = SubstTm du ((idMorDerivable dΓ) , (Conv dA da (congTyEq refl (!([idMor]Ty _)) (TyRefl dA))))


MorEqMor1 : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → (⊢ Γ) → (⊢ Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ δ ∷> Δ)
MorEqMor2 : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → (⊢ Γ) → (⊢ Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ δ' ∷> Δ)

MorEqMor1 {Δ = ◇} {δ = ◇} {◇} _ _ dδ= = tt
MorEqMor1 {Δ = Δ , B} {δ = δ , u} {δ' , u'} dΓ (dΔ , _) (dδ= , du=) = (MorEqMor1 dΓ dΔ dδ=) , TmEqTm1 dΓ du=

MorEqMor2 {Δ = ◇} {δ = ◇} {◇} _ _ dδ= = tt
MorEqMor2 {Δ = Δ , B} {δ = δ , u} {δ' , u'} dΓ (dΔ , dB) (dδ= , du=) = (MorEqMor2 dΓ dΔ dδ=) , Conv (SubstTy dB (MorEqMor1 dΓ dΔ dδ=)) (TmEqTm2 dΓ du=) (SubstTyMorEq dB (MorEqMor1 dΓ dΔ dδ=) dδ=)


MorSymm : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → ⊢ Γ → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ ∷> Δ
MorSymm {Δ = ◇} {◇} {◇} _ _ tt = tt
MorSymm {Δ = Δ , B} {δ , u} {δ' , u'} dΓ (dΔ , dB) (dδ , du) = MorSymm dΓ dΔ dδ , ConvEq (SubstTy dB (MorEqMor1 dΓ dΔ dδ)) (TmSymm du) (SubstTyMorEq dB (MorEqMor1 dΓ dΔ dδ) dδ)

MorTran : {Γ : Ctx n} {Δ : Ctx m} {δ δ' δ'' : Mor n m} → ⊢ Γ → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ'' ∷> Δ → Γ ⊢ δ == δ'' ∷> Δ
MorTran {Δ = ◇} {◇} {◇} {◇} _ _ tt tt = tt
MorTran {Δ = Δ , B} {δ , u} {δ' , u'} {δ'' , u''} dΓ (dΔ , dB) (dδ , du) (dδ' , du') = (MorTran dΓ dΔ dδ dδ') , TmTran du (ConvEq (SubstTy dB (MorEqMor2 dΓ dΔ dδ)) du' (SubstTyMorEq dB (MorEqMor2 dΓ dΔ dδ) (MorSymm dΓ dΔ dδ)))


DerTmTy : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A)
DerTmTy dΓ (VarLast dA) = WeakTy _ dA
DerTmTy (dΓ , dB) (VarPrev dA dk) = WeakTy _ (DerTmTy dΓ dk)
DerTmTy dΓ (Conv dA du dA=) = TyEqTy2 dΓ dA=
DerTmTy dΓ (Lam dA dB du) = Pi dA dB
DerTmTy dΓ (App dA dB df da) = SubstTy dB ((idMorDerivable dΓ) , congTm (! ([idMor]Ty _)) refl da)


ConvTm2 : {Γ Δ : Ctx n} {u : TmExpr n} {A A' : TyExpr n} → Derivable (Γ ⊢ u :> A) → (⊢ Γ == Δ) → Derivable (Γ ⊢ A == A') → Derivable (Δ ⊢ u :> A')
ConvTm2 du dΓ= dA= = ConvTm (Conv (DerTmTy (CtxEqCtx1 dΓ=) du) du dA=) dΓ=

ConvTmEq2 : {Γ Δ : Ctx n} {u u' : TmExpr n} {A A' : TyExpr n} → Derivable (Γ ⊢ u == u' :> A) → (⊢ Γ == Δ) → Derivable (Γ ⊢ A == A') → Derivable (Δ ⊢ u == u' :> A')
ConvTmEq2 du= dΓ= dA= = ConvTmEq (ConvEq (TyEqTy1 (CtxEqCtx1 dΓ=) dA=) du= dA=) dΓ=

ConvMor : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ : Mor n m} → (Γ ⊢ δ ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ ∷> Δ')
ConvMor {Δ = ◇} {Δ' = ◇} {δ = ◇} dδ dΓ= dΔ= = tt
ConvMor {Δ = Δ , B} {Δ' = Δ' , B'} {δ = δ , u} (dδ , du) dΓ= (dΔ= , dB , dB' ,  dB= , dB=') =
        ConvMor dδ dΓ= dΔ= , Conv (ConvTy (SubstTy dB dδ) dΓ=) (ConvTm du dΓ=) (SubstTyEq dB= (ConvMor dδ dΓ= (CtxRefl (CtxEqCtx1 dΔ=))))

ConvMorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} → (Γ ⊢ δ == δ' ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ == δ' ∷> Δ')
ConvMorEq {Δ = ◇} {Δ' = ◇} {δ = ◇} {◇} dδ= dΓ= dΔ= = tt
ConvMorEq {Δ = Δ , B} {Δ' = Δ' , B'} {δ = δ , u} {δ' , u₁} (dδ= , du=) dΓ= (dΔ= , dB , dB' , dB= , dB=') = (ConvMorEq dδ= dΓ= dΔ=) , ConvTmEq (ConvEq (SubstTy dB (MorEqMor1 (CtxEqCtx1 dΓ=) (CtxEqCtx1 dΔ=) dδ=)) du= (SubstTyEq dB= (MorEqMor1 (CtxEqCtx1 dΓ=) (CtxEqCtx1 dΔ=) dδ=))) dΓ=

eqMorDer : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' → Γ' ⊢ idMor n ∷> Γ
eqMorDer dΓ= = ConvMor (idMorDerivable (CtxEqCtx1 dΓ=)) dΓ= (CtxRefl (CtxEqCtx1 dΓ=))

-- Should those functions be replaced by [SubstTyMorEq2]?
SubstTyFullEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m} → Derivable (Δ ⊢ A') → (Γ ⊢ δ ∷> Δ)
       → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
SubstTyFullEq dA' dδ dA= dδ= = TyTran (SubstTy dA' dδ) (SubstTyEq dA= dδ) (SubstTyMorEq dA' dδ dδ=)

SubstTmFullEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m} →  Derivable (Δ ⊢ u' :> A) → (Γ ⊢ δ ∷> Δ) 
       → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u' [ δ' ]Tm :> A [ δ ]Ty)
SubstTmFullEq du' dδ du= dδ= = TmTran (SubstTmEq du= dδ) (SubstTmMorEq du' dδ dδ=)

SubstMorFullEq : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ θ' : Mor m k} {δ δ' : Mor n m} → (⊢ Δ) → (⊢ Θ) → (Δ ⊢ θ' ∷> Θ) → (Δ ⊢ θ == θ' ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ' [ δ' ]Mor ∷> Θ)
SubstMorFullEq {Θ = ◇} {◇} {◇} dΔ tt dθ' tt dδ dδ= = tt
SubstMorFullEq {Θ = Θ , C} {θ , w} {θ' , w'} dΔ (dΘ , dC) (dθ' , dw') (dθ= , dw=) dδ dδ= = (SubstMorFullEq dΔ dΘ dθ' dθ= dδ dδ=) , congTmEqTy ([]Ty-assoc _ θ C) (SubstTmFullEq (Conv (SubstTy dC dθ') dw' (SubstTyMorEq dC dθ' (MorSymm dΔ dΘ dθ=))) dδ dw= dδ=) 

SubstTyMorEq2 : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m}
              → ⊢ Γ → ⊢ Δ → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
SubstTyMorEq2 dΓ dΔ dA= dδ= =
  let dδ = MorEqMor1 dΓ dΔ dδ=
      dA' = TyEqTy2 dΔ dA=
  in
  TyTran (SubstTy dA' dδ) (SubstTyEq dA= dδ) (SubstTyMorEq (TyEqTy2 dΔ dA=) dδ dδ=)

_,,_ : {Γ Γ' : Ctx n} {A A' : TyExpr n} → ⊢ Γ == Γ' → Derivable (Γ ⊢ A == A') → ⊢ (Γ , A) == (Γ' , A')
dΓ= ,, dA= =
  let dΓ = CtxEqCtx1 dΓ=
  in
  (dΓ= , TyEqTy1 dΓ dA= , ConvTy (TyEqTy2 dΓ dA=) dΓ= , dA= , ConvTyEq dA= dΓ=)
