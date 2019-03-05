{-# OPTIONS --rewriting --prop --without-K --no-auto-inline #-}

open import common
open import typetheory
open import syntx
open import rules
open import contextualcat
open import quotients

open CCat hiding (Mor) renaming (id to idC)

{- Preliminary definitions -}

record DCtx (n : ℕ) : Set where
  no-eta-equality
  constructor _,_
  field
    ctx : Ctx n
    der : ⊢ ctx
open DCtx public

record DMor (n m : ℕ) : Set where
  no-eta-equality
  constructor dmor
  field
    lhs : DCtx n
    rhs : DCtx m
    mor : Mor n m
    morDer : ctx lhs ⊢ mor ∷> ctx rhs
open DMor public

{-
Defining _Ob≃_ as a datatype as follows rather than being equal to ⊢ ctx Γ == ctx Γ'
allows us to have more arguments implicit.
The reason is that if you want to solve the definitional equality
   (Γ ≃ Γ') = (Δ ≃ Δ')
you get that Γ = Δ and Γ' = Δ' rather than simply ctx Γ = ctx Δ and ctx Γ' = ctx Δ'.
-}

data _Ob≃_ (Γ Γ' : DCtx n) : Prop where
  box : ⊢ ctx Γ == ctx Γ' → Γ Ob≃ Γ'

unOb≃ : {Γ Γ' : DCtx n} → Γ Ob≃ Γ' → ⊢ ctx Γ == ctx Γ'
unOb≃ (box x) = x

data _Mor≃_ (δ δ' : DMor n m) : Prop where
  box : ⊢ ctx (lhs δ) == ctx (lhs δ') → ⊢ ctx (rhs δ) == ctx (rhs δ') → ctx (lhs δ) ⊢ mor δ == mor δ' ∷> ctx (rhs δ) → δ Mor≃ δ'

unMor≃-lhs : {δ δ' : DMor n m} → δ Mor≃ δ' → ⊢ ctx (lhs δ) == ctx (lhs δ')
unMor≃-lhs (box x _ _) = x

unMor≃-rhs : {δ δ' : DMor n m} → δ Mor≃ δ' → ⊢ ctx (rhs δ) == ctx (rhs δ')
unMor≃-rhs (box _ x _) = x

unMor≃-mor : {δ δ' : DMor n m} → δ Mor≃ δ' → ctx (lhs δ) ⊢ mor δ == mor δ' ∷> ctx (rhs δ)
unMor≃-mor (box _ _ x) = x

instance
  ObEquiv : {n : ℕ} → EquivRel (DCtx n)
  EquivRel._≃_ ObEquiv Γ Γ' = Γ Ob≃ Γ'
  EquivRel.ref ObEquiv Γ = box (CtxRefl (der Γ))
  EquivRel.sym ObEquiv (box p) = box (CtxSymm p)
  EquivRel.tra ObEquiv (box p) (box q) = box (CtxTran p q)

  MorEquiv : {n m : ℕ} → EquivRel (DMor n m)
  EquivRel._≃_ MorEquiv δ δ' = δ Mor≃ δ'
  EquivRel.ref MorEquiv δ = box (CtxRefl (der (lhs δ))) (CtxRefl (der (rhs δ))) (MorRefl (morDer δ))
  EquivRel.sym MorEquiv (box Γ= Δ= δ=) = box (CtxSymm Γ=) (CtxSymm Δ=) (ConvMorEq (MorSymm (CtxEqCtx1 Γ=) (CtxEqCtx1 Δ=) δ=) Γ= Δ=)
  EquivRel.tra MorEquiv (box Γ= Δ= δ=) (box Γ'= Δ'= δ'=) = box (CtxTran Γ= Γ'=) (CtxTran Δ= Δ'=) (MorTran (CtxEqCtx1 Γ=) (CtxEqCtx1 Δ=) δ= (ConvMorEq δ'= (CtxSymm Γ=) (CtxSymm Δ=)))

reflectOb : {Γ Γ' : DCtx n} → proj {R = ObEquiv} Γ ≡ proj Γ' → ⊢ ctx Γ == ctx Γ'
reflectOb p = unOb≃ (reflect p)

DCtx= : {Γ Γ' : Ctx n} {w₁ : _} {w₂ : _} → Γ ≡ Γ' → proj {R = ObEquiv} (Γ , w₁) ≡ proj (Γ' , w₂)
DCtx= refl = refl

DMor= : {Γ Γ' : Ctx m} {w₁ : _} {w₂ : _} {Δ Δ' : Ctx n} {w₃ : _} {w₄ : _} {δ δ' : Mor m n} {w₅ : _} {w₆ : _} → Γ ≡ Γ' → Δ ≡ Δ' → δ ≡ δ' → proj {R = MorEquiv} (dmor (Γ , w₁) (Δ , w₃) δ w₅) ≡ proj (dmor (Γ' , w₂) (Δ' , w₄) δ' w₆)
DMor= refl refl refl = refl

idMor+ : {Γ : Ctx n} {A : TyExpr n} {a : TmExpr n} → ⊢ Γ → Derivable (Γ ⊢ a :> A) → Γ ⊢ (idMor n , a) ∷> (Γ , A)
idMor+ dΓ da = (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl da)

idMor+= : {Γ : Ctx n} {A : TyExpr n} {a a' : TmExpr n} → ⊢ Γ → Derivable (Γ ⊢ a == a' :> A) → Γ ⊢ (idMor n , a) == (idMor n , a') ∷> (Γ , A)
idMor+= dΓ da= = (MorRefl (idMorDerivable dΓ) , congTmEqTy (! ([idMor]Ty _)) da=)

{- helper function to extract data from DCtx/DMor -}
getCtx : (Γ : DCtx (suc n)) → Ctx n
getCtx ((Γ , _) , _) = Γ

getdCtx : (Γ : DCtx (suc n)) → ⊢ getCtx Γ
getdCtx ((_ , _) , (dΓ , _)) = dΓ

getTy' : Ctx (suc n) → TyExpr n
getTy' (Δ , B) = B

getTy : (X : DCtx (suc n)) → TyExpr n
getTy Δ = getTy' (ctx Δ)

getdTy : (Γ : DCtx (suc n)) → Derivable (getCtx Γ ⊢ getTy Γ)
getdTy ((_ , _) , (_ , dA)) = dA

getTm : (u : DMor m (suc n)) → TmExpr m
getTm u = getRHS (mor u)

getMor : (a : DMor m (suc n)) → Mor m n
getMor a = getLHS (mor a)

getdTm : (a : DMor m (suc n)) → Derivable (ctx (lhs a) ⊢ getTm a :> (getTy (rhs a) [ getMor a ]Ty))
getdTm (dmor _ ((_ , _) , _) (_ , _) (_ , da)) = da

getdMor : (a : DMor m (suc n)) → ctx (lhs a) ⊢ getMor a ∷> getCtx (rhs a)
getdMor (dmor _ ((_ , _) , _) (_ , _) (dδ , _)) = dδ



CtxTy=Ctx : {Γ : DCtx n} (A : DCtx (suc n)) (A= : proj {R = ObEquiv} (getCtx A , getdCtx A) ≡ proj Γ) → ⊢ ctx Γ , getTy A == ctx A
CtxTy=Ctx {Γ = Γ} A@((_ , _) , (_ , _)) A= = CtxSymm (reflectOb A=) ,, TyRefl (ConvTy (getdTy A) (reflectOb A=))

CtxTy=Ctx' : (Γ : DCtx (suc n)) → ⊢ (getCtx Γ , getTy Γ) == ctx Γ
CtxTy=Ctx' ((_ , _) , dΓ@(_ , _)) = CtxRefl dΓ

getCtx= : {Γ Γ' : DCtx (suc n)} (rΓ : Γ ≃ Γ') → ⊢ getCtx Γ == getCtx Γ'
getCtx= {Γ = (Γ , A) , _} {(Γ' , A') , _} (box (dΓ= , _ , _ , _ , _)) = dΓ=

getTy= : {Γ Γ' : DCtx (suc n)} (rΓ : Γ ≃ Γ') → Derivable (getCtx Γ  ⊢ getTy Γ == getTy Γ')
getTy= {Γ = (Γ , A) , (dΓ , A)} {(Γ' , A') , (dΓ' , dA')} (box (_ , _ , _ , dA= , _)) = dA=

dLHS : {Γ : Ctx m} {Δ : DCtx (suc n)} {δ : Mor m (suc n)} → Γ ⊢ δ ∷> ctx Δ → Γ ⊢ getLHS δ ∷> getCtx Δ
dLHS {Δ = (Δ , B) , (dΔ , dB)} {δ = δ , u} (dδ , du) = dδ

getLHS= : {Γ : Ctx m} {Δ : DCtx (suc n)} {δ δ' : Mor m (suc n)} → Γ  ⊢ δ == δ' ∷> ctx Δ → Γ ⊢ getLHS δ == getLHS δ' ∷> getCtx Δ
getLHS= {Δ = (Δ , B) , (dΔ , dB)} {δ = (δ , u)} {δ' = (δ' , u')} (dδ= , du=) = dδ=

getRHS= : {Γ : Ctx m} {Δ : Ctx (suc n)} {δ δ' : Mor m (suc n)} → Γ  ⊢ δ == δ' ∷> Δ → Derivable (Γ ⊢ getRHS δ == getRHS δ' :> (getTy' Δ [ getLHS δ ]Ty))
getRHS= {Δ = (Δ , B)} {δ = (δ , u)} {δ' = (δ' , u')} (dδ= , du=) = du=
