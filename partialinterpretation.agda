{-# OPTIONS --allow-unsolved-metas #-}

open import common
open import syntx
open import contextualcat

module _ (C : StructuredCCat) where

open StructuredCCat C
open CCat ccat renaming (Mor to MorC)
open M ccat

{- Helper functions -}

shift : {X : Ob n} {X' : Ob (k + n)} (p : ft^ k X' ≡ X) → Ty X' 0 → Ty X k
toCtx (shift p T) = toCtx T
toCtxEq (shift {k = k} p T) = ap (ft^ k) (toCtxEq T) ∙ p

shift! : {X : Ob n} (T : Ty X k) → Ty (ft (toCtx T)) 0
toCtx (shift! T) = toCtx T
toCtxEq (shift! {k = k} T) = refl

shiftTm : {X : Ob n} {X' : Ob (k + n)} (p : ft^ k X' ≡ X) → Tm X' 0 → Tm X k
getTy (shiftTm p t) = shift p (getTy t)
morTm (shiftTm p t) = morTm t
morTm₀ (shiftTm p t) = morTm₀ t
morTm₁ (shiftTm p t) = morTm₁ t
eqTm (shiftTm p t) = eqTm t

{- The partial interpretation functions -}

⟦_⟧Ty : TyExpr n → (X : Ob n) → Partial (Ty X 0)
⟦_⟧Tm : TmExpr n → (X : Ob n) → Partial (Tm X 0)

⟦ pi A B ⟧Ty X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty ([A] .toCtx)
  return (PiStr X [A] (shift (toCtxEq [A]) [B]) (ap-irr _,_ (toCtxEq [B])))
⟦ uu ⟧Ty X = return (UUStr X)
⟦ el v ⟧Ty X = do
  [v] ← ⟦ v ⟧Tm X
  vTy ← assume (getTy [v] ≡ UUStr X)
  return (ElStr X [v] (vTy .unbox))

⟦ var x ⟧Tm X = return (varC x X)
⟦ lam A B u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty ([A] .toCtx)
  [u] ← ⟦ u ⟧Tm ([A] .toCtx)

  uTy ← assume (getTy [u] ≡ [B])
  return (lamStr X [A] (shift (toCtxEq [A]) [B]) (shiftTm (toCtxEq [A]) [u]) (ap-irr _,_ (toCtxEq [B])) (ap (shift (toCtxEq [A])) (uTy .unbox)))
⟦ app A B f a ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty ([A] .toCtx)
  [f] ← ⟦ f ⟧Tm X
  [a] ← ⟦ a ⟧Tm X

  fTy ← assume (getTy [f] ≡ PiStr X [A] (shift (toCtxEq [A]) [B]) (ap-irr _,_ (toCtxEq [B])))
  aTy ← assume (getTy [a] ≡ [A])
  return (appStr X [A] (shift (toCtxEq [A]) [B]) [f] [a] (ap-irr _,_ (toCtxEq [B])) (fTy .unbox) (aTy .unbox))

{- We can now interpret contexts and context morphisms -}

⟦_⟧Ctx : (Γ : Ctx n) → Partial (Ob n)
⟦ ◇ ⟧Ctx = return pt
⟦ Γ , A ⟧Ctx = do
  [Γ] ← ⟦ Γ ⟧Ctx
  [A] ← ⟦ A ⟧Ty [Γ]
  return (toCtx [A])

⟦_⟧Mor : (δ : Mor n m) (X : Ob n) (Y : Ob m) → Partial (MorC n m)
⟦ ◇ ⟧Mor X Y = return (ptmor X)
⟦ δ , u ⟧Mor X Y = do
  [δ] ← ⟦ δ ⟧Mor X (ft Y)
  [u] ← ⟦ u ⟧Tm X
  
  ∂₁δ ← assume (∂₁ [δ] ≡ ft Y)
  uTy ← assume (toCtx (getTy [u]) ≡ star [δ] Y (∂₁δ .unbox))
  return (comp (qq [δ] Y (∂₁δ .unbox)) (morTm [u]) (morTm₁ [u] ∙ uTy .unbox ∙ ! qq₀))
