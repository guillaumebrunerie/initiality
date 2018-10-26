{-# OPTIONS --irrelevant-projections --allow-unsolved-metas #-}

open import common
open import syntx
open import contextualcat

module _ (C : StructuredCCat) where

open StructuredCCat C
open CCat ccat renaming (Mor to MorC)
open M ccat

{- Helper functions -}

shift : {X : Ob n} {X' : Ob (suc n)} .(p : ft X' ≡ X) → Ty X' 0 → Ty X 1
toCtx (shift p T) = toCtx T
toCtxEq (shift p T) = ap ft (toCtxEq T) ∙ p

shiftTm : {X : Ob n} {X' : Ob (suc n)} .(p : ft X' ≡ X) → Tm X' 0 → Tm X 1
getTy (shiftTm p t) = shift p (getTy t)
morTm (shiftTm p t) = morTm t
morTm₀ (shiftTm p t) = morTm₀ t
morTm₁ (shiftTm p t) = morTm₁ t
eqTm (shiftTm p t) = eqTm t

{- The partial interpretation functions -}

⟦_⟧ctx : (Γ : Ctx n) → Partial (Ob n)
⟦_⟧ty : TyExpr n → (X : Ob n) → Partial (Ty X 0)
⟦_⟧tm : TmExpr n → (X : Ob n) → Partial (Tm X 0)
⟦_⟧mor : (δ : Mor n m) (X : Ob n) (Y : Ob m) → Partial (MorC n m)


⟦ ◇ ⟧ctx = return pt
⟦ Γ , A ⟧ctx = do
  [Γ] ← ⟦ Γ ⟧ctx
  [A] ← ⟦ A ⟧ty [Γ]
  return (toCtx [A])

⟦ pi A B ⟧ty X = do
  [A] ← ⟦ A ⟧ty X
  [B] ← ⟦ B ⟧ty ([A] .toCtx)
  return (PiStr X [A] (shift (toCtxEq [A]) [B]) (ap-irr _,_ (toCtxEq [B])))
⟦ uu ⟧ty X = return (UUStr X)
⟦ el v ⟧ty X = do
  [v] ← ⟦ v ⟧tm X
  vTy ← assume (getTy [v] ≡P UUStr X)
  return (ElStr X [v] vTy)

⟦ var x ⟧tm X = return (M.var ccat x X)
⟦ lam A B u ⟧tm X = do
  [A] ← ⟦ A ⟧ty X
  [B] ← ⟦ B ⟧ty ([A] .toCtx)
  [u] ← ⟦ u ⟧tm ([A] .toCtx)

  uTy ← assume (getTy [u] ≡P [B])
  return (lamStr X [A] (shift (toCtxEq [A]) [B]) (shiftTm (toCtxEq [A]) [u]) (ap-irr _,_ (toCtxEq [B])) (ap (shift (toCtxEq [A])) uTy))
⟦ app A B f a ⟧tm X = do
  [A] ← ⟦ A ⟧ty X
  [B] ← ⟦ B ⟧ty ([A] .toCtx)
  [f] ← ⟦ f ⟧tm X
  [a] ← ⟦ a ⟧tm X

  fTy ← assume (getTy [f] ≡P PiStr X [A] (shift (toCtxEq [A]) [B]) (ap-irr _,_ (toCtxEq [B])))
  aTy ← assume (getTy [a] ≡P [A])
  return (appStr X [A] (shift (toCtxEq [A]) [B]) [f] [a] (ap-irr _,_ (toCtxEq [B])) fTy aTy)
     
⟦ ◇ ⟧mor X Y = return (ptmor X)
⟦ δ , u ⟧mor X Y = do
  [δ] ← ⟦ δ ⟧mor X (ft Y)
  [u] ← ⟦ u ⟧tm X
  
  ∂₁δ ← assume (∂₁ [δ] ≡P ft Y)
  uTy ← assume (∂₁ (morTm [u]) ≡P ∂₀ (qq [δ] Y ∂₁δ))
  return (comp (qq [δ] Y ∂₁δ) (morTm [u]) uTy)
