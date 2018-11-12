{-# OPTIONS --allow-unsolved-metas #-}

open import common
open import syntx
open import contextualcat

module _ (C : StructuredCCat) where

open StructuredCCat C
open CCat ccat renaming (Mor to MorC)

{- The partial interpretation functions -}

⟦_⟧Ty : TyExpr n → (X : Ob n) → Partial (Ob (suc n))
⟦_⟧Tm : TmExpr n → (X : Ob n) → Partial (MorC n (suc n))

⟦ pi A B ⟧Ty X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  return (PiStr [B])
⟦ uu ⟧Ty X = return (UUStr X)
⟦ el v ⟧Ty X = do
  [v] ← ⟦ v ⟧Tm X
  [v]s ← assume (is-section [v])
  [v]₁ ← assume (∂₁ [v] ≡ UUStr (∂₀ [v]))
  return (ElStr [v] (unbox [v]s) (unbox [v]₁))

⟦ var x ⟧Tm X = return {!!} --(varC x X)
⟦ lam A _ u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [u] ← ⟦ u ⟧Tm [A]
  [u]s ← assume (is-section [u])
  return (lamStr [u] (unbox [u]s))
⟦ app A B f a ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  [f] ← ⟦ f ⟧Tm X
  [f]s ← assume (is-section [f])
  [f]₁ ← assume (∂₁ [f] ≡ PiStr [B])
  [a] ← ⟦ a ⟧Tm X
  [a]s ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ ft [B])
  return (appStr [B] [f] (unbox [f]s) (unbox [f]₁) [a] (unbox [a]s) (unbox [a]₁))

{- We can now interpret contexts and context morphisms -}

⟦_⟧Ctx : (Γ : Ctx n) → Partial (Ob n)
⟦ ◇ ⟧Ctx = return pt
⟦ Γ , A ⟧Ctx = do
  [Γ] ← ⟦ Γ ⟧Ctx
  [A] ← ⟦ A ⟧Ty [Γ]
  return [A]

⟦_⟧Mor : (δ : Mor n m) (X : Ob n) (Y : Ob m) → Partial (MorC n m)
⟦ ◇ ⟧Mor X pt = return (ptmor X)
⟦ δ , u ⟧Mor X Y = do
  [δ] ← ⟦ δ ⟧Mor X (ft Y)
  [u] ← ⟦ u ⟧Tm X
  
  [δ]₁ ← assume (∂₁ [δ] ≡ ft Y)
  [u]₁ ← assume (∂₁ [u] ≡ star [δ] Y (unbox [δ]₁))
  return (comp (qq [δ] Y (unbox [δ]₁)) [u] (unbox [u]₁ ∙ ! qq₀))
