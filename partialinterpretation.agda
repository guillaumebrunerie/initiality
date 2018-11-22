{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import syntx
open import contextualcat

module _ (C : StructuredCCat) where

open StructuredCCat C
open CCat ccat renaming (Mor to MorC; substTy to substTyC)

{- Partial interpretation of types and terms -}

⟦_⟧Ty : TyExpr n → (X : Ob n) → Partial (Ty X)
⟦_⟧Tm : TmExpr n → (X : Ob n) → (Y : Ty X) → Partial (Tm X Y)

⟦ pi A B ⟧Ty X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty (Ty-Ctx [A])
  return (PiStr X [A] [B])
⟦ uu ⟧Ty X = return (UUStr X)
⟦ el v ⟧Ty X = do
  [v] ← ⟦ v ⟧Tm X (UUStr X)
  return (ElStr X [v])

⟦ var last ⟧Tm X Y = do
  p ← assume (Y ≡ ((star (pp X) X pp₁) , (ft-star ∙ pp₀)))
  return (varLastStr X Y (unbox p)) --return (ss (id X))
⟦ var (prev x) ⟧Tm X Y = {!!}  {-do
  [x] ← ⟦ var x ⟧Tm (ft X)
  [x]₀ ← assume (∂₀ [x] ≡ ft X)
  return (ss (comp [x] (pp X) (pp₁ ∙ ! (unbox [x]₀))))-}
⟦ lam A B u ⟧Tm X Y = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty (Ty-Ctx [A])
  [u] ← ⟦ u ⟧Tm (Ty-Ctx [A]) [B]
  p ← assume (Y ≡ PiStr X [A] [B])
  return (lamStr X [A] [B] [u] Y (unbox p))
⟦ app A B f a ⟧Tm X Y = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty (Ty-Ctx [A])
  [f] ← ⟦ f ⟧Tm X (PiStr X [A] [B])
  [a] ← ⟦ a ⟧Tm X [A]
  p ← assume (Y ≡ substTyC [B] [a])
  return (appStr X [A] [B] [f] [a] Y (unbox p))


{- Partial interpretation of contexts and context morphisms -}

-- ⟦_⟧Ctx : (Γ : Ctx n) → Partial (Ob n)
-- ⟦ ◇ ⟧Ctx = return pt
-- ⟦ Γ , A ⟧Ctx = do
--   [Γ] ← ⟦ Γ ⟧Ctx
--   [A] ← ⟦ A ⟧Ty [Γ]
--   return [A]

-- ⟦_⟧Mor : (δ : Mor n m) (X : Ob n) (Y : Ob m) → Partial (MorC n m)
-- ⟦ ◇ ⟧Mor X Y = return (ptmor X)
-- ⟦ δ , u ⟧Mor X Y = do
--   [δ] ← ⟦ δ ⟧Mor X (ft Y)
--   [u] ← ⟦ u ⟧Tm X
--   [δ]₁ ← assume (∂₁ [δ] ≡ ft Y)
--   [u]₁ ← assume (∂₁ [u] ≡ star [δ] Y (unbox [δ]₁))
--   return (comp (qq [δ] Y (unbox [δ]₁)) [u] (unbox [u]₁ ∙ ! qq₀))
