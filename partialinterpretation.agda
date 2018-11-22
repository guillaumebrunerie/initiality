{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import syntx
open import contextualcat

module _ (C : StructuredCCat) where

open StructuredCCat C
open CCat ccat renaming (Mor to MorC)
open M ccat renaming (substTy to substTyC; weakenTy to weakenTyC; weakenTm to weakenTmC)

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

⟦ var k ⟧Tm X Y = do
  p ← (assume (Y ≡ weakenTy^ k (Ty-at k X)))
  return (varStr k X Y (unbox p))
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

⟦_⟧Ctx : (Γ : Ctx n) → Partial (Ob n)
⟦ ◇ ⟧Ctx = return pt
⟦ Γ , A ⟧Ctx = do
  [Γ] ← ⟦ Γ ⟧Ctx
  [A] ← ⟦ A ⟧Ty [Γ]
  return (Ty-Ctx [A])

⟦_⟧Mor : (δ : Mor n m) (X : Ob n) (Y : Ob m) → Partial (CtxMor X Y)
⟦ ◇ ⟧Mor X Y = return (ptmorCtx X Y)
⟦ δ , u ⟧Mor X Y = do
  [δ] ← ⟦ δ ⟧Mor X (ft Y)
  [u] ← ⟦ u ⟧Tm X (starTy (Ob-Ty Y) [δ])
  return (compCtx (qqCtx Y [δ]) (Tm-CtxMor [u]))
