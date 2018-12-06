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
  return (cong!Tm (unbox p) (varStr k X))
⟦ lam A B u ⟧Tm X Y = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty (Ty-Ctx [A])
  [u] ← ⟦ u ⟧Tm (Ty-Ctx [A]) [B]
  p ← assume (Y ≡ PiStr X [A] [B])
  return (cong!Tm (unbox p) (lamStr X [A] [B] [u]))
⟦ app A B f a ⟧Tm X Y = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty (Ty-Ctx [A])
  [f] ← ⟦ f ⟧Tm X (PiStr X [A] [B])
  [a] ← ⟦ a ⟧Tm X [A]
  p ← assume (Y ≡ substTyC [B] [a])
  return (cong!Tm (unbox p) (appStr X [A] [B] [f] [a]))


{- Partial interpretation of contexts and context morphisms -}

⟦_⟧Ctx : (Γ : Ctx n) → Partial (Ob n)
⟦ ◇ ⟧Ctx = return pt
⟦ Γ , A ⟧Ctx = do
  [Γ] ← ⟦ Γ ⟧Ctx
  [A] ← ⟦ A ⟧Ty [Γ]
  return (Ty-Ctx [A])

⟦_⟧Mor : (δ : Mor n m) (X : Ob n) (Y : Ob m) → Partial (CtxMor X Y)
⟦ ◇ ⟧Mor X Y = return (convertMorR (ptmorCtx X) (pt-unique Y))
⟦ δ , u ⟧Mor X Y = do
  [δ] ← ⟦ δ ⟧Mor X (ft Y)
  [u] ← ⟦ u ⟧Tm X (starTy [δ] (Ob-Ty Y))
  return (compCtx (qqCtx [δ] (Ob-Ty Y)) (Tm-CtxMor [u]))

