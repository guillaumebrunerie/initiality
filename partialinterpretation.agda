{-# OPTIONS --irrelevant-projections #-}

open import common
open import expr
open import contextualcat


record Partial (A : Set) : Set₁ where
  constructor makePartial
  field
    prop : Set
--    prop-is-prop : (a b : prop) → a ≡ b
    inj : prop → A
open Partial

return : {A : Set} → A → Partial A
return x = makePartial Unit {-(λ _ _ → refl)-} (λ _ → x)

_>>=_ : {A B : Set} → Partial A → (A → Partial B) → Partial B
prop (a >>= f) = Σ (prop a) (λ x → prop (f (inj a x)))
--prop-is-prop (a >>= f) (a₀ , b₀) (a₁ , b₁) = {!!}
inj (a >>= f) (a₀ , b₀) = inj (f (inj a a₀)) b₀

assume : (P : Set) → Partial P
assume p = makePartial p (λ x → x)

module _ (C : StructuredCCat) where

  open StructuredCCat C
  open CCat ccat renaming (Mor to MorC)
  open M ccat


  shift : {X : Ob n} {X' : Ob (suc n)} .(p : ft X' ≡ X) → Ty X' 0 → Ty X 1
  shift p T = (toCtx T) M., (ap ft (toCtxEq T) ∙ p)

  shiftTm : {X : Ob n} {X' : Ob (suc n)} .(p : ft X' ≡ X) → Tm X' 0 → Tm X 1
  getTy (shiftTm p t) = shift p (getTy t)
  morTm (shiftTm p t) = morTm t
  morTm₀ (shiftTm p t) = morTm₀ t
  morTm₁ (shiftTm p t) = morTm₁ t
  eqTm (shiftTm p t) = eqTm t

  ⟦_⟧ctx : (Γ : Ctx) → Partial (Ob (lenCtx Γ))
  ⟦_⟧ty : {n : ℕ} → TyExpr n → (X : Ob n) → Partial (Ty X 0)
  ⟦_⟧tm : {n : ℕ} → TmExpr n → (X : Ob n) → Partial (Tm X 0)
  ⟦_⟧mor : (δ : Mor n) (X : Ob n) (Y : Ob (lenMor δ)) → Partial (MorC n (lenMor δ))


  ⟦ ◇ ⟧ctx = return pt
  ⟦ Γ , A ⟧ctx = do
    [Γ] ← ⟦ Γ ⟧ctx
    [A] ← ⟦ A ⟧ty [Γ]
    return (toCtx [A])

  ⟦ pi A B ⟧ty X = do
    [A] ← ⟦ A ⟧ty X
    [B] ← ⟦ B ⟧ty ([A] .toCtx)
    return (PiStr X [A] (shift (toCtxEq [A]) [B]) (pair-irr (toCtxEq [B])))
  ⟦ uu ⟧ty X = return (UUStr X)
  ⟦ el v ⟧ty X = do
    [v] ← ⟦ v ⟧tm X
    vTy ← assume (getTy [v] ≡ UUStr X)
    return (ElStr X [v] vTy)

  ⟦ var x ⟧tm X = return (M.var ccat x X)
  ⟦ lam A B u ⟧tm X = do
    [A] ← ⟦ A ⟧ty X
    [B] ← ⟦ B ⟧ty ([A] .toCtx)
    [u] ← ⟦ u ⟧tm ([A] .toCtx)

    uTy ← assume (getTy [u] ≡ [B])
    return (lamStr X [A] (shift (toCtxEq [A]) [B]) (shiftTm (toCtxEq [A]) [u]) (pair-irr (toCtxEq [B])) (ap (shift (toCtxEq [A])) uTy))
  ⟦ app A B f a ⟧tm X = do
    [A] ← ⟦ A ⟧ty X
    [B] ← ⟦ B ⟧ty ([A] .toCtx)
    [f] ← ⟦ f ⟧tm X
    [a] ← ⟦ a ⟧tm X

    fTy ← assume (getTy [f] ≡ PiStr X [A] (shift (toCtxEq [A]) [B]) (pair-irr (toCtxEq [B])))
    aTy ← assume (getTy [a] ≡ [A])
    return (appStr X [A] (shift (toCtxEq [A]) [B]) [f] [a] (pair-irr (toCtxEq [B])) fTy aTy)
    
  ⟦ ◇ ⟧mor X Y = return (ptmor X)
  ⟦ δ , u ⟧mor X Y = do
    [δ] ← ⟦ δ ⟧mor X (ft Y)
    [u] ← ⟦ u ⟧tm X
  
    ∂₁δ ← assume (∂₁ [δ] ≡ ft Y)
    uTy ← assume (∂₁ (morTm [u]) ≡ ∂₀ (qq [δ] Y ∂₁δ))
    return (comp (qq [δ] Y ∂₁δ) (morTm [u]) uTy)
