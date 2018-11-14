{-# OPTIONS --rewriting --prop #-}

open import common
open import termmodel
import partialinterpretation
import totality
open import contextualcat
open import quotients

module _ (sC : StructuredCCat) where

open StructuredCCat
open CCat
open CCatMor
open partialinterpretation sC
open totality sC

private
  C = ccat sC

{- Existence of a morphism between the contextual categories (not yet structured) -}

Ob/ : DCtx n → Ob C n
Ob/ (Γ , dΓ) = totalify ⟦ Γ ⟧Ctx (isTotal⟦⟧Ctx dΓ)

Ob→S : ObS n → Ob C n
Ob→S = //-rec Ob/ {!!}

Mor/ : DMor n m → Mor C n m
Mor/ (dmor Γd Δd δ dδ) = totalify (⟦ δ ⟧Mor (Ob/ Γd) (Ob/ Δd)) (isTotal⟦⟧Mor (Ob/ Γd) (Ob/ Δd) (respects⟦⟧Ctx _ _) (respects⟦⟧Ctx _ _) dδ)

Mor→S : MorS n m → Mor C n m
Mor→S = //-rec Mor/ {!!}

∂₀/ : (X : DMor n m) → Ob→S (∂₀S (proj X)) ≡ ∂₀ C (Mor→S (proj X))
∂₀/ X@(dmor (Γ , dΓ) _ δ dδ) = ! (∂₀⟦⟧Mor _ _ δ {δᵈ = isTotal⟦⟧Mor _ _ (respects⟦⟧Ctx _ _) (respects⟦⟧Ctx _ _) dδ})

∂₀→S : (X : MorS n m) → Ob→S (∂₀S X) ≡ ∂₀ C (Mor→S X)
∂₀→S = //-elimP ∂₀/

f₀ : CCatMor synCCat C
Ob→ f₀ = Ob→S
Mor→ f₀ = Mor→S
∂₀→ f₀ {X = X} = ∂₀→S X
∂₁→ f₀ = {!!}
id→ f₀ = {!!}
comp→ f₀ = {!!}
ft→ f₀ = {!!}
pp→ f₀ = {!!}
star→ f₀ = {!!}
qq→ f₀ = {!!}
ss→ f₀ = {!!}
pt→ f₀ = {!!}
ptmor→ f₀ = {!!}


{- Existence of a morphism between the structured contextual categories -}

open StructuredCCatMor

f : StructuredCCatMor strSynCCat sC
ccat→ f = f₀
PiStr→ f = {!!}
lamStr→ f = {!!}
appStr→ f = {!!}
UUStr→ f = {!!}
ElStr→ f = {!!}


{- Uniqueness of the morphism -}

uniqueness : (f g : StructuredCCatMor strSynCCat sC) → f ≡ g
uniqueness f g = {!!}
