{-# OPTIONS --rewriting --prop #-}

open import common
open import termmodel
open import partialinterpretation
open import totality
open import contextualcat
open import quotients

module _ (C : StructuredCCat) where

open StructuredCCat
open CCat
open StructuredCCatMor
open CCatMor
open DMor
open DCtx

Ob/ : DCtx n → Ob (ccat C) n
Ob/ (Γ , dΓ) = ⟦⟧Ctx C Γ dΓ

Mor/ : DMor n m → Mor (ccat C) n m
Mor/ (dmor Γd Δd δ dδ) = ⟦⟧Mor C (Ob/ Γd) (Ob/ Δd) δ dδ

f₀ : CCatMor synCCat (ccat C)
Ob→ f₀ = //-rec _ Ob/ #TODOP#
Mor→ f₀ = //-rec _ Mor/ #TODOP#
∂₀→ f₀ {X = X} = //-elimId (λ δ → Ob→ f₀ (∂₀S δ)) (λ δ → ∂₀ (ccat C) (Mor→ f₀ δ)) (λ δ → {!!}) X
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

{- Existence -}
f : StructuredCCatMor strSynCCat C
ccat→ f = {!!}
PiStr→ f = {!!}
lamStr→ f = {!!}
appStr→ f = {!!}
UUStr→ f = {!!}
ElStr→ f = {!!}

{- Uniqueness -}
uniqueness : (f g : StructuredCCatMor strSynCCat C) → f ≡ g
uniqueness f g = {!!}
