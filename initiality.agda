{-# OPTIONS --rewriting --prop #-}

open import common
open import quotients
open import syntx hiding (Mor)
open import rules
open import contextualcat
open import termmodel
import partialinterpretation
import totality

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
Ob/ (Γ , dΓ) = ⟦ Γ ⟧Ctx $ ⟦⟧Ctxᵈ dΓ

Ob/-eq : {Γ Γ' : DCtx n} → ⊢ ctx Γ == ctx Γ' → Ob/ Γ ≡ Ob/ Γ'
Ob/-eq dΓ= = ⟦⟧CtxEq dΓ=

Ob→S : ObS n → Ob C n
Ob→S = //-rec Ob/ (λ {a} {b} r → Ob/-eq {Γ = a} {Γ' = b} r)

Mor/ : DMor n m → Mor C n m
Mor/ (dmor Γd Δd δ dδ) = ⟦ δ ⟧Mor (Ob/ Γd) (Ob/ Δd) $ ⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ

Mor/-eq : {δ δ' : DMor n m} → ((⊢ ctx (lhs δ) == ctx (lhs δ')) × (⊢ ctx (rhs δ) == ctx (rhs δ'))) ×
                              (ctx (lhs δ) ⊢ mor δ == mor δ' ∷> ctx (rhs δ))
                            → Mor/ δ ≡ Mor/ δ'
Mor/-eq {δ = dmor (Γ , dΓ) _ _ _} {δ' = dmor (Γ' , dΓ') _ _ _} ((dΓ= , dΔ=) , dδ=) = {!!} --rewrite ⟦⟧CtxEq dΓ= {⟦⟧Ctxᵈ dΓ} {⟦⟧Ctxᵈ dΓ'} = {!⟦⟧MorEq ? ? ? dδ=!}

Mor→S : MorS n m → Mor C n m
Mor→S = //-rec Mor/ (λ {a} {b} r → Mor/-eq {δ = a} {δ' = b} r)

∂₀/ : (X : DMor n m) → Ob→S (∂₀S (proj X)) ≡ ∂₀ C (Mor→S (proj X))
∂₀/ X@(dmor (Γ , dΓ) _ δ dδ) = ! (⟦⟧Mor₀ δ {δᵈ = ⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ})

∂₀→S : (X : MorS n m) → Ob→S (∂₀S X) ≡ ∂₀ C (Mor→S X)
∂₀→S = //-elimP ∂₀/

∂₁/ : (X : DMor n m) → Ob→S (∂₁S (proj X)) ≡ ∂₁ C (Mor→S (proj X))
∂₁/ X@(dmor (Γ , dΓ) _ δ dδ) = ! (⟦⟧Mor₁ δ {δᵈ = ⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ})

∂₁→S : (X : MorS n m) → Ob→S (∂₁S X) ≡ ∂₁ C (Mor→S X)
∂₁→S = //-elimP ∂₁/

id/ : (X : DCtx n) → Mor→S (idS n (proj X)) ≡ id C (Ob→S (proj X))
id/ (Γ , dΓ) = ⟦idMor⟧=

id→S : (X : ObS n) → Mor→S (idS n X) ≡ id C (Ob→S X)
id→S = //-elimP id/

ptmor→S : (X : ObS n) → Mor→S (ptmorS X) ≡ ptmor C (Ob→S X)
ptmor→S = //-elimP (λ _ → refl)

f₀ : CCatMor synCCat C
Ob→ f₀ = Ob→S
Mor→ f₀ = Mor→S
∂₀→ f₀ {X = X} = ∂₀→S X
∂₁→ f₀ {X = X} = ∂₁→S X
id→ f₀ {X = X} = id→S X
comp→ f₀ = {!!}
ft→ f₀ = {!!}
pp→ f₀ = {!!}
star→ f₀ = {!!}
qq→ f₀ = {!!}
ss→ f₀ = {!!}
pt→ f₀ = refl
ptmor→ f₀ {X = X} = ptmor→S X


{- Existence of a morphism between the structured contextual categories -}

open StructuredCCatMor

PiStr→S : (B : ObS (suc (suc n))) → Ob→ f₀ (PiStr strSynCCat B) ≡ PiStr sC (Ob→ f₀ B)
PiStr→S = //-elimP (λ {(((Γ , A) , B) , ((dΓ , dA) , dB)) → refl})

--lamStr→S

--appStr→S

UUStr→S : (X : ObS n) → Ob→S (UUStrS X) ≡ UUStr sC (Ob→S X)
UUStr→S = //-elimP (λ _ → refl)

ap2-irr2 : {A B E : Set} {C D : (a : A) (b : B) → Prop} (f : (a : A) (b : B) (c : C a b) (d : D a b) → E) {a a' : A} (p : a ≡ a') {b b' : B} (q : b ≡ b') {c : C a b} {c' : C a' b'} {d : D a b} {d' : D a' b'} → f a b c d ≡ f a' b' c' d'
ap2-irr2 f refl refl = refl

ElStr→S : (v : MorS n (suc n)) (vs : is-section synCCat v) (v₁ : ∂₁S v ≡ UUStrS (∂₀S v)) → Ob→S (ElStrS v vs v₁) ≡ ElStr sC (Mor→S v) {!!} {!!}
ElStr→S = //-elimP (λ {(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) vs v₁ → ap-irr2 (ElStr sC) {!reflect vs!}})

f-ex : StructuredCCatMor strSynCCat sC
ccat→ f-ex = f₀
PiStr→ f-ex = PiStr→S
lamStr→ f-ex = {!!}
appStr→ f-ex = {!!}
UUStr→ f-ex = UUStr→S
ElStr→ f-ex = ElStr→S


{- Uniqueness of the morphism -}

module _ (sf sg : StructuredCCatMor strSynCCat sC) where

  private
    f = ccat→ sf
    g = ccat→ sg

  uniqueness-Ob-// : (Γ : DCtx n) → Ob→ f (proj Γ) ≡ Ob→ g (proj Γ)
  uniqueness-Mor-// : (δ : DMor n m) → Mor→ f (proj δ) ≡ Mor→ g (proj δ)

  uniqueness-Ob-// (◇ , tt) = pt→ f ∙ ! (pt→ g)
  uniqueness-Ob-// ((Γ , pi A B) , (dΓ , Pi dA dB)) = PiStr→ sf (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) ∙ ap (PiStr sC) (uniqueness-Ob-// (((Γ , A) , B) , ((dΓ , dA) , dB))) ∙ ! (PiStr→ sg (proj (((Γ , A) , B) , ((dΓ , dA) , dB))))
  uniqueness-Ob-// ((Γ , uu) , (dΓ , A)) = UUStr→ sf (proj (Γ , dΓ)) ∙ ap (UUStr sC) (uniqueness-Ob-// (Γ , dΓ)) ∙ ! (UUStr→ sg (proj (Γ , dΓ)))
  uniqueness-Ob-// ((Γ , el v) , (dΓ , El dv)) =
    let thing = eq ((CtxRefl dΓ , CtxRefl dΓ) , MorSymm dΓ dΓ (congMorRefl (! (weakenMorInsert _ _ _ ∙ idMor[]Mor _)) (idMorDerivable dΓ)))
    in ElStr→ sf (proj (dmor (Γ , dΓ) ((Γ , uu) , (dΓ , UU)) (idMor _ , v) (idMorDerivable dΓ , dv))) thing refl ∙ ap-irr2 (ElStr sC) (uniqueness-Mor-// _) ∙ ! (ElStr→ sg (proj (dmor (Γ , dΓ) ((Γ , uu) , (dΓ , UU)) (idMor _ , v) (idMorDerivable dΓ , dv))) thing refl)

  uniqueness-Mor-// (dmor (Γ , dΓ) (◇ , tt) ◇ tt) = ptmor→ f {X = proj (Γ , dΓ)} ∙ ap (ptmor C) (uniqueness-Ob-// (Γ , dΓ)) ∙ ! (ptmor→ g)
  uniqueness-Mor-// (dmor (Γ , dΓ) ((Δ , B) , (dΔ , dB)) (δ , var last) (dδ , du)) = {!!}
  uniqueness-Mor-// (dmor (Γ , dΓ) ((Δ , B) , (dΔ , dB)) (δ , var (prev x)) (dδ , du)) = {!!}
  uniqueness-Mor-// (dmor (Γ , dΓ) ((Δ , B) , (dΔ , dB)) (δ , lam A B₁ u) (dδ , du)) = {!lamStr→ sf ? ? ∙ ? ∙ ! ?!}
  uniqueness-Mor-// (dmor (Γ , dΓ) ((Δ , B) , (dΔ , dB)) (δ , app A B₁ u u₁) (dδ , du)) = {!appStr→ sf ? ? ? ? ? ∙ ?!}

  uniqueness-Ob : (X : ObS n) → Ob→ f X ≡ Ob→ g X
  uniqueness-Ob = //-elimP uniqueness-Ob-//

  uniqueness-Mor : (X : MorS n m) → Mor→ f X ≡ Mor→ g X
  uniqueness-Mor = //-elimP uniqueness-Mor-//

  uniqueness : sf ≡ sg
  uniqueness = structuredCCatMorEq uniqueness-Ob uniqueness-Mor
