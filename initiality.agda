{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import typetheory
open import syntx hiding (Mor)
open import rules
open import contextualcat
open import quotients
open import termmodel
import partialinterpretation
import totality hiding (lhs)

module _ (sC : StructuredCCat) where

open StructuredCCat
open CCatMor
open partialinterpretation sC
open totality sC
open StructuredCCatMor

private
  C = ccat sC

open CCat C renaming (id to idC)

{- Existence of a morphism between the contextual categories (not yet structured) -}

Ob/ : DCtx n → Ob n
Ob/ Γ = ⟦ ctx Γ ⟧Ctx $ ⟦⟧Ctxᵈ (der Γ)

Ob/-eq : {Γ Γ' : DCtx n} → Γ ≃ Γ' → Ob/ Γ ≡ Ob/ Γ'
Ob/-eq rΓ = ⟦⟧CtxEq (unOb≃ rΓ)

Ob→S : ObS n → Ob n
Ob→S = //-rec Ob/ Ob/-eq

Mor/ : DMor n m → Mor n m
Mor/ δ = ⟦ mor δ ⟧Mor (Ob/ (lhs δ)) (Ob/ (rhs δ)) $ ⟦⟧Morᵈ (⟦⟧Ctxᵈ (der (lhs δ))) (⟦⟧Ctxᵈ (der (rhs δ))) (morDer δ)

Mor/-eq : {δ δ' : DMor n m} → δ ≃ δ' → Mor/ δ ≡ Mor/ δ'
Mor/-eq {δ = δ} {δ'} rδ =
  ⟦⟧MorEq {Γ' = ctx (lhs δ')} {Δ' = ctx (rhs δ')} (⟦⟧Ctxᵈ (der (lhs δ))) (unMor≃-mor rδ) {δ'ᵈ = ⟦⟧Morᵈ (⟦⟧Ctxᵈ (der (lhs δ))) (⟦⟧Ctxᵈ (der (rhs δ))) (MorEqMor2 (der (lhs δ)) (der (rhs δ)) (unMor≃-mor rδ))}
  ∙ ap2-irr (λ x y z → ⟦_⟧Mor (mor δ') x y $ z) (⟦⟧CtxEq (unMor≃-lhs rδ)) (⟦⟧CtxEq (unMor≃-rhs rδ))

Mor→S : MorS n m → Mor n m
Mor→S = //-rec Mor/ Mor/-eq

∂₀/ : (f : DMor n m) → ∂₀ (Mor→S (proj f)) ≡ Ob→S (∂₀S (proj f))
∂₀/ f = ⟦⟧Mor₀ (mor f)

∂₀→S : (f : MorS n m) → ∂₀ (Mor→S f) ≡ Ob→S (∂₀S f)
∂₀→S = //-elimP ∂₀/

∂₁/ : (f : DMor n m) → ∂₁ (Mor→S (proj f)) ≡ Ob→S (∂₁S (proj f))
∂₁/ f = ⟦⟧Mor₁ (mor f)

∂₁→S : (f : MorS n m) → ∂₁ (Mor→S f) ≡ Ob→S (∂₁S f)
∂₁→S = //-elimP ∂₁/

id/ : (Γ : DCtx n) → idC (Ob→S (proj Γ)) ≡ Mor→S (idS n (proj Γ))
id/ Γ = ! (⟦idMor⟧= refl)

id→S : (Γ : ObS n) → idC (Ob→S Γ) ≡ Mor→S (idS n Γ)
id→S = //-elimP id/

comp/ : (g : DMor m k) (f : DMor n m) {X : DCtx m} (g₀ : ∂₀S (proj g) ≡ proj X) (f₁ : ∂₁S (proj f) ≡ proj X) → comp (Mor→S (proj g)) (Mor→S (proj f)) (∂₀/ g ∙ ap Ob→S g₀) (∂₁/ f ∙ ap Ob→S f₁) ≡ Mor→S (S.comp (proj g) (proj f) g₀ f₁)
comp/ g f g₀ f₁ = ! (⟦tsubst⟧Mor= (⟦⟧CtxEq (reflectOb (f₁ ∙ ! g₀))) (mor f) (⟦⟧Morᵈ (⟦⟧Ctxᵈ (der (lhs f))) (⟦⟧Ctxᵈ (der (rhs f))) (morDer f)) (mor g) (⟦⟧Morᵈ (⟦⟧Ctxᵈ (der (lhs g))) (⟦⟧Ctxᵈ (der (rhs g))) (morDer g)) ∙ ap-irr-comp refl refl)

comp→S : (g : MorS m k) (f : MorS n m) (X : ObS m) (g₀ : ∂₀S g ≡ X) (f₁ : ∂₁S f ≡ X) → comp (Mor→S g) (Mor→S f) (∂₀→S g ∙ ap Ob→S g₀) (∂₁→S f ∙ ap Ob→S f₁) ≡ Mor→S (S.comp g f g₀ f₁)
comp→S = //-elimP (λ g → //-elimP (λ f → //-elimP (λ X → comp/ g f)))

ft/ : (X : DCtx (suc n)) → ft (Ob→S (proj X)) ≡ Ob→S (ftS (proj X))
ft/ ((Γ , A) , (dΓ , dA)) = ⟦⟧Ty-ft A

ft→S : (X : ObS (suc n)) → ft (Ob→S X) ≡ Ob→S (ftS X)
ft→S = //-elimP ft/

pp/ : (X : DCtx (suc n)) → pp (Ob→S (proj X)) ≡ Mor→S (ppS (proj X))
pp/ {n = n} ((Γ , A) , (dΓ , dA)) = ! (⟦weakenMor⟧= (⟦⟧Ty-ft A) (idMor n) (⟦idMor⟧ᵈ {X = ⟦ Γ ⟧Ctx $ ⟦⟧Ctxᵈ dΓ} refl) ∙ ap-irr-comp (⟦idMor⟧= refl) refl ∙ id-right (pp₁ ∙ ⟦⟧Ty-ft A))

pp→S : (X : ObS (suc n)) → pp (Ob→S X) ≡ Mor→S (ppS X)
pp→S = //-elimP pp/

⟦⟧dTyᵈ : (A : DCtx (suc n)) {Γ : DCtx n} (A= : (Ctx-Ty (ctx A) , dCtx-Ty A) ≃ Γ) → isDefined (⟦ Ty A ⟧Ty (Ob/ Γ))
⟦⟧dTyᵈ A {Γ} A= = ⟦⟧Tyᵈ (⟦⟧Ctxᵈ (der Γ)) (dTy A (eq A=))

cong⟦⟧Mor2 : {X X' : Ob n} {Y Y' : Ob m} {δ : syntx.Mor n m} → X ≡ X' → Y ≡ Y' → isDefined (⟦ δ ⟧Mor X Y) → isDefined (⟦ δ ⟧Mor X' Y')
cong⟦⟧Mor2 refl refl δᵈ = δᵈ

⟦⟧dMorᵈ : (f : DMor m n) {Γ : DCtx m} {Δ : DCtx n} (f₀ : lhs f ≃ Γ) (f₁ : rhs f ≃ Δ) → isDefined (⟦ mor f ⟧Mor (Ob/ Γ) (Ob/ Δ))
⟦⟧dMorᵈ f f₀ f₁ = cong⟦⟧Mor2 {δ = mor f} (⟦⟧CtxEq (unOb≃ f₀)) (⟦⟧CtxEq (unOb≃ f₁)) (⟦⟧Morᵈ (⟦⟧Ctxᵈ (der (lhs f))) (⟦⟧Ctxᵈ (der (rhs f))) (morDer f))

star/ : (f : DMor m n) (X : DCtx (suc n)) (Y : DCtx n) (q : ftS (proj X) ≡ proj Y) (f₁ : ∂₁S (proj f) ≡ proj Y) → star (Mor→S (proj f)) (Ob→S (proj X)) (ft/ X ∙ ap Ob→S q) (∂₁/ f ∙ ap Ob→S f₁) ≡ Ob→S (S.star (proj f) (proj X) q f₁)
star/ f X Y q f₁ = ap-irr-star {!!} {!refl!} ∙ ⟦tsubst⟧Ty= (Ty X) (⟦⟧dTyᵈ X (reflect q)) (mor f) (⟦⟧dMorᵈ f (ref (lhs f)) (reflect f₁))
-- star/ (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) ((Δ' , A) , (dΔ' , dA')) p =
--   let dA = ConvTy dA' (reflect (! p)) in
--   ! (⟦tsubst⟧Ty= A (⟦⟧Tyᵈ respects⟦⟧Ctx dA) δ (⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ)) ∙ ap2-irr star refl (ap-irr (λ x z → ⟦ A ⟧Ty x $ z) (⟦⟧CtxEq (reflect p)))

star→S : (f : MorS m n) (X : ObS (suc n)) (Y : ObS n) (q : ftS X ≡ Y) (f₁ : ∂₁S f ≡ Y) → star (Mor→S f) (Ob→S X) (ft→S X ∙ ap Ob→S q) (∂₁→S f ∙ ap Ob→S f₁) ≡ Ob→S (S.star f X q f₁)
star→S = //-elimP (λ f → //-elimP (λ X → //-elimP (λ Y → star/ f X Y)))

-- qq/ : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → Mor→S (qqS (proj f) (proj X) p) ≡ qq (Mor→S (proj f)) (Ob→S (proj X)) (! (∂₁→S (proj f)) ∙ ap Ob→S p ∙ ft→S (proj X))
-- qq/ (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) ((Δ' , A) , (dΔ' , dA')) p =
--   let dA = ConvTy dA' (reflect (! p)) in
--   ⟦weakenMor+⟧= (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A ∙ ⟦⟧CtxEq (reflect (! p))) δ (⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ) (ap2-irr star refl (ap-irr (λ x z → ⟦ A ⟧Ty x $ z) (! (⟦⟧CtxEq (reflect p)))) ∙ ⟦tsubst⟧Ty= A (⟦⟧Tyᵈ respects⟦⟧Ctx dA) δ (⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ))

-- qq→S : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → Mor→S (qqS f X p) ≡ qq (Mor→S f) (Ob→S X) (! (∂₁→S f) ∙ ap Ob→S p ∙ ft→S X)
-- qq→S = //-elimP (λ f → //-elimP (qq/ f))

-- ss/ : (f : DMor m (suc n)) → Mor→S (ssS (proj f)) ≡ ss (Mor→S (proj f))
-- ss/ (dmor (Γ , dΓ) ((Δ , A) , (dΔ , dA)) (δ , u) (dδ , du)) = ap2-irr comp (ap2-irr qq (⟦idMor⟧= (⟦⟧Ty-ft (A [ δ ]Ty)) ∙ ap idC (! (⟦⟧Ty-ft (A [ δ ]Ty)))) refl ∙ qq-id ∙ ap idC (! (⟦⟧Tm₁ respects⟦⟧Ctx du))) refl ∙ id-right ∙ ! (ss-of-section _ (⟦⟧Tmₛ u)) ∙ ss-comp {f₁ = ⟦⟧Tm₁ respects⟦⟧Ctx du ∙ ! (⟦tsubst⟧Ty= A (⟦⟧Tyᵈ aux dA) δ (⟦⟧Morᵈ respects⟦⟧Ctx aux dδ)) ∙ ap2-irr star refl (ap-irr (λ x z → ⟦ A ⟧Ty x $ z) (⟦⟧Ty-ft A))}  where

--   aux : respectsCtx (ft (⟦ A ⟧Ty (⟦ Δ ⟧Ctx $ (⟦⟧Ctxᵈ dΔ)) $ (⟦⟧Tyᵈ respects⟦⟧Ctx dA))) Δ
--   aux rewrite ⟦⟧Ty-ft {X = ⟦ Δ ⟧Ctx $ (⟦⟧Ctxᵈ dΔ)} A {⟦⟧Tyᵈ respects⟦⟧Ctx dA} = respects⟦⟧Ctx

-- ss→S : (f : MorS m (suc n)) → Mor→S (ssS f) ≡ ss (Mor→S f)
-- ss→S = //-elimP ss/

ptmor→S : (X : ObS n) → ptmor (Ob→S X) ≡ Mor→S (ptmorS X)
ptmor→S = //-elimP (λ _ → refl)

f₀ : CCatMor synCCat C
Ob→ f₀ = Ob→S
Mor→ f₀ = Mor→S
∂₀→ f₀ {X = X} = ! (∂₀→S X)
∂₁→ f₀ {X = X} = ! (∂₁→S X)
id→ f₀ {X = X} = ! (id→S X)
comp→ f₀ {g = g} {f = f} {g₀ = g₀} {f₁ = f₁} = ! (comp→S g f _ g₀ f₁)
ft→ f₀ {X = X} = ! (ft→S X)
pp→ f₀ {X = X} = ! (pp→S X)
star→ f₀ {f = f} {X = X} {q = q} {f₁ = f₁} = ! (star→S f X _ q f₁)
qq→ f₀ {f = f} {X = X} = {!qq→S f X p!}
ss→ f₀ {f = f} = {!ss→S f!}
pt→ f₀ = refl
ptmor→ f₀ {X = X} = ! (ptmor→S X)

{- Existence of a morphism between the structured contextual categories -}

lemmaTy : {Γ : DCtx n} (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) → ⟦ Ty A ⟧Ty (Ob/ Γ) $ ⟦⟧dTyᵈ A (reflect A=) ≡ Ob→S (proj A)
lemmaTy ((Γ' , A) , (dΓ' , dA)) A= = ap-irr (λ x z → ⟦ A ⟧Ty x $ z) (⟦⟧CtxEq (reflectOb (! A=)))

lemmaTm : (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) {A : DCtx (suc n)} {Γ : DCtx n} (u₁ : ∂₁S (proj u) ≡ proj A) (p : proj {R = ObEquiv} (ftS-// A) ≡ proj Γ) {w : _}
           → ⟦ Tm u ⟧Tm (Ob/ Γ) $ w ≡ Mor→S (proj u)
lemmaTm uu@(dmor (Γu , dΓu) ((Γu' , Au) , (dΓu' , dAu)) (δu , u) (dδu , du~)) uₛ {((Γ , A) , (dΓ , dA))} {(Γ' , dA')} u₁ p =
  -- let δu= : Γu ⊢ δu == idMor _ ∷> Γu'
  --     δu= = congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor δu) refl (snd (reflect uₛ))

  --     du : Derivable (Γu ⊢ u :> Au)
  --     du = ConvTm2 du~ (CtxRefl dΓu) (congTyEq refl ([idMor]Ty Au) (SubstTyMorEq dAu dδu δu=))

  --     dΓu=' : ⊢ Γu' == Γu
  --     dΓu=' = snd (fst (reflect uₛ))

  --     dAu' : Derivable (Γu ⊢ Au)
  --     dAu' = ConvTy dAu dΓu='

  --     u₀ : ⟦ Γu ⟧Ctx $ ⟦⟧Ctxᵈ dΓu ≡ ⟦ Γ' ⟧Ctx $ ⟦⟧Ctxᵈ dA'
  --     u₀ = ⟦⟧CtxEq (CtxTran (CtxSymm dΓu=') (CtxTran (fst (reflect u₁)) (reflect p))) --(! (⟦⟧CtxEq dΓu=')) ∙ {!ap (λ z → Ob→S (ftS z)) u₁ !} ∙ ⟦⟧CtxEq (reflect p)
  -- in
  {!!}
  -- ! (ap2-irr comp (ap2-irr qq (⟦⟧MorEq {Γ' = Γu} {Δ' = Γu'} respects⟦⟧Ctx δu= ∙ ⟦idMor⟧= (⟦⟧Ty-ft Au ∙ ⟦⟧CtxEq dΓu=') ∙ ap idC (! (⟦⟧Ty-ft Au ∙ ⟦⟧CtxEq dΓu='))) refl ∙ qq-id ∙ ap idC (ap-irr (λ x z → ⟦ Au ⟧Ty (Ob→S x) $ z) (eq {a = Γu' , dΓu'} {b = Γu , dΓu} dΓu=') {b' = ⟦⟧Tyᵈ respects⟦⟧Ctx dAu'} ∙ ! (⟦⟧Tm₁ respects⟦⟧Ctx du))) refl ∙ id-right ∙ ap-irr (λ x z → ⟦ u ⟧Tm x $ z) u₀)

lemmaMorᵈ : (u : DMor n (suc n)) {X : Ob n} (u₀ : Ob→S (∂₀S (proj u)) ≡ X) → isDefined (⟦ Tm u ⟧Tm X)
lemmaMorᵈ uu@(dmor (Γu , dΓu) ((Γu' , Au) , (dΓu' , dAu)) (δu , u) (dδu , du~)) refl = {!⟦⟧Tmᵈ respects⟦⟧Ctx du~!}

lemma2 : (u : DMor n (suc n)) (uₛ : S.is-section (proj u))
           → Mor→S (proj u) ≡ ⟦ Tm u ⟧Tm (Ob→S (∂₀S (proj u))) $ lemmaMorᵈ u refl
lemma2 uu@(dmor (Γ , dΓ) ((Δ , A) , (dΔ , dA)) (δ , u) (dδ , du)) uₛ =
  {!! (lemmaTm uu uₛ refl refl {w = ⟦⟧Tmᵈ respects⟦⟧Ctx (ConvTm du (CtxSymm (sectionS-eq-ctx {dA = dA} {dδ = dδ} {du = du} uₛ)))}) ∙ ap-irr (λ x z → ⟦ u ⟧Tm x $ z) (⟦⟧CtxEq (sectionS-eq-ctx {dA = dA} {dδ = dδ} {du = du} uₛ))!}


UUStr→S : (i : ℕ) (Γ : ObS n) → Ob→S (UUStrS i Γ) ≡ UUStr sC i (Ob→S Γ)
UUStr→S i = //-elimP (λ _ → refl)

ElStr→S : (i : ℕ) (Γ : ObS n) (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ UUStrS i Γ) → Ob→S (ElStrS i Γ v vₛ v₁) ≡ ElStr sC i (Ob→S Γ) (Mor→S v) (Mor→ₛ f₀ vₛ) (∂₁→S v ∙ ap Ob→S v₁ ∙ UUStr→S i Γ)
ElStr→S i = //-elimP (λ Γ → //-elimP (λ v vₛ v₁ →
  ap-irr-ElStr refl
               (lemmaTm v vₛ v₁ refl)))

PiStr→S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) → Ob→ f₀ (PiStrS Γ A A= B B=) ≡ PiStr sC (Ob→ f₀ Γ) (Ob→ f₀ A) (ft→S A ∙ ap (Ob→ f₀) A=) (Ob→ f₀ B) (ft→S B ∙ ap (Ob→ f₀) B=)
PiStr→S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= →
  ap-irr-PiStr refl
               (lemmaTy A A=)
               (lemmaTy B (combine A= B B=)))))

SigStr→S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) → Ob→ f₀ (SigStrS Γ A A= B B=) ≡ SigStr sC (Ob→ f₀ Γ) (Ob→ f₀ A) (ft→S A ∙ ap (Ob→ f₀) A=) (Ob→ f₀ B) (ft→S B ∙ ap (Ob→ f₀) B=)
SigStr→S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= →
  ap-irr-SigStr refl
                (lemmaTy A A=)
                (lemmaTy B (combine A= B B=)))))

NatStr→S : (Γ : ObS n) → Ob→S (NatStrS Γ) ≡ NatStr sC (Ob→S Γ)
NatStr→S = //-elimP (λ _ → refl)

IdStr→S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ A) (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ A)
        → {w1 : _} {w2 : _} {w3 : _} {w4 : _} {w5 : _}
        → Ob→ f₀ (IdStrS Γ A A= u uₛ u₁ v vₛ v₁) ≡ IdStr sC (Ob→ f₀ Γ) (Ob→ f₀ A) w1 (Mor→ f₀ u) w2 w3 (Mor→ f₀ v) w4 w5
IdStr→S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ →
  ap-irr-IdStr sC refl
                  (lemmaTy A A=)
                  (lemmaTm u uₛ u₁ (eq (reflect A=)))
                  (lemmaTm v vₛ v₁ (eq (reflect A=)))))))


uuStr→S : (i : ℕ) (Γ : ObS n)
        → Mor→ f₀ (uuStrS i Γ) ≡ uuStr sC i (Ob→ f₀ Γ)
uuStr→S i = //-elimP (λ Γ → lemma2 _ (uuStrₛS i (proj Γ)))

piStr→S : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁))
        → Mor→ f₀ (piStrS i Γ a aₛ a₁ b bₛ b₁) ≡ piStr sC i (Ob→ f₀ Γ) (Mor→ f₀ a) (Mor→ₛ f₀ aₛ) (Mor→₁ f₀ {u = a} a₁ ∙ UUStr→S i Γ) (Mor→ f₀ b) (Mor→ₛ f₀ bₛ) (Mor→₁ f₀ {u = b} b₁ ∙ UUStr→S i (ElStrS i Γ a aₛ a₁) ∙ ap (UUStr sC i) (ElStr→S i Γ a aₛ a₁))
piStr→S i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ →
  lemma2 _ (piStrₛS i (proj Γ) (proj a) aₛ a₁ (proj b) bₛ b₁)
  ∙ ap-irr-piStr refl
                 (lemmaTm a aₛ a₁ refl)
                 (lemmaTm b bₛ b₁ refl))))

lamStr→S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (u : MorS (suc n) (suc (suc n))) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ B)
         → {w1 : _} {w2 : _} {w3 : _} {w4 : _}
         → Mor→ f₀ (lamStrS Γ A A= B B= u uₛ u₁) ≡ lamStr sC (Ob→S Γ) (Ob→S A) w1 (Ob→S B) w2 (Mor→S u) w3 w4
lamStr→S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ →
  lemma2 _ (lamStrₛS (proj Γ) (proj A) A= (proj B) B= (proj u) uₛ u₁)
  ∙ ap-irr-lamStr refl
                  (lemmaTy A A=)
                  (lemmaTy B (combine A= B B=))
                  (lemmaTm u uₛ u₁ (combine A= B B=))))))

appStr→S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (f : MorS n (suc n)) (fₛ : S.is-section f) (f₁ : ∂₁S f ≡ PiStrS Γ A A= B B=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
         → {w1 : _} {w2 : _} {w3 : _} {w4 : _} {w5 : _} {w6 : _}
         → Mor→ f₀ (appStrS Γ A A= B B= f fₛ f₁ a aₛ a₁) ≡ appStr sC (Ob→S Γ) (Ob→S A) w1 (Ob→S B) w2 (Mor→S f) w3 w4 (Mor→S a) w5 w6
appStr→S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ f fₛ f₁ → //-elimP (λ a aₛ a₁ →
  lemma2 _ (appStrₛS (proj Γ) (proj A) A= (proj B) B= (proj f) fₛ f₁ (proj a) aₛ a₁)
  ∙ ap-irr-appStr refl
                  (lemmaTy A A=)
                  (lemmaTy B (combine A= B B=))
                  (lemmaTm f fₛ f₁ refl)
                  (lemmaTm a aₛ a₁ A=))))))

sigStr→S : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁))
        → Mor→ f₀ (sigStrS i Γ a aₛ a₁ b bₛ b₁) ≡ sigStr sC i (Ob→ f₀ Γ) (Mor→ f₀ a) (Mor→ₛ f₀ aₛ) (Mor→₁ f₀ {u = a} a₁ ∙ UUStr→S i Γ) (Mor→ f₀ b) (Mor→ₛ f₀ bₛ) (Mor→₁ f₀ {u = b} b₁ ∙ UUStr→S i (ElStrS i Γ a aₛ a₁) ∙ ap (UUStr sC i) (ElStr→S i Γ a aₛ a₁))
sigStr→S i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ →
  lemma2 _ (sigStrₛS i (proj Γ) (proj a) aₛ a₁ (proj b) bₛ b₁)
  ∙ ap-irr-sigStr refl
                  (lemmaTm a aₛ a₁ refl)
                  (lemmaTm b bₛ b₁ refl))))


-- pairStr/ : (B : DCtx (suc (suc n))) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (b : DMor n (suc n)) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj B) a₁)
--             {w1 : _} {w2 : _} {w3 : _} {w4 : _}
--           → Mor→ f₀ (pairStrS (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁) ≡ pairStr sC (Ob→ f₀ (proj B)) (Mor→ f₀ (proj a)) w1 w2 (Mor→ f₀ (proj b)) w3 w4
-- pairStr/ B@(((Γ , A') , B') , ((_ , _) , _)) a@(dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) aₛ a₁ b bₛ b₁ =
--   lemmaMor→S' (pairStrS-// B a aₛ a₁ b bₛ b₁) (pairStrₛS-// B a aₛ a₁ b bₛ b₁)
--   ∙ ap-irr-pairStr refl
--                    (lemmaMor→S a aₛ a₁ refl)
--                    (lemmaMor→S b bₛ b₁ (eq (snd (fst (reflect (! aₛ)))) ∙ ap ftS a₁))

pairStr→S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ S.star a B B= a₁)
          → {w1 : _} {w2 : _} {w3 : _} {w4 : _} {w5 : _} {w6 : _}
          → Mor→ f₀ (pairStrS Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ pairStr sC (Ob→ f₀ Γ) (Ob→ f₀ A) w1 (Ob→ f₀ B) w2 (Mor→ f₀ a) w3 w4 (Mor→ f₀ b) w5 w6
pairStr→S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ →
  lemma2 _ (pairStrₛS (proj Γ) (proj A) A= (proj B) B= (proj a) aₛ a₁ (proj b) bₛ b₁)
  ∙ ap-irr-pairStr refl
                   (lemmaTy A A=)
                   (lemmaTy B (combine A= B B=))
                   (lemmaTm a aₛ a₁ A=)
                   (lemmaTm b bₛ b₁ {!!}))))))


-- pr1Str/ : (B : DCtx (suc (suc n))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B))
--           {w1 : _} {w2 : _}
--         → Mor→ f₀ (pr1StrS (proj B) (proj u) uₛ u₁) ≡ pr1Str sC (Ob→ f₀ (proj B)) (Mor→ f₀ (proj u)) w1 w2
-- pr1Str/ B@(((Γ , A') , B') , ((_ , _) , _)) u@(dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) uₛ u₁ =
--   lemmaMor→S' (pr1StrS-// B u uₛ u₁) (pr1StrₛS-// B u uₛ u₁)
--   ∙ ap-irr-pr1Str refl
--                    (lemmaMor→S u uₛ u₁ refl)

-- pr1Str→S : (B : ObS (suc (suc n))) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B)
--            {w1 : _} {w2 : _}
--          → Mor→ f₀ (pr1StrS B u uₛ u₁) ≡ pr1Str sC (Ob→ f₀ B) (Mor→ f₀ u) w1 w2
-- pr1Str→S = //-elimP (λ B → //-elimP (λ u uₛ u₁ → pr1Str/ B u uₛ u₁))


-- pr2Str/ : (B : DCtx (suc (suc n))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B))
--           {w1 : _} {w2 : _}
--         → Mor→ f₀ (pr2StrS (proj B) (proj u) uₛ u₁) ≡ pr2Str sC (Ob→ f₀ (proj B)) (Mor→ f₀ (proj u)) w1 w2
-- pr2Str/ B@(((Γ , A') , B') , ((_ , _) , _)) u@(dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) uₛ u₁ =
--   lemmaMor→S' (pr2StrS-// B u uₛ u₁) (pr2StrₛS-// B u uₛ u₁)
--   ∙ ap-irr-pr2Str refl
--                    (lemmaMor→S u uₛ u₁ refl)

-- pr2Str→S : (B : ObS (suc (suc n))) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B)
--            {w1 : _} {w2 : _}
--          → Mor→ f₀ (pr2StrS B u uₛ u₁) ≡ pr2Str sC (Ob→ f₀ B) (Mor→ f₀ u) w1 w2
-- pr2Str→S = //-elimP (λ B → //-elimP (λ u uₛ u₁ → pr2Str/ B u uₛ u₁))


-- natStr/ : (i : ℕ) (X : DCtx n)
--         → Mor→ f₀ (natStrS i (proj X)) ≡ natStr sC i (Ob→ f₀ (proj X))
-- natStr/ i X =
--   lemmaMor→S' (natStrS-// i X) (natStrₛS-// i X)

-- natStr→S : (i : ℕ) (X : ObS n)
--         → Mor→ f₀ (natStrS i X) ≡ natStr sC i (Ob→ f₀ X)
-- natStr→S i = //-elimP (λ X → natStr/ i X)


-- zeroStr/ : (X : DCtx n)
--         → Mor→ f₀ (zeroStrS (proj X)) ≡ zeroStr sC (Ob→ f₀ (proj X))
-- zeroStr/ X =
--   lemmaMor→S' (zeroStrS-// X) (zeroStrₛS-// X)

-- zeroStr→S : (X : ObS n)
--         → Mor→ f₀ (zeroStrS X) ≡ zeroStr sC (Ob→ f₀ X)
-- zeroStr→S = //-elimP (λ X → zeroStr/ X)


-- sucStr/ : (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (∂₀S (proj u)))
--           {w1 : _} {w2 : _}
--         → Mor→ f₀ (sucStrS (proj u) uₛ u₁) ≡ sucStr sC (Mor→ f₀ (proj u)) w1 w2
-- sucStr/ u uₛ u₁ =
--   lemmaMor→S' (sucStrS-// u uₛ u₁) (sucStrₛS-// u uₛ u₁)
--   ∙ ap-irr2 (sucStr sC) (lemmaMor→S u uₛ u₁ refl)

-- sucStr→S : (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ NatStrS (∂₀S u))
--            {w1 : _} {w2 : _}
--          → Mor→ f₀ (sucStrS u uₛ u₁) ≡ sucStr sC (Mor→ f₀ u) w1 w2
-- sucStr→S = //-elimP (λ u uₛ u₁ → sucStr/ u uₛ u₁)


-- idStr/ : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a)))
--                  (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj a) aₛ a₁)
--                  (v : DMor n (suc n)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj a) aₛ a₁)
--          {w1 : _} {w2 : _} {w3 : _} {w4 : _} {w5 : _} {w6 : _}
--        → Mor→ f₀ (idStrS i (proj a) aₛ a₁ (proj u) uₛ u₁ (proj v) vₛ v₁) ≡ idStr sC i (Mor→ f₀ (proj a)) w1 w2 (Mor→ f₀ (proj u)) w3 w4 (Mor→ f₀ (proj v)) w5 w6
-- idStr/ i a aₛ a₁ u uₛ u₁ v vₛ v₁ =
--   lemmaMor→S' (idStrS-// i a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStrₛS-// i a aₛ a₁ u uₛ u₁ v vₛ v₁)
--   ∙ ap-irr-idStr (lemmaMor→S a aₛ a₁ refl)
--                  (lemmaMor→S u uₛ u₁ refl)
--                  (lemmaMor→S v vₛ v₁ refl)

-- idStr→S : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a))
--                   (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ ElStrS i a aₛ a₁)
--                   (v : MorS n (suc n)) (vₛ : is-sectionS v) (v₁ : ∂₁S v ≡ ElStrS i a aₛ a₁)
--            {w1 : _} {w2 : _} {w3 : _} {w4 : _} {w5 : _} {w6 : _}
--          → Mor→ f₀ (idStrS i a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ idStr sC i (Mor→ f₀ a) w1 w2 (Mor→ f₀ u) w3 w4 (Mor→ f₀ v) w5 w6
-- idStr→S i = //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → idStr/ i a aₛ a₁ u uₛ u₁ v vₛ v₁)))


-- reflStr/ : (A : DCtx (suc n)) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ proj A)
--            {w1 : _} {w2 : _}
--          → Mor→ f₀ (reflStrS (proj A) (proj u) uₛ u₁) ≡ reflStr sC (Ob→ f₀ (proj A)) (Mor→ f₀ (proj u)) w1 w2
-- reflStr/ A@((_ , _) , (_ , _)) u uₛ u₁ =
--   lemmaMor→S' (reflStrS-// A u uₛ u₁) (reflStrₛS-// A u uₛ u₁)
--   ∙ ap-irr-reflStr refl
--                    (lemmaMor→S u uₛ u₁ refl)

-- reflStr→S : (A : ObS (suc n)) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ A)
--             {w1 : _} {w2 : _}
--           → Mor→ f₀ (reflStrS A u uₛ u₁) ≡ reflStr sC (Ob→ f₀ A) (Mor→ f₀ u) w1 w2
-- reflStr→S = //-elimP (λ A → //-elimP (λ u uₛ u₁ → reflStr/ A u uₛ u₁))


existence : StructuredCCatMor strSynCCat sC
ccat→ existence = f₀

UUStr→ existence = UUStr→S
ElStr→ existence = ElStr→S
PiStr→ existence = PiStr→S
SigStr→ existence = SigStr→S
NatStr→ existence = NatStr→S
IdStr→ existence Γ A A= a aₛ a₁ b bₛ b₁ = IdStr→S Γ A A= a aₛ a₁ b bₛ b₁

uuStr→ existence = uuStr→S
piStr→ existence = piStr→S
lamStr→ existence Γ A A= B B= u uₛ u₁ = lamStr→S Γ A A= B B= u uₛ u₁
appStr→ existence Γ A A= B B= f fₛ f₁ a aₛ a₁ = appStr→S Γ A A= B B= f fₛ f₁ a aₛ a₁
sigStr→ existence i Γ a aₛ a₁ b bₛ b₁ = sigStr→S i Γ a aₛ a₁ b bₛ b₁
pairStr→ existence Γ A A= B B= a aₛ a₁ b bₛ b₁ = pairStr→S Γ A A= B B= a aₛ a₁ b bₛ b₁
pr1Str→ existence Γ A A= B B= u uₛ u₁ = {!pr1Str→S B u uₛ u₁!}
pr2Str→ existence Γ A A= B B= u uₛ u₁ = {!pr2Str→S B u uₛ u₁!}
natStr→ existence i Γ = {!natStr→S i X!}
zeroStr→ existence Γ = {!zeroStr→S X!}
sucStr→ existence Γ u uₛ u₁ = {!sucStr→S u uₛ u₁!}
idStr→ existence i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁ = {!idStr→S i a aₛ a₁ u uₛ u₁ v vₛ v₁!}
reflStr→ existence Γ A A= u uₛ u₁ = {!reflStr→S A u uₛ u₁!}

{-

{- Uniqueness of the morphism -}

get : (k : ℕ) (l : List ℕ) → ℕ
get k [] = zero
get zero (n ∷ ns) = n
get (suc k) (n ∷ ns) = get k ns

abstract
  +-it : List ℕ → ℕ
  +-it [] = zero
  +-it (n ∷ ns) = (+-it ns) + n

  <-+-lemma2 : (n m k m+k : ℕ) → n < m → m + k ≡ m+k → n < m+k
  <-+-lemma2 _ m k .(m + k) <-refl refl = <-+ k (+-comm k _)
  <-+-lemma2 n m k .(m + k) (<-suc ineq) refl = <-+-lemma2 n _ (suc k) _ ineq (! (+-suc _ k))

  <-+-lemma : (n a b x : ℕ) → n < suc (a + b) → n < suc (a + x + b)
  <-+-lemma n a b x ineq = <-+-lemma2 n (suc (a + b)) x (suc (a + x + b)) ineq (ap suc (+-assoc a _ _ ∙ ap (λ z → a + z) (+-comm b x) ∙ ! (+-assoc a _ _)))

  <-+-it : (k : ℕ) {l : List ℕ} {Γ : ℕ} → (get k l + Γ) < (suc (+-it l) + Γ)
  <-+-it k {[]} {Γ} = <-refl
  <-+-it zero {x ∷ l} {Γ} = <-+ (+-it l) (! (+-assoc (+-it l) _ _))
  <-+-it (suc k) {x ∷ l} {Γ} = <-+-lemma _ (+-it l) Γ x (<-+-it k {l = l} {Γ = Γ})

<-+-it' : (k : ℕ) {l : List ℕ} {Γ : ℕ} {x : ℕ} → (get k l + Γ ≡ x) → x < (suc (+-it l) + Γ)
<-+-it' k refl = <-+-it k

+suc+-lemma : (b a Γ : ℕ) → b + suc a + Γ ≡ b + suc (a + Γ)
+suc+-lemma zero a Γ = refl
+suc+-lemma (suc b) a Γ = ap suc (+suc+-lemma b a Γ)

<-refl' : {k n : ℕ} (p : k ≡ n) → n < suc k
<-refl' refl = <-refl

sizeTy : TyExpr n → ℕ
sizeTm : TmExpr n → ℕ

sizeTy (uu i) = 1
sizeTy (el i v) = 1 + sizeTm v
sizeTy (pi A B) = 1 + sizeTy B + sizeTy A
sizeTy (sig A B) = 1 + sizeTy B + sizeTy A
sizeTy nat = 1
sizeTy (id A u v) = suc (+-it (sizeTy A ∷ sizeTm u ∷ sizeTm v ∷ []))

sizeTm (var _) = 0

sizeTm (uu i) = 1

sizeTm (pi i a b) = suc (+-it (sizeTm a ∷ sizeTm b + suc (sizeTm a) ∷ []))
sizeTm (lam A B u) = suc (+-it ((sizeTy B + sizeTy A) ∷ (sizeTm u + sizeTy A) ∷ []))
sizeTm (app A B f a) = suc (+-it ((sizeTy B + sizeTy A) ∷ sizeTm f ∷ sizeTm a ∷ []))

sizeTm (sig i a b) = suc (+-it (sizeTm a ∷ sizeTm b + suc (sizeTm a) ∷ []))
sizeTm (pair A B a b) = suc (+-it ((sizeTy B + sizeTy A) ∷ sizeTm a ∷ sizeTm b ∷ []))
sizeTm (pr1 A B u) = suc (+-it ((sizeTy B + sizeTy A) ∷ sizeTm u ∷ []))
sizeTm (pr2 A B u) = suc (+-it ((sizeTy B + sizeTy A) ∷ sizeTm u ∷ []))

sizeTm (nat i) = 1
sizeTm zero = 1
sizeTm (suc u) = suc (sizeTm u)

sizeTm (id i a u v) = suc (+-it (sizeTm a ∷ sizeTm u ∷ sizeTm v ∷ []))
sizeTm (refl A u) = suc (+-it (sizeTy A ∷ sizeTm u ∷ []))


sizeCtx : Ctx n → ℕ
sizeCtx ◇ = 0
sizeCtx (Γ , A) = sizeTy A + sizeCtx Γ

sizeMor : syntx.Mor n m → ℕ
sizeMor {m = 0} ◇ = 0
sizeMor {m = suc m} (δ , u) = sizeTm u + sizeMor δ

sizeDMor : DMor n m → ℕ
sizeDMor δ = sizeCtx (ctx (lhs δ)) + sizeMor (mor δ)

sizeTy-pos : (A : TyExpr n) → 0 < sizeTy A
sizeTy-pos (uu i) = suc-pos _
sizeTy-pos (el i v) = suc-pos _
sizeTy-pos (pi A B) = suc-pos _
sizeTy-pos (sig A B) = suc-pos _
sizeTy-pos nat = suc-pos _
sizeTy-pos (id A u v) = suc-pos _

split-left : DMor n (suc m) → DMor n (suc n)
split-left (dmor (Γ , dΓ) ((Δ , C) , (dΔ , dC)) (δ , u) (dδ , du)) =
  dmor (Γ , dΓ) ((Γ , C [ δ ]Ty) , (dΓ , SubstTy dC dδ)) (idMor _ , u) ((idMorDerivable dΓ) , congTm (! ([idMor]Ty _)) refl du)

split-right : DMor n (suc m) → DMor (suc n) (suc m)
split-right (dmor (Γ , dΓ) ((Δ , C) , (dΔ , dC)) (δ , u) (dδ , du)) =
  dmor ((Γ , C [ δ ]Ty) , (dΓ , SubstTy dC dδ)) ((Δ , C) , (dΔ , dC)) (weakenMor δ , (var last)) (WeakMor (C [ δ ]Ty) dδ , (congTm (weaken[]Ty C δ last) refl (VarLast (SubstTy dC dδ))))

split-eq : (δ : DMor n (suc m)) → rhs (split-left δ) ≡ lhs (split-right δ)
split-eq (dmor (Γ , dΓ) ((Δ , C) , (dΔ , dC)) (δ , u) (dδ , du)) = refl

split-comp : (δ : DMor n (suc m)) → compS-//-u (split-right δ) (split-left δ) (ap proj (split-eq δ)) ≡ δ
split-comp (dmor (Γ , dΓ) ((Δ , C) , (dΔ , dC)) (δ , u) (dδ , du)) =
  ap-irr (λ x z → dmor (Γ , dΓ) ((Δ , C) , (dΔ , dC)) x z) (ap (λ x → x , u) (weakenMorInsert _ _ _ ∙ [idMor]Mor δ))

module _ (sf sg : StructuredCCatMor strSynCCat sC) where

  private
    f = ccat→ sf
    g = ccat→ sg

  TmToMor : {Γ : Ctx n} (dΓ : ⊢ Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → DMor n (suc n)
  TmToMor dΓ dA du = dmor (_ , dΓ) ((_ , _) , (dΓ , dA)) (idMor _ , _) (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl du)

  TmToMorₛ : {Γ : Ctx n} (dΓ : ⊢ Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → CCat.is-section synCCat (proj (TmToMor dΓ dA du))
  TmToMorₛ dΓ dA du = eq ((CtxRefl dΓ , CtxRefl dΓ) , MorSymm dΓ dΓ (congMorRefl (! (weakenMorInsert _ _ _ ∙ idMor[]Mor _)) (idMorDerivable dΓ)))

  uniqueness-Ob-// : (Γ : DCtx n) (IH : Acc (sizeCtx (ctx Γ))) → Ob→ f (proj Γ) ≡ Ob→ g (proj Γ)
  uniqueness-Tm-// : {Γ : Ctx n} (dΓ : ⊢ Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) (IH : Acc (sizeTm u + sizeCtx Γ)) → Mor→ f (proj (TmToMor dΓ dA du)) ≡ Mor→ g (proj (TmToMor dΓ dA du))

  uniqueness-Ob-// (◇ , tt) (acc IH) = pt→ f ∙ ! (pt→ g)
  uniqueness-Ob-// ((Γ , uu i) , (dΓ , UU)) (acc IH) =
    UUStr→ sf i (proj (Γ , dΓ))
    ∙ ap (UUStr sC i) (uniqueness-Ob-// (Γ , dΓ) (IH <-refl))
    ∙ ! (UUStr→ sg i (proj (Γ , dΓ)))
  uniqueness-Ob-// ((Γ , el i v) , (dΓ , El dv)) (acc IH) =
    ElStr→ sf i (proj (TmToMor dΓ UU dv)) (TmToMorₛ dΓ UU dv) refl
    ∙ ap-irr2 (ElStr sC i) (uniqueness-Tm-// dΓ UU dv (IH <-refl))
    ∙ ! (ElStr→ sg i (proj (TmToMor dΓ UU dv)) (TmToMorₛ dΓ UU dv) refl)
  uniqueness-Ob-// ((Γ , pi A B) , (dΓ , Pi dA dB)) (acc IH) =
    PiStr→ sf (proj (((Γ , A) , B) , ((dΓ , dA) , dB)))
    ∙ ap (PiStr sC) (uniqueness-Ob-// (((Γ , A) , B) , ((dΓ , dA) , dB)) (IH (<-refl' (+-assoc (sizeTy B) _ _))))
    ∙ ! (PiStr→ sg (proj (((Γ , A) , B) , ((dΓ , dA) , dB))))
  uniqueness-Ob-// ((Γ , sig A B) , (dΓ , Sig dA dB)) (acc IH) =
    SigStr→ sf (proj (((Γ , A) , B) , ((dΓ , dA) , dB)))
    ∙ ap (SigStr sC) (uniqueness-Ob-// (((Γ , A) , B) , ((dΓ , dA) , dB)) (IH (<-refl' (+-assoc (sizeTy B) _ _))))
    ∙ ! (SigStr→ sg (proj (((Γ , A) , B) , ((dΓ , dA) , dB))))
  uniqueness-Ob-// ((Γ , nat) , (dΓ , Nat)) (acc IH) =
    NatStr→ sf (proj (Γ , dΓ))
    ∙ ap (NatStr sC) (uniqueness-Ob-// (Γ , dΓ) (IH <-refl))
    ∙ ! (NatStr→ sg (proj (Γ , dΓ)))
  uniqueness-Ob-// ((Γ , id A u v) , (dΓ , Id dA du dv)) (acc IH) =
    IdStr→ sf (proj ((Γ , A) , (dΓ , dA))) (proj (TmToMor dΓ dA du)) (TmToMorₛ dΓ dA du) refl (proj (TmToMor dΓ dA dv)) (TmToMorₛ dΓ dA dv) refl
    ∙ ap-irr-IdStr (uniqueness-Ob-// _ (IH (<-+-it 0)))
                   (uniqueness-Tm-// dΓ dA du (IH (<-+-it 1)))
                   (uniqueness-Tm-// dΓ dA dv (IH (<-+-it 2)))
    ∙ ! (IdStr→ sg (proj ((Γ , A) , (dΓ , dA))) (proj (TmToMor dΓ dA du)) (TmToMorₛ dΓ dA du) refl (proj (TmToMor dΓ dA dv)) (TmToMorₛ dΓ dA dv) refl)

  uniqueness-Tm-// {Γ = Γ , A} (dΓ , dA) _ (VarLast dA) (acc IH) =
    ap (Mor→ f) (eq ((CtxRefl (dΓ , dA) , (CtxRefl (dΓ , dA) ,, congTyRefl (WeakTy A dA) (! (ap weakenTy ([idMor]Ty _)) ∙ weaken[]Ty A (idMor _) last))) , MorRefl (idMorDerivable (dΓ , dA) , (congTm (! ([idMor]Ty (weakenTy A))) refl (VarLast dA)))))
    ∙ ss→ f {f = proj (dmor ((Γ , A) , (dΓ , dA)) ((Γ , A) , (dΓ , dA)) (idMor _) (idMorDerivable (dΓ , dA)))}
    ∙ ap ss (id→ f ∙ ap idC (uniqueness-Ob-// ((Γ , A) , (dΓ , dA)) (acc IH)) ∙ ! (id→ g))
    ∙ ! (ss→ g {f = proj (dmor ((Γ , A) , (dΓ , dA)) ((Γ , A) , (dΓ , dA)) (idMor _) (idMorDerivable (dΓ , dA)))})
    ∙ ! (ap (Mor→ g) (eq ((CtxRefl (dΓ , dA) , (CtxRefl (dΓ , dA) ,, congTyRefl (WeakTy A dA) (! (ap weakenTy ([idMor]Ty _)) ∙ weaken[]Ty A (idMor _) last))) , MorRefl (idMorDerivable (dΓ , dA) , (congTm (! ([idMor]Ty (weakenTy A))) refl (VarLast dA))))))
  uniqueness-Tm-// {Γ = Γ , A} (dΓ , dA) _ (VarPrev {k = x} {A = B} dB dx) (acc IH) =
    ap (Mor→ f) (eq ((CtxRefl (dΓ , dA) , (CtxRefl (dΓ , dA) ,, congTyRefl (WeakTy A dB) (ap weakenTy (! ([idMor]Ty B)) ∙ weaken[]Ty B (idMor _) last ∙ ap (λ z → B [ z ]Ty) (! (idMor[]Mor _))))) , (MorRefl (idMorDerivable (dΓ , dA)) , congTmRefl (congTm (! ([idMor]Ty _)) refl (VarPrev dB dx)) (ap weakenTm (! ([idMor]Tm (var x))) ∙ weaken[]Tm (var x) (idMor _) last))))
    ∙ ss→ f {f = proj (dmor ((Γ , A) , (dΓ , dA)) ((Γ , B) , (dΓ , dB)) (idMor _ [ weakenMor (idMor _) ]Mor , var x [ weakenMor' last (idMor _) ]Tm) (SubstMor (idMorDerivable dΓ) (WeakMor A (idMorDerivable dΓ)) , congTm (ap (λ z → B [ z ]Ty) (! (idMor[]Mor _))) refl (SubstTm dx (WeakMor A (idMorDerivable dΓ)))))}
    ∙ ap ss (comp→ f {g = proj (dmor (Γ , dΓ) ((Γ , B) , (dΓ , dB)) (idMor _ , var x) (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl dx))} {f = ppS (proj ((Γ , A) , (dΓ , dA)))} {p = refl}
            ∙ ap2-irr comp (uniqueness-Tm-// dΓ dB dx (IH (<-pos _ _ (sizeTy-pos A))))
                           (pp→ f {X = proj ((Γ , A) , (dΓ , dA))}
                           ∙ ap pp (uniqueness-Ob-// ((Γ , A) , (dΓ , dA)) (acc IH))
                           ∙ ! (pp→ g {X = proj ((Γ , A) , (dΓ , dA))}))
            ∙ ! (comp→ g {g = proj (dmor (Γ , dΓ) ((Γ , B) , (dΓ , dB)) (idMor _ , var x) (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl dx))} {f = ppS (proj ((Γ , A) , (dΓ , dA)))} {p = refl}))
    ∙ ! (ss→ g {f = proj (dmor ((Γ , A) , (dΓ , dA)) ((Γ , B) , (dΓ , dB)) (idMor _ [ weakenMor (idMor _) ]Mor , var x [ weakenMor' last (idMor _) ]Tm) (SubstMor (idMorDerivable dΓ) (WeakMor A (idMorDerivable dΓ)) , congTm (ap (λ z → B [ z ]Ty) (! (idMor[]Mor _))) refl (SubstTm dx (WeakMor A (idMorDerivable dΓ)))))})
    ∙ ! (ap (Mor→ g) (eq ((CtxRefl (dΓ , dA) , (CtxRefl (dΓ , dA) ,, congTyRefl (WeakTy A dB) (ap weakenTy (! ([idMor]Ty B)) ∙ weaken[]Ty B (idMor _) last ∙ ap (λ z → B [ z ]Ty) (! (idMor[]Mor _))))) , (MorRefl (idMorDerivable (dΓ , dA)) , congTmRefl (congTm (! ([idMor]Ty _)) refl (VarPrev dB dx)) (ap weakenTm (! ([idMor]Tm (var x))) ∙ weaken[]Tm (var x) (idMor _) last)))))

  uniqueness-Tm-// dΓ _ (Conv dA du dA=) (acc IH) =
    ap (Mor→ f) (! (eq ((CtxRefl dΓ , (CtxRefl dΓ ,, dA=)) , MorRefl (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl du))))
    ∙ uniqueness-Tm-// dΓ dA du (acc IH)
    ∙ ! (ap (Mor→ g) (! (eq ((CtxRefl dΓ , (CtxRefl dΓ ,, dA=)) , MorRefl (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl du)))))

  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = uu i} UUUU (acc IH) =
    uuStr→ sf i (proj (Γ , dΓ))
    ∙ ap (uuStr sC i) (uniqueness-Ob-// _ (IH <-refl))
    ∙ ! (uuStr→ sg i (proj (Γ , dΓ)))

  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = pi i a b} (PiUU da db) (acc IH) =
    piStr→ sf i (proj (TmToMor dΓ UU da)) (TmToMorₛ dΓ UU da) refl (proj (TmToMor (dΓ , El da) UU db)) (TmToMorₛ (dΓ , El da) UU db) refl
    ∙ ap-irr-piStr (uniqueness-Tm-// dΓ UU da (IH (<-+-it 0)))
                   (uniqueness-Tm-// (dΓ , El da) UU db (IH (<-+-it' 1 (+suc+-lemma _ _ _))))
    ∙ ! (piStr→ sg i (proj (TmToMor dΓ UU da)) (TmToMorₛ dΓ UU da) refl (proj (TmToMor (dΓ , El da) UU db)) (TmToMorₛ (dΓ , El da) UU db) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = lam A B u} (Lam dA dB du) (acc IH) =
    lamStr→ sf (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) (proj (TmToMor (dΓ , dA) dB du)) (TmToMorₛ (dΓ , dA) dB du) refl
    ∙ ap-irr-lamStr (uniqueness-Ob-// _ (IH (<-+-it' 0 (+-assoc (sizeTy B) _ _))))
                    (uniqueness-Tm-// (dΓ , dA) dB du (IH (<-+-it' 1 (+-assoc (sizeTm u) _ _))))
    ∙ ! (lamStr→ sg (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) (proj (TmToMor (dΓ , dA) dB du)) (TmToMorₛ (dΓ , dA) dB du) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = app A B f a} (App dA dB df da) (acc IH) =
    appStr→ sf (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) (proj (TmToMor dΓ (Pi dA dB) df)) (TmToMorₛ dΓ (Pi dA dB) df) refl (proj (TmToMor dΓ dA da)) (TmToMorₛ dΓ dA da) refl
    ∙ ap-irr-appStr (uniqueness-Ob-// _ (IH (<-+-it' 0 (+-assoc (sizeTy B) _ _))))
                    (uniqueness-Tm-// dΓ (Pi dA dB) df (IH (<-+-it 1)))
                    (uniqueness-Tm-// dΓ dA da (IH (<-+-it 2)))
    ∙ ! (appStr→ sg (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) (proj (TmToMor dΓ (Pi dA dB) df)) (TmToMorₛ dΓ (Pi dA dB) df) refl (proj (TmToMor dΓ dA da)) (TmToMorₛ dΓ dA da) refl)

  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = sig i a b} (SigUU da db) (acc IH) =
    sigStr→ sf i (proj (TmToMor dΓ UU da)) (TmToMorₛ dΓ UU da) refl (proj (TmToMor (dΓ , El da) UU db)) (TmToMorₛ (dΓ , El da) UU db) refl
    ∙ ap-irr-sigStr (uniqueness-Tm-// dΓ UU da (IH (<-+-it 0)))
                    (uniqueness-Tm-// (dΓ , El da) UU db (IH (<-+-it' 1 (+suc+-lemma _ _ _))))
    ∙ ! (sigStr→ sg i (proj (TmToMor dΓ UU da)) (TmToMorₛ dΓ UU da) refl (proj (TmToMor (dΓ , El da) UU db)) (TmToMorₛ (dΓ , El da) UU db) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = pair A B a b} (Pair dA dB da db) (acc IH) =
    pairStr→ sf (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) (proj (TmToMor dΓ dA da)) (TmToMorₛ dΓ dA da) refl (proj (TmToMor dΓ (SubstTy dB (idMor+ dΓ da)) db)) (TmToMorₛ dΓ (SubstTy dB (idMor+ dΓ da)) db) refl
    ∙ ap-irr-pairStr (uniqueness-Ob-// _ (IH (<-+-it' 0 (+-assoc (sizeTy B) _ _))))
                     (uniqueness-Tm-// dΓ dA da (IH (<-+-it 1)))
                     (uniqueness-Tm-// dΓ (SubstTy dB (idMor+ dΓ da)) db (IH (<-+-it 2)))
    ∙ ! (pairStr→ sg (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) (proj (TmToMor dΓ dA da)) (TmToMorₛ dΓ dA da) refl (proj (TmToMor dΓ (SubstTy dB (idMor+ dΓ da)) db)) (TmToMorₛ dΓ (SubstTy dB (idMor+ dΓ da)) db) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = pr1 A B u} (Pr1 dA dB du) (acc IH) =
    pr1Str→ sf (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) (proj (TmToMor dΓ (Sig dA dB) du)) (TmToMorₛ dΓ (Sig dA dB) du) refl
    ∙ ap-irr-pr1Str (uniqueness-Ob-// _ (IH (<-+-it' 0 (+-assoc (sizeTy B) _ _))))
                    (uniqueness-Tm-// dΓ (Sig dA dB) du (IH (<-+-it 1)))
    ∙ ! (pr1Str→ sg (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) (proj (TmToMor dΓ (Sig dA dB) du)) (TmToMorₛ dΓ (Sig dA dB) du) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = pr2 A B u} (Pr2 dA dB du) (acc IH) =
    pr2Str→ sf (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) (proj (TmToMor dΓ (Sig dA dB) du)) (TmToMorₛ dΓ (Sig dA dB) du) refl
    ∙ ap-irr-pr2Str (uniqueness-Ob-// _ (IH (<-+-it' 0 (+-assoc (sizeTy B) _ _))))
                    (uniqueness-Tm-// dΓ (Sig dA dB) du (IH (<-+-it 1)))
    ∙ ! (pr2Str→ sg (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) (proj (TmToMor dΓ (Sig dA dB) du)) (TmToMorₛ dΓ (Sig dA dB) du) refl)

  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = nat i} NatUU (acc IH) =
    natStr→ sf i (proj (Γ , dΓ))
    ∙ ap (natStr sC i) (uniqueness-Ob-// _ (IH <-refl))
    ∙ ! (natStr→ sg i (proj (Γ , dΓ)))
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = zero} Zero (acc IH) =
    zeroStr→ sf (proj (Γ , dΓ))
    ∙ ap (zeroStr sC) (uniqueness-Ob-// _ (IH <-refl))
    ∙ ! (zeroStr→ sg (proj (Γ , dΓ)))
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = suc u} (Suc du) (acc IH) =
    sucStr→ sf (proj (TmToMor dΓ Nat du)) (TmToMorₛ dΓ Nat du) refl
    ∙ ap-irr2 (sucStr sC) (uniqueness-Tm-// dΓ Nat du (IH <-refl))
    ∙ ! (sucStr→ sg (proj (TmToMor dΓ Nat du)) (TmToMorₛ dΓ Nat du) refl)

  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = id i a u v} (IdUU da du dv) (acc IH) =
    idStr→ sf i (proj (TmToMor dΓ UU da)) (TmToMorₛ dΓ UU da) refl (proj (TmToMor dΓ (El da) du)) (TmToMorₛ dΓ (El da) du) refl (proj (TmToMor dΓ (El da) dv)) (TmToMorₛ dΓ (El da) dv) refl
    ∙ ap-irr-idStr (uniqueness-Tm-// dΓ UU da (IH (<-+-it 0)))
                   (uniqueness-Tm-// dΓ (El da) du (IH (<-+-it 1)))
                   (uniqueness-Tm-// dΓ (El da) dv (IH (<-+-it 2)))
    ∙ ! (idStr→ sg i (proj (TmToMor dΓ UU da)) (TmToMorₛ dΓ UU da) refl (proj (TmToMor dΓ (El da) du)) (TmToMorₛ dΓ (El da) du) refl (proj (TmToMor dΓ (El da) dv)) (TmToMorₛ dΓ (El da) dv) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = refl A u} (Refl dA du) (acc IH) =
    reflStr→ sf (proj ((Γ , A) , (dΓ , dA))) (proj (TmToMor dΓ dA du)) (TmToMorₛ dΓ dA du) refl
    ∙ ap-irr-reflStr (uniqueness-Ob-// _ (IH (<-+-it 0)))
                     (uniqueness-Tm-// dΓ dA du (IH (<-+-it 1)))
    ∙ ! (reflStr→ sg (proj ((Γ , A) , (dΓ , dA))) (proj (TmToMor dΓ dA du)) (TmToMorₛ dΓ dA du) refl)

  uniqueness-Ob : (X : ObS n) → Ob→ f X ≡ Ob→ g X
  uniqueness-Ob = //-elimP (λ Γ → uniqueness-Ob-// Γ (WO-Nat _))

  uniqueness-Mor-// : (δ : DMor n m) → Mor→ f (proj δ) ≡ Mor→ g (proj δ)
  uniqueness-Mor-// (dmor (Γ , dΓ) (◇ , tt) ◇ tt) = ptmor→ f {X = proj (Γ , dΓ)} ∙ ap ptmor (uniqueness-Ob-// (Γ , dΓ) (WO-Nat _)) ∙ ! (ptmor→ g)
  uniqueness-Mor-// δδ@(dmor (Γ , dΓ) ((Δ , C) , (dΔ , dC)) (δ , u) (dδ , du)) =
    ap (Mor→ f) (ap proj (! (split-comp δδ)))
    ∙ comp→ f {g = proj (split-right δδ)} {f = proj (split-left δδ)} {p = ap proj (split-eq δδ)}
    ∙ ap2-irr comp (qq→ f {f = proj (dmor (Γ , dΓ) (Δ , dΔ) δ dδ)} {X = proj ((Δ , C) , (dΔ , dC))} {p = refl}
                   ∙ ap2-irr qq (uniqueness-Mor-// (dmor (Γ , dΓ) (Δ , dΔ) δ dδ)) (uniqueness-Ob-// ((Δ , C) , (dΔ , dC)) (WO-Nat _))
                   ∙ ! (qq→ g {f = proj (dmor (Γ , dΓ) (Δ , dΔ) δ dδ)} {X = proj ((Δ , C) , (dΔ , dC))} {p = refl}))
                   (uniqueness-Tm-// dΓ (SubstTy dC dδ) du (WO-Nat _))
    ∙ ! (comp→ g {g = proj (split-right δδ)} {f = proj (split-left δδ)} {p = ap proj (split-eq δδ)})
    ∙ ! (ap (Mor→ g) (ap proj (! (split-comp δδ))))

  uniqueness-Mor : (X : MorS n m) → Mor→ f X ≡ Mor→ g X
  uniqueness-Mor = //-elimP uniqueness-Mor-//

  uniqueness : sf ≡ sg
  uniqueness = structuredCCatMorEq uniqueness-Ob uniqueness-Mor

-}
