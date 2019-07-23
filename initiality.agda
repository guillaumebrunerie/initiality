{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import typetheory
open import syntx hiding (Mor)
open import rules
open import contextualcat
open import contextualcatmor
open import quotients
open import termmodel
import partialinterpretation
import totality

module _ (sC : StructuredCCat) where

open StructuredCCat
open CCatMor
open partialinterpretation sC
open totality sC
open StructuredCCatMor+
open StructuredCCatMor

private
  C = ccat sC

open CCat+ C renaming (id to idC)

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

⟦⟧dTyᵈ : (A : DCtx (suc n)) {Γ : DCtx n} (A= : (getCtx A , getdCtx A) ≃ Γ) → isDefined (⟦ getTy A ⟧Ty (Ob/ Γ))
⟦⟧dTyᵈ A {Γ} A= = ⟦⟧Tyᵈ (⟦⟧Ctxᵈ (der Γ)) (dTy A (eq A=))

cong⟦⟧Mor2 : {X X' : Ob n} {Y Y' : Ob m} {δ : syntx.Mor n m} → X ≡ X' → Y ≡ Y' → isDefined (⟦ δ ⟧Mor X Y) → isDefined (⟦ δ ⟧Mor X' Y')
cong⟦⟧Mor2 refl refl δᵈ = δᵈ

⟦⟧dMorᵈ : (f : DMor m n) {Γ : DCtx m} {Δ : DCtx n} (f₀ : lhs f ≃ Γ) (f₁ : rhs f ≃ Δ) → isDefined (⟦ mor f ⟧Mor (Ob/ Γ) (Ob/ Δ))
⟦⟧dMorᵈ f f₀ f₁ = cong⟦⟧Mor2 {δ = mor f} (⟦⟧CtxEq (unOb≃ f₀)) (⟦⟧CtxEq (unOb≃ f₁)) (⟦⟧Morᵈ (⟦⟧Ctxᵈ (der (lhs f))) (⟦⟧Ctxᵈ (der (rhs f))) (morDer f))

lemmaX : {Γ : DCtx n} (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) → proj {R = ObEquiv} (ctx A , der A) ≡ proj ((ctx Γ , getTy A) , (der Γ , dTy A A=))
lemmaX ((ΓA , A) , (dΓA , dA)) A= = eq (box (unOb≃ (reflect A=) ,, TyRefl dA))

star/ : (f : DMor m n) (X : DCtx (suc n)) (Y : DCtx n) (q : ftS (proj X) ≡ proj Y) (f₁ : ∂₁S (proj f) ≡ proj Y) → star (Mor→S (proj f)) (Ob→S (proj X)) (ft/ X ∙ ap Ob→S q) (∂₁/ f ∙ ap Ob→S f₁) ≡ Ob→S (S.star (proj f) (proj X) q f₁)
star/ f X Y q f₁ = ap-irr-star (ap2-irr (λ x y z → ⟦ mor f ⟧Mor x y $ z) refl (Ob/-eq (reflect f₁))) (Ob/-eq (reflect (lemmaX X q))) ∙ ⟦tsubst⟧Ty= (getTy X) (⟦⟧dTyᵈ X (reflect q)) (mor f) (⟦⟧dMorᵈ f (ref (lhs f)) (reflect f₁))

star→S : (f : MorS m n) (X : ObS (suc n)) (Y : ObS n) (q : ftS X ≡ Y) (f₁ : ∂₁S f ≡ Y) → star (Mor→S f) (Ob→S X) (ft→S X ∙ ap Ob→S q) (∂₁→S f ∙ ap Ob→S f₁) ≡ Ob→S (S.star f X q f₁)
star→S = //-elimP (λ f → //-elimP (λ X → //-elimP (λ Y → star/ f X Y)))

qq/ : (f : DMor m n) (X : DCtx (suc n)) (Y : DCtx n) (q : ftS (proj X) ≡ proj Y) (f₁ : ∂₁S (proj f) ≡ proj Y) → qq (Mor→S (proj f)) (Ob→S (proj X)) (ft→S (proj X) ∙ ap Ob→S q) (∂₁→S (proj f) ∙ ap Ob→S f₁) ≡ Mor→S (S.qq (proj f) (proj X) q f₁)
qq/ f X Y q f₁ = ap-irr-qq (ap2-irr (λ x y z → ⟦ mor f ⟧Mor x y $ z) refl (Ob/-eq (reflect (f₁ ∙ ! q)))) refl ∙ ! (⟦weakenMor+⟧= (mor f) (⟦⟧dMorᵈ f (ref (lhs f)) (reflect (f₁ ∙ ! q))) (ft/ X)   (ap-irr-star refl (Ob/-eq (reflect (lemmaX X refl))) ∙ ⟦tsubst⟧Ty= (getTy X) (⟦⟧dTyᵈ X (ref _)) (mor f) (⟦⟧dMorᵈ f (ref _) (reflect (f₁ ∙ ! q)))))

qq→S : (f : MorS m n) (X : ObS (suc n)) (Y : ObS n) (q : ftS X ≡ Y) (f₁ : ∂₁S f ≡ Y) → qq (Mor→S f) (Ob→S X) (ft→S X ∙ ap Ob→S q) (∂₁→S f ∙ ap Ob→S f₁) ≡ Mor→S (S.qq f X q f₁)
qq→S = //-elimP (λ f → //-elimP (λ X → //-elimP (λ Y → qq/ f X Y)))

ss/ : (f : DMor m (suc n)) → ss (Mor→S (proj f)) ≡ Mor→S (ssS (proj f))
ss/ (dmor (Γ , dΓ) ((Δ , A) , (dΔ , dA)) (δ , u) (dδ , du)) = ! ss-comp ∙ ss-of-section _ (⟦⟧Tmₛ u) ∙ ! (id-right (⟦⟧Tm₁ (⟦⟧Ctxᵈ dΓ) du)) ∙ ap-irr-comp (! (qq-id {p = ⟦⟧Ty-ft (A [ δ ]Ty)}) ∙ ! (ap-irr-qq (⟦idMor⟧= (⟦⟧Ty-ft (A [ δ ]Ty))) refl)) refl

ss→S : (f : MorS m (suc n)) → ss (Mor→S f) ≡ Mor→S (ssS f)
ss→S = //-elimP ss/

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
qq→ f₀ {f = f} {X = X} {q = q} {f₁ = f₁} = ! (qq→S f X _ q f₁)
ss→ f₀ {f = f} = ! (ss→S f)
pt→ f₀ = refl
ptmor→ f₀ {X = X} = ! (ptmor→S X)

{- Existence of a morphism between the structured contextual categories -}

lemmaTy : {Γ : DCtx n} (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) → ⟦ getTy A ⟧Ty (Ob/ Γ) $ ⟦⟧dTyᵈ A (reflect A=) ≡ Ob→S (proj A)
lemmaTy ((Γ' , A) , (dΓ' , dA)) A= = ap-irr (λ x z → ⟦ A ⟧Ty x $ z) (⟦⟧CtxEq (reflectOb (! A=)))

lemmaTm : (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) {A : DCtx (suc n)} {Γ : DCtx n} (u₁ : ∂₁S (proj u) ≡ proj A) (p : proj {R = ObEquiv} (ftS-// A) ≡ proj Γ) {w : _}
           → ⟦ getTm u ⟧Tm (Ob/ Γ) $ w ≡ Mor→S (proj u)
lemmaTm uu@(dmor (Γu , dΓu) ((Γu' , Au) , (dΓu' , dAu)) (δu , u) (dδu , du~)) uₛ {((Γ , A) , (dΓ , dA))} {(Γ' , dΓ')} u₁ p =
  let δu= : Γu ⊢ δu == idMor _ ∷> Γu'
      δu= = congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor δu) refl (unMor≃-mor (reflect (S.is-section= refl uₛ refl)))

      du' : Derivable (Γu ⊢ u :> Au)
      du' = ConvTm2 du~ (CtxRefl dΓu) (congTyEq refl ([idMor]Ty Au) (SubstTyMorEq dAu dδu δu=))

      dΓu=' : ⊢ Γu' == Γu
      dΓu=' = unMor≃-lhs (reflect (! (S.is-section= refl uₛ refl)))

      du : Derivable (Γu' ⊢ u :> Au)
      du = ConvTm du' (CtxSymm dΓu=')

      u₀ : ⟦ Γu' ⟧Ctx $ ⟦⟧Ctxᵈ dΓu' ≡ ⟦ Γ' ⟧Ctx $ ⟦⟧Ctxᵈ dΓ'
      u₀ = ⟦⟧CtxEq (CtxTran (fst (reflectOb u₁)) (reflectOb p))
  in
  ap-irr (λ x z → ⟦ u ⟧Tm x $ z) (! u₀) ∙ ! (id-right {f = ⟦ u ⟧Tm (⟦ Γu' ⟧Ctx $ ⟦⟧Ctxᵈ dΓu') $ ⟦⟧Tmᵈ (⟦⟧Ctxᵈ dΓu') du} (⟦⟧Tm₁ (⟦⟧Ctxᵈ dΓu') {Aᵈ = ⟦⟧Tyᵈ (⟦⟧Ctxᵈ dΓu') dAu} du)) ∙ ap-irr-comp (! (qq-id {p = ⟦⟧Ty-ft Au ∙ ⟦⟧CtxEq dΓu='}) ∙ ap-irr-qq ((! (⟦⟧MorEq {Γ' = Γu} {Δ' = Γu'} (⟦⟧Ctxᵈ dΓu) δu= ∙ ⟦idMor⟧= (⟦⟧Ty-ft Au ∙ ⟦⟧CtxEq dΓu=')))) refl) (ap-irr (λ x z → ⟦ u ⟧Tm x $ z) (⟦⟧CtxEq dΓu='))

lemmaMorᵈ : (u : DMor n (suc n)) {X : Ob n} (u₀ : Ob→S (∂₀S (proj u)) ≡ X) → isDefined (⟦ getTm u ⟧Tm X)
lemmaMorᵈ uu@(dmor (Γu , dΓu) ((Γu' , Au) , (dΓu' , dAu)) (δu , u) (dδu , du~)) refl = ⟦⟧Tmᵈ (⟦⟧Ctxᵈ dΓu) du~

lemma2 : (u : DMor n (suc n)) (uₛ : S.is-section (proj u))
           → Mor→S (proj u) ≡ ⟦ getTm u ⟧Tm (Ob→S (∂₀S (proj u))) $ lemmaMorᵈ u refl
lemma2 uu@(dmor (Γ , dΓ) ((Δ , A) , (dΔ , dA)) (δ , u) (dδ , du)) uₛ =
  ! (lemmaTm uu uₛ refl refl {w = ⟦⟧Tmᵈ (⟦⟧Ctxᵈ dΔ) (ConvTm du (unMor≃-lhs (reflect (S.is-section= refl uₛ refl))))}) ∙ ap-irr (λ x z → ⟦ u ⟧Tm x $ z) (⟦⟧CtxEq (unMor≃-lhs (reflect (! (S.is-section= refl uₛ refl)))))


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


pairStr→S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ S.star a B B= a₁)
          → {w1 : _} {w2 : _} {w3 : _} {w4 : _} {w5 : _} {w6 : _}
          → Mor→ f₀ (pairStrS Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ pairStr sC (Ob→ f₀ Γ) (Ob→ f₀ A) w1 (Ob→ f₀ B) w2 (Mor→ f₀ a) w3 w4 (Mor→ f₀ b) w5 w6
pairStr→S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ →
  lemma2 _ (pairStrₛS (proj Γ) (proj A) A= (proj B) B= (proj a) aₛ a₁ (proj b) bₛ b₁)
  ∙ ap-irr-pairStr refl
                   (lemmaTy A A=)
                   (lemmaTy B (combine A= B B=))
                   (lemmaTm a aₛ a₁ A=)
                   (lemmaTm b bₛ b₁ (S-is-section₀ aₛ a₁ ∙ A=)))))))

pr1Str→S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=)
         → {w1 : _} {w2 : _} {w3 : _} {w4 : _}
         → Mor→ f₀ (pr1StrS Γ A A= B B= u uₛ u₁) ≡ pr1Str sC (Ob→ f₀ Γ) (Ob→ f₀ A) w1 (Ob→ f₀ B) w2 (Mor→ f₀ u) w3 w4
pr1Str→S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ →
  lemma2 _ (pr1StrₛS (proj Γ) (proj A) A= (proj B) B= (proj u) uₛ u₁)
  ∙ ap-irr-pr1Str refl
                  (lemmaTy A A=)
                  (lemmaTy B (combine A= B B=))
                  (lemmaTm u uₛ u₁ refl)))))

pr2Str→S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=)
         → {w1 : _} {w2 : _} {w3 : _} {w4 : _}
         → Mor→ f₀ (pr2StrS Γ A A= B B= u uₛ u₁) ≡ pr2Str sC (Ob→ f₀ Γ) (Ob→ f₀ A) w1 (Ob→ f₀ B) w2 (Mor→ f₀ u) w3 w4
pr2Str→S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ →
  lemma2 _ (pr2StrₛS (proj Γ) (proj A) A= (proj B) B= (proj u) uₛ u₁)
  ∙ ap-irr-pr2Str refl
                  (lemmaTy A A=)
                  (lemmaTy B (combine A= B B=))
                  (lemmaTm u uₛ u₁ refl)))))

natStr→S : (i : ℕ) (Γ : ObS n)
        → Mor→ f₀ (natStrS i Γ) ≡ natStr sC i (Ob→ f₀ Γ)
natStr→S i = //-elimP (λ Γ → lemma2 _ (natStrₛS i (proj Γ)))

zeroStr→S : (Γ : ObS n)
        → Mor→ f₀ (zeroStrS Γ) ≡ zeroStr sC (Ob→ f₀ Γ)
zeroStr→S = //-elimP (λ Γ → lemma2 _ (zeroStrₛS (proj Γ)))

sucStr→S : (Γ : ObS n) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ)
         → {w1 : _} {w2 : _}
         → Mor→ f₀ (sucStrS Γ u uₛ u₁) ≡ sucStr sC (Ob→ f₀ Γ) (Mor→ f₀ u) w1 w2
sucStr→S = //-elimP (λ Γ → //-elimP (λ u uₛ u₁ →
  lemma2 _ (sucStrₛS (proj Γ) (proj u) {uₛ = uₛ} {u₁ = u₁})
  ∙ ap-irr-sucStr sC refl (lemmaTm u uₛ u₁ refl)))

natelimStr→S : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
               (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : ∂₁S dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
               (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : ∂₁S dS ≡ T-dS₁ sucStrSynCCat Γ P P=)
               (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ)
               {w1 : _} {w2 : _} {w3 : _} {w4 : _} {w5 : _} {w6 : _} {w7 : _}
            → Mor→ f₀ (natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)
              ≡ natelimStr sC (Ob→ f₀ Γ) (Ob→ f₀ P) w1
                              (Mor→ f₀ dO) w2 w3
                              (Mor→ f₀ dS) w4 w5
                              (Mor→ f₀ u) w6 w7
natelimStr→S = //-elimP (λ Γ → //-elimP (λ P P= → //-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → //-elimP (λ u uₛ u₁ →
  lemma2 (natelimStrS-// Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) (natelimStrₛS (proj Γ) (proj P) P= (proj dO) dOₛ dO₁ (proj dS) dSₛ dS₁ (proj u) uₛ u₁)
  ∙ ap-irr-natelimStr refl
                      (lemmaTy P P=)
                      (lemmaTm dO dOₛ dO₁ refl)
                      (lemmaTm dS dSₛ {Γ = ((ctx Γ , nat) , getTy P) , ((der Γ , Nat) , dTy P P=)} dS₁ (lemmaX P P=))
                      (lemmaTm u uₛ u₁ refl))))))

idStr→S : (i : ℕ) (Γ : ObS n)
                  (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ)
                  (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)
                  (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁)
           {w1 : _} {w2 : _} {w3 : _} {w4 : _} {w5 : _} {w6 : _}
         → Mor→ f₀ (idStrS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ idStr sC i (Ob→ f₀ Γ) (Mor→ f₀ a) w1 w2 (Mor→ f₀ u) w3 w4 (Mor→ f₀ v) w5 w6
idStr→S i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ →
  lemma2 _ (idStrₛS i (proj Γ) (proj a) aₛ a₁ (proj u) uₛ u₁ (proj v) vₛ v₁)
  ∙ ap-irr-idStr refl
                 (lemmaTm a aₛ a₁ refl)
                 (lemmaTm u uₛ u₁ refl)
                 (lemmaTm v vₛ v₁ refl)))))

reflStr→S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ A)
            {w1 : _} {w2 : _} {w3 : _}
          → Mor→ f₀ (reflStrS Γ A A= u uₛ u₁) ≡ reflStr sC (Ob→ f₀ Γ) (Ob→ f₀ A) w1 (Mor→ f₀ u) w2 w3
reflStr→S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ u uₛ u₁ →
  lemma2 _ (reflStrₛS (proj Γ) (proj A) A= (proj u) uₛ u₁)
  ∙ ap-irr-reflStr sC refl
                   (lemmaTy A A=)
                   (lemmaTm u uₛ u₁ A=))))

-- jjStr→S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc n)))) (P= : ftS P ≡ T-ftP ? Γ A A=) (d : MorS n (suc n)) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ T-d₁ ? Γ A A= P P=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ A) (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : ∂₁S p ≡ IdStr ? Γ A A= a aₛ a₁ b bₛ b₁) {w1 : _} {w2 : _} {w3 : _} {w4 : _} {w5 : _} {w6 : _} {w7 : _} {w8 : _} {w9 : _} {w10 : _} → Mor→ f₀ (jjStrS Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁) ≡ jjStr sC (Ob→ f₀ Γ) (Ob→ f₀ A) w1 (Ob→ f₀ P) w2 (Mor→ f₀ d) w3 w4 (Mor→ f₀ a) w5 w6 (Mor→ f₀ b) w7 w8 (Mor→ f₀ p) w9 w10
-- jjStr→s = ?


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
pr1Str→ existence Γ A A= B B= u uₛ u₁ = pr1Str→S Γ A A= B B= u uₛ u₁
pr2Str→ existence Γ A A= B B= u uₛ u₁ = pr2Str→S Γ A A= B B= u uₛ u₁
natStr→ existence i Γ = natStr→S i Γ
zeroStr→ existence Γ = zeroStr→S Γ
sucStr→ existence Γ u uₛ u₁ = sucStr→S Γ u uₛ u₁
idStr→ existence i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁ = idStr→S i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁
reflStr→ existence Γ A A= u uₛ u₁ = reflStr→S Γ A A= u uₛ u₁

existence+ : StructuredCCatMor+ strSynCCat sC
strucCCat→ existence+ = existence
natelimStr→ existence+ Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁ = natelimStr→S Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁
jjStr→ existence+ Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁ = #TODO#

{- Uniqueness of the morphism -}

get : (k : ℕ) (l : List ℕ) → ℕ
get k [] = zero
get zero (n ∷ ns) = n
get (suc k) (n ∷ ns) = get k ns

<-r : {n m : ℕ} → n < m → (n + 0) < (m + 0)
<-r <-refl = <-refl
<-r (<-suc eq) = <-suc (<-r eq)

<-l : (Γ : ℕ) {n m : ℕ} → n < m → (Γ + n) < (Γ + m)
<-l zero eq = eq
<-l (suc Γ) eq = suc-pres-< (<-l Γ eq)

<-pos' : (n m : ℕ) → 0 < m → n < (n + m)
<-pos' zero _ eq = eq
<-pos' (suc n) m eq = suc-pres-< (<-pos' n m eq)

abstract
  +-it : List ℕ → ℕ
  +-it [] = zero
  +-it (n ∷ ns) = (+-it ns) + n

  <-+-lemma2 : (n m k m+k : ℕ) → n < m → m + k ≡ m+k → n < m+k
  <-+-lemma2 _ m k .(m + k) <-refl refl = <-+ k (+-comm k _)
  <-+-lemma2 n m k .(m + k) (<-suc ineq) refl = <-+-lemma2 n _ (suc k) _ ineq (! (+-suc _ k))

  <-+-lemma : (n a b : ℕ) → n < suc a → n < suc (a + b)
  <-+-lemma n .n b <-refl = <-+-lemma2 n (suc n) b (suc (n + b)) <-refl refl
  <-+-lemma n a b (<-suc ineq) = <-+-lemma2 n a (suc b) (suc (a + b)) ineq (! (+-suc a b))

  get-<-+-it : (k : ℕ) {l : List ℕ} → get k l < suc (+-it l)
  get-<-+-it k {[]} = <-refl
  get-<-+-it zero {x ∷ l} = <-+ _ refl
  get-<-+-it (suc k) {x ∷ l} = <-+-lemma _ _ _ (get-<-+-it k {l})

  <-+-it : (k : ℕ) {l : List ℕ} {Γ : ℕ} → (Γ + get k l) < (Γ + suc (+-it l))
  <-+-it k {l} {Γ} = <-l Γ (get-<-+-it k {l})

  <-ctx : {Γ : ℕ} {l : List ℕ} → Γ < (Γ + suc (+-it l))
  <-ctx {zero} = suc-pos _
  <-ctx {suc Γ} {l} = suc-pres-< (<-ctx {l = l})

<-+-it' : (k : ℕ) {l : List ℕ} {Γ : ℕ} {x : ℕ} → (Γ + get k l ≡ x) → x < (Γ + suc (+-it l))
<-+-it' k refl = <-+-it k

+suc+-lemma : (Γ a b : ℕ) → Γ + suc (a + b) ≡ Γ + suc a + b
+suc+-lemma Γ _ _ = ! (+-assoc Γ _ _)

+suc+-lemma2 : (Γ a b c : ℕ) → Γ + suc (a + b + c) ≡ Γ + suc a + b + c
+suc+-lemma2 Γ a b c = ! (ap (λ u → u + c) (+-assoc Γ _ _) ∙ +-assoc Γ _ _)

lemma3 : (Γ : ℕ) {A v : ℕ} → (Γ + A) < (Γ + A + suc v)
lemma3 zero {zero} {v} = suc-pos v
lemma3 zero {suc A} {v} = suc-pres-< (lemma3 zero)
lemma3 (suc Γ) {A} {v} = suc-pres-< (lemma3 Γ)

lemma4 : (Γ : ℕ) {A v : ℕ} → 0 < A → (Γ + suc v) < (Γ + A + suc v)
lemma4 zero {A} {v} eq = <-pos _ _ eq
lemma4 (suc Γ) {A} {v} eq = suc-pres-< (lemma4 Γ eq)

{- [sizeTy' A] (resp. [sizeTm' u]) is a list of the same length as the number of
   premises as the corresponding rule, and each number is the sum of the sizes
   of all types/terms appearing in the corresponding premise.
   For term premises, the type doesn’t count (for instance for [id], we do not
   count the [A] for the premises corresponding to [u] and [v]), but the types
   of bound variables do count. -}

sizeTy' : TyExpr n → List ℕ
sizeTm' : TmExpr n → List ℕ

sizeTy : TyExpr n → ℕ
sizeTy A = suc (+-it (sizeTy' A))

sizeTm : TmExpr n → ℕ
sizeTm u = suc (+-it (sizeTm' u))

sizeTy' (uu i) = []
sizeTy' (el i v) = sizeTm v ∷ []
sizeTy' (pi A B) = sizeTy A ∷ (sizeTy A + sizeTy B) ∷ []
sizeTy' (sig A B) = sizeTy A ∷ (sizeTy A + sizeTy B) ∷ []
sizeTy' nat = []
sizeTy' (id A u v) = sizeTy A ∷ sizeTm u ∷ sizeTm v ∷ []

sizeTm' (var _) = []

sizeTm' (uu i) = []

sizeTm' (pi i a b) = sizeTm a ∷ (sizeTy (el i a) + sizeTm b) ∷ []
sizeTm' (lam A B u) = sizeTy A ∷ (sizeTy A + sizeTy B) ∷ (sizeTy A + sizeTm u) ∷ []
sizeTm' (app A B f a) = sizeTy A ∷ (sizeTy A + sizeTy B) ∷ sizeTm f ∷ sizeTm a ∷ []

sizeTm' (sig i a b) = sizeTm a ∷ (sizeTy (el i a) + sizeTm b) ∷ []
sizeTm' (pair A B a b) = sizeTy A ∷ (sizeTy A + sizeTy B) ∷ sizeTm a ∷ sizeTm b ∷ []
sizeTm' (pr1 A B u) = sizeTy A ∷ (sizeTy A + sizeTy B) ∷ sizeTm u ∷ []
sizeTm' (pr2 A B u) = sizeTy A ∷ (sizeTy A + sizeTy B) ∷ sizeTm u ∷ []

sizeTm' (nat i) = []
sizeTm' zero = []
sizeTm' (suc u) = sizeTm u ∷ []
sizeTm' {n = n} (natelim P dO dS u) = (sizeTy {n = n} nat + sizeTy P) ∷ sizeTm dO ∷ (sizeTy {n = n} nat + sizeTy P + sizeTm dS) ∷ sizeTm u ∷ []

sizeTm' (id i a u v) = sizeTm a ∷ sizeTm u ∷ sizeTm v ∷ []
sizeTm' (refl A u) = sizeTy A ∷ sizeTm u ∷ []
sizeTm' (jj A P d a b p) = sizeTy A ∷ (sizeTy A + sizeTy A + suc (sizeTy A) + sizeTy P) ∷ (sizeTy A + sizeTm d) ∷ sizeTm a ∷ sizeTm b ∷ sizeTm p ∷ []

sizeCtx : Ctx n → ℕ
sizeCtx ◇ = 0
sizeCtx (Γ , A) = sizeCtx Γ + sizeTy A

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
  dmor ((Γ , C [ δ ]Ty) , (dΓ , SubstTy dC dδ)) ((Δ , C) , (dΔ , dC)) (weakenMor δ , (var last)) (WeakMor dδ , (congTm (weaken[]Ty C δ last) refl (VarLast (SubstTy dC dδ))))

split-eq : (δ : DMor n (suc m)) → rhs (split-left δ) ≡ lhs (split-right δ)
split-eq (dmor (Γ , dΓ) ((Δ , C) , (dΔ , dC)) (δ , u) (dδ , du)) = refl

split-comp : (δ : DMor n (suc m)) → compS-// (split-right δ) (split-left δ) _ refl (ap proj (split-eq δ)) ≡ δ
split-comp (dmor (Γ , dΓ) ((Δ , C) , (dΔ , dC)) (δ , u) (dδ , du)) =
  ap-irr (λ x z → dmor (Γ , dΓ) ((Δ , C) , (dΔ , dC)) x z) (ap (λ x → x , u) (weakenMorInsert _ _ _ ∙ [idMor]Mor δ))

module _ (sf+ sg+ : StructuredCCatMor+ strSynCCat sC) where

  private
    sf = strucCCat→ sf+
    sg = strucCCat→ sg+
    f = ccat→ sf
    g = ccat→ sg

  TmToMor : {Γ : Ctx n} (dΓ : ⊢ Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → DMor n (suc n)
  TmToMor dΓ dA du = dmor (_ , dΓ) ((_ , _) , (dΓ , dA)) (idMor _ , _) (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl du)

  TmToMorₛ : {Γ : Ctx n} (dΓ : ⊢ Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → S.is-section (proj (TmToMor dΓ dA du))
  TmToMorₛ dΓ dA du = S.is-section→ (eq (box (CtxRefl dΓ) (CtxRefl dΓ) (MorSymm dΓ dΓ (congMorRefl (! (weakenMorInsert _ _ _ ∙ idMor[]Mor _)) (idMorDerivable dΓ)))))

  uniqueness-Ob-// : (Γ : DCtx n) (IH : Acc (sizeCtx (ctx Γ))) → Ob→ f (proj Γ) ≡ Ob→ g (proj Γ)
  uniqueness-Tm-// : {Γ : Ctx n} (dΓ : ⊢ Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) (IH : Acc (sizeCtx Γ + sizeTm u)) → Mor→ f (proj (TmToMor dΓ dA du)) ≡ Mor→ g (proj (TmToMor dΓ dA du))

  uniqueness-Ob-// (◇ , tt) (acc IH) = pt→ f ∙ ! (pt→ g)
  uniqueness-Ob-// ((Γ , uu i) , (dΓ , UU)) (acc IH) =
    UUStr→ sf i (proj (Γ , dΓ))
    ∙ ap (UUStr sC i) (uniqueness-Ob-// (Γ , dΓ) (IH <-ctx))
    ∙ ! (UUStr→ sg i (proj (Γ , dΓ)))
  uniqueness-Ob-// ((Γ , el i v) , (dΓ , El dv)) (acc IH) =
    ElStr→ sf i (proj (Γ , dΓ)) (proj (TmToMor dΓ UU dv)) (TmToMorₛ dΓ UU dv) refl
    ∙ ap-irr-ElStr (uniqueness-Ob-// (Γ , dΓ) (IH <-ctx)) (uniqueness-Tm-// dΓ UU dv (IH (<-+-it 0)))
    ∙ ! (ElStr→ sg i (proj (Γ , dΓ)) (proj (TmToMor dΓ UU dv)) (TmToMorₛ dΓ UU dv) refl)
  uniqueness-Ob-// ((Γ , pi A B) , (dΓ , Pi dA dB)) (acc IH) =
    PiStr→ sf (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl
    ∙ ap-irr-PiStr (uniqueness-Ob-// (Γ , dΓ) (IH <-ctx)) (uniqueness-Ob-// ((Γ , A) , (dΓ , dA)) (IH (<-+-it 0))) (uniqueness-Ob-// (((Γ , A) , B) , ((dΓ , dA) , dB)) (IH (<-+-it' 1 (+suc+-lemma _ _ _))))
    ∙ ! (PiStr→ sg (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl)
  uniqueness-Ob-// ((Γ , sig A B) , (dΓ , Sig dA dB)) (acc IH) =
    SigStr→ sf (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl
    ∙ ap-irr-SigStr (uniqueness-Ob-// (Γ , dΓ) (IH <-ctx)) (uniqueness-Ob-// ((Γ , A) , (dΓ , dA)) (IH (<-+-it 0))) (uniqueness-Ob-// (((Γ , A) , B) , ((dΓ , dA) , dB)) (IH (<-+-it' 1 (+suc+-lemma _ _ _))))
    ∙ ! (SigStr→ sg (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl)
  uniqueness-Ob-// ((Γ , nat) , (dΓ , Nat)) (acc IH) =
    NatStr→ sf (proj (Γ , dΓ))
    ∙ ap (NatStr sC) (uniqueness-Ob-// (Γ , dΓ) (IH <-ctx))
    ∙ ! (NatStr→ sg (proj (Γ , dΓ)))
  uniqueness-Ob-// ((Γ , id A u v) , (dΓ , Id dA du dv)) (acc IH) =
    IdStr→ sf (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (TmToMor dΓ dA du)) (TmToMorₛ dΓ dA du) refl (proj (TmToMor dΓ dA dv)) (TmToMorₛ dΓ dA dv) refl
    ∙ ap-irr-IdStr sC
                   (uniqueness-Ob-// (Γ , dΓ) (IH <-ctx))
                   (uniqueness-Ob-// _ (IH (<-+-it 0)))
                   (uniqueness-Tm-// dΓ dA du (IH (<-+-it 1)))
                   (uniqueness-Tm-// dΓ dA dv (IH (<-+-it 2)))
    ∙ ! (IdStr→ sg (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (TmToMor dΓ dA du)) (TmToMorₛ dΓ dA du) refl (proj (TmToMor dΓ dA dv)) (TmToMorₛ dΓ dA dv) refl)

  uniqueness-Tm-// {Γ = Γ , A} (dΓ , dA) _ (VarLast dA) (acc IH) =
    ap (Mor→ f) (eq (box (CtxRefl (dΓ , dA)) (CtxRefl (dΓ , dA) ,, congTyRefl (WeakTy dA) (! (ap weakenTy ([idMor]Ty _)) ∙ weaken[]Ty A (idMor _) last)) (MorRefl (idMorDerivable (dΓ , dA) , (congTm (! ([idMor]Ty (weakenTy A))) refl (VarLast dA))))))
    ∙ ss→ f {f = proj (dmor ((Γ , A) , (dΓ , dA)) ((Γ , A) , (dΓ , dA)) (idMor _) (idMorDerivable (dΓ , dA)))}
    ∙ ap ss (id→ f ∙ ap idC (uniqueness-Ob-// ((Γ , A) , (dΓ , dA)) (IH (lemma3 (sizeCtx Γ)))) ∙ ! (id→ g))
    ∙ ! (ss→ g {f = proj (dmor ((Γ , A) , (dΓ , dA)) ((Γ , A) , (dΓ , dA)) (idMor _) (idMorDerivable (dΓ , dA)))})
    ∙ ! (ap (Mor→ g) (eq (box (CtxRefl (dΓ , dA)) (CtxRefl (dΓ , dA) ,, congTyRefl (WeakTy dA) (! (ap weakenTy ([idMor]Ty _)) ∙ weaken[]Ty A (idMor _) last)) (MorRefl (idMorDerivable (dΓ , dA) , (congTm (! ([idMor]Ty (weakenTy A))) refl (VarLast dA)))))))
  uniqueness-Tm-// {Γ = Γ , A} (dΓ , dA) _ (VarPrev {k = x} {A = B} dB dx) (acc IH) =
    ap (Mor→ f) (eq (box (CtxRefl (dΓ , dA)) (CtxRefl (dΓ , dA) ,, congTyRefl (WeakTy dB) (ap weakenTy (! ([idMor]Ty B)) ∙ weaken[]Ty B (idMor _) last ∙ ap (λ z → B [ z ]Ty) (! (idMor[]Mor _)))) (MorRefl (idMorDerivable (dΓ , dA)) , congTmRefl (congTm (! ([idMor]Ty _)) refl (VarPrev dB dx)) (ap weakenTm (! ([idMor]Tm (var x))) ∙ weaken[]Tm (var x) (idMor _) last))))
    ∙ ss→ f {f = proj (dmor ((Γ , A) , (dΓ , dA)) ((Γ , B) , (dΓ , dB)) (idMor _ [ weakenMor (idMor _) ]Mor , var x [ weakenMor' last (idMor _) ]Tm) (SubstMor (idMorDerivable dΓ) (WeakMor (idMorDerivable dΓ)) , congTm (ap (λ z → B [ z ]Ty) (! (idMor[]Mor _))) refl (SubstTm dx (WeakMor (idMorDerivable dΓ)))))}
    ∙ ap ss (comp→ f {g = proj (dmor (Γ , dΓ) ((Γ , B) , (dΓ , dB)) (idMor _ , var x) (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl dx))} {f = ppS (proj ((Γ , A) , (dΓ , dA)))} {g₀ = refl} {f₁ = refl}
            ∙ ap-irr-comp (uniqueness-Tm-// dΓ dB dx (IH (lemma4 (sizeCtx Γ) (sizeTy-pos A))))
                          (pp→ f {X = proj ((Γ , A) , (dΓ , dA))}
                           ∙ ap pp (uniqueness-Ob-// ((Γ , A) , (dΓ , dA)) (IH (lemma3 (sizeCtx Γ))))
                           ∙ ! (pp→ g {X = proj ((Γ , A) , (dΓ , dA))}))
            ∙ ! (comp→ g {g = proj (dmor (Γ , dΓ) ((Γ , B) , (dΓ , dB)) (idMor _ , var x) (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl dx))} {f = ppS (proj ((Γ , A) , (dΓ , dA)))} {g₀ = refl} {f₁ = refl}))
    ∙ ! (ss→ g {f = proj (dmor ((Γ , A) , (dΓ , dA)) ((Γ , B) , (dΓ , dB)) (idMor _ [ weakenMor (idMor _) ]Mor , var x [ weakenMor' last (idMor _) ]Tm) (SubstMor (idMorDerivable dΓ) (WeakMor (idMorDerivable dΓ)) , congTm (ap (λ z → B [ z ]Ty) (! (idMor[]Mor _))) refl (SubstTm dx (WeakMor (idMorDerivable dΓ)))))})
    ∙ ! (ap (Mor→ g) (eq (box (CtxRefl (dΓ , dA)) (CtxRefl (dΓ , dA) ,, congTyRefl (WeakTy dB) (ap weakenTy (! ([idMor]Ty B)) ∙ weaken[]Ty B (idMor _) last ∙ ap (λ z → B [ z ]Ty) (! (idMor[]Mor _)))) (MorRefl (idMorDerivable (dΓ , dA)) , congTmRefl (congTm (! ([idMor]Ty _)) refl (VarPrev dB dx)) (ap weakenTm (! ([idMor]Tm (var x))) ∙ weaken[]Tm (var x) (idMor _) last)))))

  uniqueness-Tm-// dΓ _ (Conv dA du dA=) (acc IH) =
    ap (Mor→ f) (! (eq (box (CtxRefl dΓ) (CtxRefl dΓ ,, dA=) (MorRefl (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl du)))))
    ∙ uniqueness-Tm-// dΓ dA du (acc IH)
    ∙ ! (ap (Mor→ g) (! (eq (box (CtxRefl dΓ) (CtxRefl dΓ ,, dA=) (MorRefl (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl du))))))

  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = uu i} UUUU (acc IH) =
    uuStr→ sf i (proj (Γ , dΓ))
    ∙ ap (uuStr sC i) (uniqueness-Ob-// _ (IH <-ctx))
    ∙ ! (uuStr→ sg i (proj (Γ , dΓ)))

  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = pi i a b} (PiUU da db) (acc IH) =
    piStr→ sf i (proj (Γ , dΓ)) (proj (TmToMor dΓ UU da)) (TmToMorₛ dΓ UU da) refl (proj (TmToMor (dΓ , El da) UU db)) (TmToMorₛ (dΓ , El da) UU db) refl
    ∙ ap-irr-piStr (uniqueness-Ob-// _ (IH <-ctx))
                   (uniqueness-Tm-// dΓ UU da (IH (<-+-it 0)))
                   (uniqueness-Tm-// (dΓ , El da) UU db (IH (<-+-it' 1 (+suc+-lemma _ _ _))))
    ∙ ! (piStr→ sg i (proj (Γ , dΓ)) (proj (TmToMor dΓ UU da)) (TmToMorₛ dΓ UU da) refl (proj (TmToMor (dΓ , El da) UU db)) (TmToMorₛ (dΓ , El da) UU db) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = lam A B u} (Lam dA dB du) (acc IH) =
    lamStr→ sf (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl (proj (TmToMor (dΓ , dA) dB du)) (TmToMorₛ (dΓ , dA) dB du) refl
    ∙ ap-irr-lamStr (uniqueness-Ob-// _ (IH <-ctx))
                    (uniqueness-Ob-// _ (IH (<-+-it 0)))
                    (uniqueness-Ob-// _ (IH (<-+-it' 1 (+suc+-lemma _ _ _))))
                    (uniqueness-Tm-// (dΓ , dA) dB du (IH (<-+-it' 2 (+suc+-lemma _ _ _))))
    ∙ ! (lamStr→ sg (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl (proj (TmToMor (dΓ , dA) dB du)) (TmToMorₛ (dΓ , dA) dB du) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = app A B f a} (App dA dB df da) (acc IH) =
    appStr→ sf (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl (proj (TmToMor dΓ (Pi dA dB) df)) (TmToMorₛ dΓ (Pi dA dB) df) refl (proj (TmToMor dΓ dA da)) (TmToMorₛ dΓ dA da) refl
    ∙ ap-irr-appStr (uniqueness-Ob-// _ (IH <-ctx))
                    (uniqueness-Ob-// _ (IH (<-+-it 0)))
                    (uniqueness-Ob-// _ (IH (<-+-it' 1 (+suc+-lemma _ _ _))))
                    (uniqueness-Tm-// dΓ (Pi dA dB) df (IH (<-+-it 2)))
                    (uniqueness-Tm-// dΓ dA da (IH (<-+-it 3)))
    ∙ ! (appStr→ sg (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl (proj (TmToMor dΓ (Pi dA dB) df)) (TmToMorₛ dΓ (Pi dA dB) df) refl (proj (TmToMor dΓ dA da)) (TmToMorₛ dΓ dA da) refl)

  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = sig i a b} (SigUU da db) (acc IH) =
    sigStr→ sf i (proj (Γ , dΓ)) (proj (TmToMor dΓ UU da)) (TmToMorₛ dΓ UU da) refl (proj (TmToMor (dΓ , El da) UU db)) (TmToMorₛ (dΓ , El da) UU db) refl
    ∙ ap-irr-sigStr (uniqueness-Ob-// _ (IH <-ctx))
                    (uniqueness-Tm-// dΓ UU da (IH (<-+-it 0)))
                    (uniqueness-Tm-// (dΓ , El da) UU db (IH (<-+-it' 1 (+suc+-lemma _ _ _))))
    ∙ ! (sigStr→ sg i (proj (Γ , dΓ)) (proj (TmToMor dΓ UU da)) (TmToMorₛ dΓ UU da) refl (proj (TmToMor (dΓ , El da) UU db)) (TmToMorₛ (dΓ , El da) UU db) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = pair A B a b} (Pair dA dB da db) (acc IH) =
    pairStr→ sf (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl (proj (TmToMor dΓ dA da)) (TmToMorₛ dΓ dA da) refl (proj (TmToMor dΓ (SubstTy dB (idMor+ dΓ da)) db)) (TmToMorₛ dΓ (SubstTy dB (idMor+ dΓ da)) db) refl
    ∙ ap-irr-pairStr (uniqueness-Ob-// _ (IH <-ctx))
                     (uniqueness-Ob-// _ (IH (<-+-it 0)))
                     (uniqueness-Ob-// _ (IH (<-+-it' 1 (+suc+-lemma _ _ _))))
                     (uniqueness-Tm-// dΓ dA da (IH (<-+-it 2)))
                     (uniqueness-Tm-// dΓ (SubstTy dB (idMor+ dΓ da)) db (IH (<-+-it 3)))
    ∙ ! (pairStr→ sg (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl (proj (TmToMor dΓ dA da)) (TmToMorₛ dΓ dA da) refl (proj (TmToMor dΓ (SubstTy dB (idMor+ dΓ da)) db)) (TmToMorₛ dΓ (SubstTy dB (idMor+ dΓ da)) db) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = pr1 A B u} (Pr1 dA dB du) (acc IH) =
    pr1Str→ sf (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl (proj (TmToMor dΓ (Sig dA dB) du)) (TmToMorₛ dΓ (Sig dA dB) du) refl
    ∙ ap-irr-pr1Str (uniqueness-Ob-// _ (IH <-ctx))
                    (uniqueness-Ob-// _ (IH (<-+-it 0)))
                    (uniqueness-Ob-// _ (IH (<-+-it' 1 (+suc+-lemma _ _ _))))
                    (uniqueness-Tm-// dΓ (Sig dA dB) du (IH (<-+-it 2)))
    ∙ ! (pr1Str→ sg (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl (proj (TmToMor dΓ (Sig dA dB) du)) (TmToMorₛ dΓ (Sig dA dB) du) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = pr2 A B u} (Pr2 dA dB du) (acc IH) =
    pr2Str→ sf (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl (proj (TmToMor dΓ (Sig dA dB) du)) (TmToMorₛ dΓ (Sig dA dB) du) refl
    ∙ ap-irr-pr2Str (uniqueness-Ob-// _ (IH <-ctx))
                    (uniqueness-Ob-// _ (IH (<-+-it 0)))
                    (uniqueness-Ob-// _ (IH (<-+-it' 1 (+suc+-lemma _ _ _))))
                    (uniqueness-Tm-// dΓ (Sig dA dB) du (IH (<-+-it 2)))
    ∙ ! (pr2Str→ sg (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) refl (proj (TmToMor dΓ (Sig dA dB) du)) (TmToMorₛ dΓ (Sig dA dB) du) refl)

  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = nat i} NatUU (acc IH) =
    natStr→ sf i (proj (Γ , dΓ))
    ∙ ap (natStr sC i) (uniqueness-Ob-// _ (IH <-ctx))
    ∙ ! (natStr→ sg i (proj (Γ , dΓ)))
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = zero} Zero (acc IH) =
    zeroStr→ sf (proj (Γ , dΓ))
    ∙ ap (zeroStr sC) (uniqueness-Ob-// _ (IH <-ctx))
    ∙ ! (zeroStr→ sg (proj (Γ , dΓ)))
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = suc u} (Suc du) (acc IH) =
    sucStr→ sf (proj (Γ , dΓ)) (proj (TmToMor dΓ Nat du)) (TmToMorₛ dΓ Nat du) refl
    ∙ ap-irr-sucStr sC (uniqueness-Ob-// _ (IH <-ctx))
                       (uniqueness-Tm-// dΓ Nat du (IH (<-+-it 0)))
    ∙ ! (sucStr→ sg (proj (Γ , dΓ)) (proj (TmToMor dΓ Nat du)) (TmToMorₛ dΓ Nat du) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = natelim P dO dS u} (Natelim dP ddO ddS du) (acc IH) =
    let ddS₁ = SubstTy (WeakTy (WeakTy dP)) (idMorDerivable ((dΓ , Nat) , dP) , Suc (VarPrev Nat (VarLast Nat))) {-WeakTy (SubstTy (WeakTy dP) (idMorDerivable (dΓ , Nat) , Suc (VarLast Nat)))-} in
    natelimStr→ sf+ (proj (Γ , dΓ)) (proj (((Γ , nat) , P) , ((dΓ , Nat) , dP))) refl
                    (proj (TmToMor dΓ (SubstTy dP (idMorDerivable dΓ , Zero)) ddO)) (TmToMorₛ dΓ (SubstTy dP (idMorDerivable dΓ , Zero)) ddO) refl
                    (proj (TmToMor ((dΓ , Nat) , dP) ddS₁ ddS)) (TmToMorₛ ((dΓ , Nat) , dP) ddS₁ ddS) (eq {R = ObEquiv} (box (CtxRefl ((dΓ , Nat) , dP) ,, congTyRefl ddS₁ fixSubstTy)))
                    (proj (TmToMor dΓ Nat du)) (TmToMorₛ dΓ Nat du) refl
    ∙ ap-irr-natelimStr (uniqueness-Ob-// _ (IH <-ctx))
                        (uniqueness-Ob-// _ (IH (<-+-it' 0 (+suc+-lemma _ _ _))))
                        (uniqueness-Tm-// dΓ (SubstTy dP (idMorDerivable dΓ , Zero)) ddO (IH (<-+-it 1)))
                        (uniqueness-Tm-// ((dΓ , Nat) , dP) ddS₁ ddS (IH (<-+-it' 2 (+suc+-lemma2 _ _ _ _))))
                        (uniqueness-Tm-// dΓ Nat du (IH (<-+-it 3)))
    ∙ ! (natelimStr→ sg+ (proj (Γ , dΓ)) (proj (((Γ , nat) , P) , ((dΓ , Nat) , dP))) refl
                         (proj (TmToMor dΓ (SubstTy dP (idMorDerivable dΓ , Zero)) ddO)) (TmToMorₛ dΓ (SubstTy dP (idMorDerivable dΓ , Zero)) ddO) refl
                         (proj (TmToMor ((dΓ , Nat) , dP) ddS₁ ddS)) (TmToMorₛ ((dΓ , Nat) , dP) ddS₁ ddS) (eq {R = ObEquiv} (box (CtxRefl ((dΓ , Nat) , dP) ,, congTyRefl ddS₁ fixSubstTy)))
                         (proj (TmToMor dΓ Nat du)) (TmToMorₛ dΓ Nat du) refl)

  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = id i a u v} (IdUU da du dv) (acc IH) =
    idStr→ sf i (proj (Γ , dΓ)) (proj (TmToMor dΓ UU da)) (TmToMorₛ dΓ UU da) refl (proj (TmToMor dΓ (El da) du)) (TmToMorₛ dΓ (El da) du) refl (proj (TmToMor dΓ (El da) dv)) (TmToMorₛ dΓ (El da) dv) refl
    ∙ ap-irr-idStr (uniqueness-Ob-// _ (IH <-ctx))
                   (uniqueness-Tm-// dΓ UU da (IH (<-+-it 0)))
                   (uniqueness-Tm-// dΓ (El da) du (IH (<-+-it 1)))
                   (uniqueness-Tm-// dΓ (El da) dv (IH (<-+-it 2)))
    ∙ ! (idStr→ sg i (proj (Γ , dΓ)) (proj (TmToMor dΓ UU da)) (TmToMorₛ dΓ UU da) refl (proj (TmToMor dΓ (El da) du)) (TmToMorₛ dΓ (El da) du) refl (proj (TmToMor dΓ (El da) dv)) (TmToMorₛ dΓ (El da) dv) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = refl A u} (Refl dA du) (acc IH) =
    reflStr→ sf (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (TmToMor dΓ dA du)) (TmToMorₛ dΓ dA du) refl
    ∙ ap-irr-reflStr sC (uniqueness-Ob-// _ (IH <-ctx))
                       (uniqueness-Ob-// _ (IH (<-+-it 0)))
                       (uniqueness-Tm-// dΓ dA du (IH (<-+-it 1)))
    ∙ ! (reflStr→ sg (proj (Γ , dΓ)) (proj ((Γ , A) , (dΓ , dA))) refl (proj (TmToMor dΓ dA du)) (TmToMorₛ dΓ dA du) refl)
  uniqueness-Tm-// {Γ = Γ} dΓ _ {u = jj A P d a b p} (JJ dA dP dd da db dp) (acc IH) = #TODO#
    {!-jjStr→ sf+ (proj (Γ , dΓ))
                (proj ?) ?
                (proj ?) ?
                (proj (TmToMor ? ? ?)) (TmToMorₛ ? ? ?) ?
                (proj (TmToMor ? ? ?)) (TmToMorₛ ? ? ?) ?
                (proj (TmToMor ? ? ?)) (TmToMorₛ ? ? ?) ?
                (proj (TmToMor ? ? ?)) (TmToMorₛ ? ? ?) ?
     ∙ ap-irr-jjStr ? ? ? ? ? ? ? ∙
     ! (jjStr→ sg+ (proj (Γ , dΓ))
                   (proj ?) ?
                   (proj ?) ?
                   (proj (TmToMor ? ? ?)) (TmToMorₛ ? ? ?) ?
                   (proj (TmToMor ? ? ?)) (TmToMorₛ ? ? ?) ?
                   (proj (TmToMor ? ? ?)) (TmToMorₛ ? ? ?) ?
                   (proj (TmToMor ? ? ?)) (TmToMorₛ ? ? ?) ?)-!}

  uniqueness-Ob : (X : ObS n) → Ob→ f X ≡ Ob→ g X
  uniqueness-Ob = //-elimP (λ Γ → uniqueness-Ob-// Γ (WO-Nat _))

  uniqueness-Mor-// : (δ : DMor n m) → Mor→ f (proj δ) ≡ Mor→ g (proj δ)
  uniqueness-Mor-// (dmor (Γ , dΓ) (◇ , tt) ◇ tt) = ptmor→ f {X = proj (Γ , dΓ)} ∙ ap ptmor (uniqueness-Ob-// (Γ , dΓ) (WO-Nat _)) ∙ ! (ptmor→ g)
  uniqueness-Mor-// δδ@(dmor (Γ , dΓ) ((Δ , C) , (dΔ , dC)) (δ , u) (dδ , du)) =
    ap (Mor→ f) (ap proj (! (split-comp δδ)))
    ∙ comp→ f {g = proj (split-right δδ)} {f = proj (split-left δδ)} {g₀ = refl} {f₁ = refl}
    ∙ ap-irr-comp (qq→ f {f = proj (dmor (Γ , dΓ) (Δ , dΔ) δ dδ)} {X = proj ((Δ , C) , (dΔ , dC))} {q = refl} {f₁ = refl}
                  ∙ ap-irr-qq (uniqueness-Mor-// (dmor (Γ , dΓ) (Δ , dΔ) δ dδ)) (uniqueness-Ob-// ((Δ , C) , (dΔ , dC)) (WO-Nat _))
                  ∙ ! (qq→ g {f = proj (dmor (Γ , dΓ) (Δ , dΔ) δ dδ)} {X = proj ((Δ , C) , (dΔ , dC))} {q = refl} {f₁ = refl}))
                  (uniqueness-Tm-// dΓ (SubstTy dC dδ) du (WO-Nat _))
    ∙ ! (comp→ g {g = proj (split-right δδ)} {f = proj (split-left δδ)} {g₀ = refl} {f₁ = refl})
    ∙ ! (ap (Mor→ g) (ap proj (! (split-comp δδ))))

  uniqueness-Mor : (X : MorS n m) → Mor→ f X ≡ Mor→ g X
  uniqueness-Mor = //-elimP uniqueness-Mor-//

  uniqueness : sf ≡ sg
  uniqueness = structuredCCatMorEq uniqueness-Ob uniqueness-Mor
