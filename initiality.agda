{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import typetheory
open import syntx hiding (Mor)
open import rules
open import contextualcat
open import quotients
open import termmodel
import partialinterpretation
import totality

module _ (sC : StructuredCCat) where

open StructuredCCat
open CCatMor
open partialinterpretation sC
module S = partialinterpretation strSynCCat
open totality sC
open StructuredCCatMor

private
  C = ccat sC

open CCat C renaming (id to idC)

{- Existence of a morphism between the contextual categories (not yet structured) -}

Ob/ : DCtx n → Ob n
Ob/ (Γ , dΓ) = ⟦ Γ ⟧Ctx $ ⟦⟧Ctxᵈ dΓ

Ob/-eq : {Γ Γ' : DCtx n} → ⊢ ctx Γ == ctx Γ' → Ob/ Γ ≡ Ob/ Γ'
Ob/-eq dΓ= = ⟦⟧CtxEq dΓ=

Ob→S : ObS n → Ob n
Ob→S = //-rec Ob/ (λ {a} {b} r → Ob/-eq {Γ = a} {Γ' = b} r)

Mor/ : DMor n m → Mor n m
Mor/ (dmor Γd Δd δ dδ) = ⟦ δ ⟧Mor (Ob/ Γd) (Ob/ Δd) $ ⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ

Mor/-eq : {δ δ' : DMor n m} → ((⊢ ctx (lhs δ) == ctx (lhs δ')) × (⊢ ctx (rhs δ) == ctx (rhs δ'))) ×
                              (ctx (lhs δ) ⊢ mor δ == mor δ' ∷> ctx (rhs δ))
                            → Mor/ δ ≡ Mor/ δ'
Mor/-eq {δ = dmor (Γ , dΓ) (Δ , dΔ) δ dδ} {δ' = dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ'} ((dΓ= , dΔ=) , dδ=) =
  ⟦⟧MorEq {Γ' = Γ'} {Δ' = Δ'} respects⟦⟧Ctx dδ= {δ'ᵈ = ⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx (MorEqMor2 dΓ dΔ dδ=)}
  ∙ ap2-irr (λ x y z → ⟦_⟧Mor δ' x y $ z) (⟦⟧CtxEq dΓ=) (⟦⟧CtxEq dΔ=)

Mor→S : MorS n m → Mor n m
Mor→S = //-rec Mor/ (λ {a} {b} r → Mor/-eq {δ = a} {δ' = b} r)

∂₀/ : (X : DMor n m) → Ob→S (∂₀S (proj X)) ≡ ∂₀ (Mor→S (proj X))
∂₀/ X@(dmor (Γ , dΓ) _ δ dδ) = ! (⟦⟧Mor₀ δ {δᵈ = ⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ})

∂₀→S : (X : MorS n m) → Ob→S (∂₀S X) ≡ ∂₀ (Mor→S X)
∂₀→S = //-elimP ∂₀/

∂₁/ : (X : DMor n m) → Ob→S (∂₁S (proj X)) ≡ ∂₁ (Mor→S (proj X))
∂₁/ X@(dmor (Γ , dΓ) _ δ dδ) = ! (⟦⟧Mor₁ δ {δᵈ = ⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ})

∂₁→S : (X : MorS n m) → Ob→S (∂₁S X) ≡ ∂₁ (Mor→S X)
∂₁→S = //-elimP ∂₁/

id/ : (X : DCtx n) → Mor→S (idS n (proj X)) ≡ idC (Ob→S (proj X))
id/ (Γ , dΓ) = ⟦idMor⟧= refl

id→S : (X : ObS n) → Mor→S (idS n X) ≡ idC (Ob→S X)
id→S = //-elimP id/

comp/ : (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) → Mor→S (compS (proj g) (proj f) p) ≡ comp (Mor→S (proj g)) (Mor→S (proj f)) (! (∂₁→S (proj f)) ∙ ap Ob→S p ∙ ∂₀→S (proj g))
comp/ (dmor _ _ θ dθ) (dmor _ _ δ dδ) p = ⟦tsubst⟧Mor= (⟦⟧CtxEq (reflect p)) δ (⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ) θ (⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dθ)

comp→S : (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) → Mor→S (compS g f p) ≡ comp (Mor→S g) (Mor→S f) (! (∂₁→S f) ∙ ap Ob→S p ∙ ∂₀→S g)
comp→S = //-elimP (λ g → //-elimP (comp/ g))

ft/ : (X : DCtx (suc n)) → Ob→S (ftS (proj X)) ≡ ft (Ob→S (proj X))
ft/ ((Γ , A) , (dΓ , dA)) = ! (⟦⟧Ty-ft A)

ft→S : (X : ObS (suc n)) → Ob→S (ftS X) ≡ ft (Ob→S X)
ft→S = //-elimP ft/

pp/ : (X : DCtx (suc n)) → Mor→S (ppS (proj X)) ≡ pp (Ob→S (proj X))
pp/ ((Γ , A) , (dΓ , dA)) = ⟦weakenMor⟧= (ap ft (! pp₀)) (idMor _) (⟦idMor⟧ᵈ (! (ap ft pp₀ ∙ ⟦⟧Ty-ft A))) ∙ ap2-irr comp (⟦idMor⟧= (! (⟦⟧Ty-ft A) ∙ ap ft (! pp₀)) ∙ ap idC (! pp₁ ∙ ap ∂₁ (ap pp pp₀))) refl ∙ id-right

pp→S : (X : ObS (suc n)) → Mor→S (ppS X) ≡ pp (Ob→S X)
pp→S = //-elimP pp/

star/ : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → Ob→S (starS (proj f) (proj X) p) ≡ star (Mor→S (proj f)) (Ob→S (proj X)) (! (∂₁→S (proj f)) ∙ ap Ob→S p ∙ ft→S (proj X))
star/ (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) ((Δ' , A) , (dΔ' , dA')) p =
  let dA = ConvTy dA' (reflect (! p)) in
  ! (⟦tsubst⟧Ty= A (⟦⟧Tyᵈ respects⟦⟧Ctx dA) δ (⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ)) ∙ ap2-irr star refl (ap-irr (λ x z → ⟦ A ⟧Ty x $ z) (⟦⟧CtxEq (reflect p)))

star→S : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → Ob→S (starS f X p) ≡ star (Mor→S f) (Ob→S X) (! (∂₁→S f) ∙ ap Ob→S p ∙ ft→S X)
star→S = //-elimP (λ f → //-elimP (star/ f))

qq/ : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → Mor→S (qqS (proj f) (proj X) p) ≡ qq (Mor→S (proj f)) (Ob→S (proj X)) (! (∂₁→S (proj f)) ∙ ap Ob→S p ∙ ft→S (proj X))
qq/ (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) ((Δ' , A) , (dΔ' , dA')) p =
  let dA = ConvTy dA' (reflect (! p)) in
  ⟦weakenMor+⟧= (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A ∙ ⟦⟧CtxEq (reflect (! p))) δ (⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ) (ap2-irr star refl (ap-irr (λ x z → ⟦ A ⟧Ty x $ z) (! (⟦⟧CtxEq (reflect p)))) ∙ ⟦tsubst⟧Ty= A (⟦⟧Tyᵈ respects⟦⟧Ctx dA) δ (⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ))

qq→S : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → Mor→S (qqS f X p) ≡ qq (Mor→S f) (Ob→S X) (! (∂₁→S f) ∙ ap Ob→S p ∙ ft→S X)
qq→S = //-elimP (λ f → //-elimP (qq/ f))

ss/ : (f : DMor m (suc n)) → Mor→S (ssS (proj f)) ≡ ss (Mor→S (proj f))
ss/ (dmor (Γ , dΓ) ((Δ , A) , (dΔ , dA)) (δ , u) (dδ , du)) = ap2-irr comp (ap2-irr qq (⟦idMor⟧= (⟦⟧Ty-ft (A [ δ ]Ty)) ∙ ap idC (! (⟦⟧Ty-ft (A [ δ ]Ty)))) refl ∙ qq-id ∙ ap idC (! (⟦⟧Tm₁ respects⟦⟧Ctx du))) refl ∙ id-right ∙ ! (ss-of-section _ (⟦⟧Tmₛ u)) ∙ ss-comp {f₁ = ⟦⟧Tm₁ respects⟦⟧Ctx du ∙ ! (⟦tsubst⟧Ty= A (⟦⟧Tyᵈ aux dA) δ (⟦⟧Morᵈ respects⟦⟧Ctx aux dδ)) ∙ ap2-irr star refl (ap-irr (λ x z → ⟦ A ⟧Ty x $ z) (⟦⟧Ty-ft A))}  where

  aux : respectsCtx (ft (⟦ A ⟧Ty (⟦ Δ ⟧Ctx $ (⟦⟧Ctxᵈ dΔ)) $ (⟦⟧Tyᵈ respects⟦⟧Ctx dA))) Δ
  aux rewrite ⟦⟧Ty-ft {X = ⟦ Δ ⟧Ctx $ (⟦⟧Ctxᵈ dΔ)} A {⟦⟧Tyᵈ respects⟦⟧Ctx dA} = respects⟦⟧Ctx

ss→S : (f : MorS m (suc n)) → Mor→S (ssS f) ≡ ss (Mor→S f)
ss→S = //-elimP ss/

ptmor→S : (X : ObS n) → Mor→S (ptmorS X) ≡ ptmor (Ob→S X)
ptmor→S = //-elimP (λ _ → refl)

f₀ : CCatMor synCCat C
Ob→ f₀ = Ob→S
Mor→ f₀ = Mor→S
∂₀→ f₀ {X = X} = ∂₀→S X
∂₁→ f₀ {X = X} = ∂₁→S X
id→ f₀ {X = X} = id→S X
comp→ f₀ {g = g} {f = f} {p = p} = comp→S g f p
ft→ f₀ {X = X} = ft→S X
pp→ f₀ {X = X} = pp→S X
star→ f₀ {f = f} {X = X} {p = p} = star→S f X p
qq→ f₀ {f = f} {X = X} {p = p} = qq→S f X p
ss→ f₀ {f = f} = ss→S f
pt→ f₀ = refl
ptmor→ f₀ {X = X} = ptmor→S X


{- Existence of a morphism between the structured contextual categories -}

lemmaMorᵈ : (u : DMor n (suc n)) {X : Ob n} (u₀ : Ob→S (∂₀S (proj u)) ≡ X) → isDefined (⟦ Tm u ⟧Tm X)
lemmaMorᵈ uu@(dmor (Γu , dΓu) ((Γu' , Au) , (dΓu' , dAu)) (δu , u) (dδu , du~)) refl = ⟦⟧Tmᵈ respects⟦⟧Ctx du~

lemmaMor→S : (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) {Γ : DCtx (suc n)} {Γ' : DCtx n} (u₁ : ∂₁S (proj u) ≡ proj Γ) (p : proj {R = ObEquiv} (ftS-// Γ) ≡ proj Γ') {w : _}
           → ⟦ Tm u ⟧Tm (Ob/ Γ') $ w ≡ Mor→S (proj u)
lemmaMor→S uu@(dmor (Γu , dΓu) ((Γu' , Au) , (dΓu' , dAu)) (δu , u) (dδu , du~)) uₛ {((Γ , A) , (dΓ , dA))} {(Γ' , dA')} u₁ p =
  let δu= : Γu ⊢ δu == idMor _ ∷> Γu'
      δu= = congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor δu) refl (snd (reflect uₛ))

      du : Derivable (Γu ⊢ u :> Au)
      du = ConvTm2 du~ (CtxRefl dΓu) (congTyEq refl ([idMor]Ty Au) (SubstTyMorEq dAu dδu δu=))

      dΓu=' : ⊢ Γu' == Γu
      dΓu=' = snd (fst (reflect uₛ))

      dAu' : Derivable (Γu ⊢ Au)
      dAu' = ConvTy dAu dΓu='

      u₀ : ⟦ Γu ⟧Ctx $ ⟦⟧Ctxᵈ dΓu ≡ ⟦ Γ' ⟧Ctx $ ⟦⟧Ctxᵈ dA'
      u₀ = ⟦⟧CtxEq (CtxTran (CtxSymm dΓu=') (CtxTran (fst (reflect u₁)) (reflect p))) --(! (⟦⟧CtxEq dΓu=')) ∙ {!ap (λ z → Ob→S (ftS z)) u₁ !} ∙ ⟦⟧CtxEq (reflect p)
  in
  ! (ap2-irr comp (ap2-irr qq (⟦⟧MorEq {Γ' = Γu} {Δ' = Γu'} respects⟦⟧Ctx δu= ∙ ⟦idMor⟧= (⟦⟧Ty-ft Au ∙ ⟦⟧CtxEq dΓu=') ∙ ap idC (! (⟦⟧Ty-ft Au ∙ ⟦⟧CtxEq dΓu='))) refl ∙ qq-id ∙ ap idC (ap-irr (λ x z → ⟦ Au ⟧Ty (Ob→S x) $ z) (eq {a = Γu' , dΓu'} {b = Γu , dΓu} dΓu=') {b' = ⟦⟧Tyᵈ respects⟦⟧Ctx dAu'} ∙ ! (⟦⟧Tm₁ respects⟦⟧Ctx du))) refl ∙ id-right ∙ ap-irr (λ x z → ⟦ u ⟧Tm x $ z) u₀)

lemmaMor→S' : (u : DMor n (suc n)) (uₛ : is-sectionS (proj u))
           → Mor→S (proj u) ≡ ⟦ Tm u ⟧Tm (Ob→S (∂₀S (proj u))) $ lemmaMorᵈ u refl
lemmaMor→S' uu@(dmor (Γ , dΓ) ((Δ , A) , (dΔ , dA)) (δ , u) (dδ , du)) uₛ =
  ! (lemmaMor→S uu uₛ refl refl {w = ⟦⟧Tmᵈ respects⟦⟧Ctx (ConvTm du (CtxSymm (sectionS-eq-ctx {dA = dA} {dδ = dδ} {du = du} uₛ)))}) ∙ ap-irr (λ x z → ⟦ u ⟧Tm x $ z) (⟦⟧CtxEq (sectionS-eq-ctx {dA = dA} {dδ = dδ} {du = du} uₛ))


UUStr→S : (i : ℕ) (X : ObS n) → Ob→S (UUStrS i X) ≡ UUStr sC i (Ob→S X)
UUStr→S i = //-elimP (λ _ → refl)


ElStr/ : (i : ℕ) (v : DMor n (suc n)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ UUStrS i (∂₀S (proj v))) {w1 : _} {w2 : _} → Ob→S (ElStrS i (proj v) vₛ v₁) ≡ ElStr sC i (Mor→S (proj v)) w1 w2
ElStr/ i v vₛ v₁ = ap-irr2 (ElStr sC i) (lemmaMor→S v vₛ v₁ refl)

ElStr→S : (i : ℕ) (v : MorS n (suc n)) (vₛ : is-sectionS v) (v₁ : ∂₁S v ≡ UUStrS i (∂₀S v)) {w1 : _} {w2 : _} → Ob→S (ElStrS i v vₛ v₁) ≡ ElStr sC i (Mor→S v) w1 w2
ElStr→S i = //-elimP (ElStr/ i)


PiStr/ : (B : DCtx (suc (suc n))) → Ob→ f₀ (PiStrS (proj B)) ≡ PiStr sC (Ob→ f₀ (proj B))
PiStr/ (((Γ , A) , B) , ((dΓ , dA) , dB)) = refl

PiStr→S : (B : ObS (suc (suc n))) → Ob→ f₀ (PiStrS B) ≡ PiStr sC (Ob→ f₀ B)
PiStr→S = //-elimP PiStr/


SigStr/ : (B : DCtx (suc (suc n))) → Ob→ f₀ (SigStrS (proj B)) ≡ SigStr sC (Ob→ f₀ (proj B))
SigStr/ (((Γ , A) , B) , ((dΓ , dA) , dB)) = refl

SigStr→S : (B : ObS (suc (suc n))) → Ob→ f₀ (SigStrS B) ≡ SigStr sC (Ob→ f₀ B)
SigStr→S = //-elimP SigStr/


NatStr→S : (X : ObS n) → Ob→S (NatStrS X) ≡ NatStr sC (Ob→S X)
NatStr→S = //-elimP (λ _ → refl)


IdStr/ : (A : DCtx (suc n)) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ proj A) (v : DMor n (suc n)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ proj A)
         {w1 : _} {w2 : _} {w3 : _} {w4 : _}
       → Ob→ f₀ (IdStrS (proj A) (proj u) uₛ u₁ (proj v) vₛ v₁) ≡ IdStr sC (Ob→ f₀ (proj A)) (Mor→ f₀ (proj u)) w1 w2 (Mor→ f₀ (proj v)) w3 w4
IdStr/ ((Γ , A) , (dΓ , dA)) u uₛ u₁ v vₛ v₁ =
  ap-irr-IdStr refl
               (lemmaMor→S u uₛ u₁ refl)
               (lemmaMor→S v vₛ v₁ refl)

IdStr→S : (A : ObS (suc n)) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ A) (v : MorS n (suc n)) (vₛ : is-sectionS v) (v₁ : ∂₁S v ≡ A)
          {w1 : _} {w2 : _} {w3 : _} {w4 : _}
        → Ob→ f₀ (IdStrS A u uₛ u₁ v vₛ v₁) ≡ IdStr sC (Ob→ f₀ A) (Mor→ f₀ u) w1 w2 (Mor→ f₀ v) w3 w4
IdStr→S = //-elimP (λ A → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → IdStr/ A u uₛ u₁ v vₛ v₁)))


uuStr/ : (i : ℕ) (X : DCtx n)
        → Mor→ f₀ (uuStrS i (proj X)) ≡ uuStr sC i (Ob→ f₀ (proj X))
uuStr/ i (Γ , dΓ) =
  lemmaMor→S' (dmor (Γ , dΓ) (UUStrS-//-u (suc i) (Γ , dΓ)) ((idMor _ , uu i)) (idMor+ dΓ UUUU)) (uuStrₛS-// i (Γ , dΓ))

uuStr→S : (i : ℕ) (X : ObS n)
        → Mor→ f₀ (uuStrS i X) ≡ uuStr sC i (Ob→ f₀ X)
uuStr→S i = //-elimP (λ X → uuStr/ i X)


piStr/ : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (b : DMor (suc n) (suc (suc n))) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁))
         {w1 : _} {w2 : _} {w3 : _} {w4 : _}
       → Mor→ f₀ (piStrS i (proj a) aₛ a₁ (proj b) bₛ b₁) ≡ piStr sC i (Mor→ f₀ (proj a)) w1 w2 (Mor→ f₀ (proj b)) w3 w4
piStr/ i a aₛ a₁ b bₛ b₁ =
  lemmaMor→S' (piStrS-// i a aₛ a₁ b bₛ b₁) (piStrₛS-// i a aₛ a₁ b bₛ b₁)
  ∙ ap-irr-piStr (lemmaMor→S a aₛ a₁ refl) (lemmaMor→S b bₛ b₁ refl)

piStr→S : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (b : MorS (suc n) (suc (suc n))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁))
          {w1 : _} {w2 : _} {w3 : _} {w4 : _}
        → Mor→ f₀ (piStrS i a aₛ a₁ b bₛ b₁) ≡ piStr sC i (Mor→ f₀ a) w1 w2 (Mor→ f₀ b) w3 w4
piStr→S i = //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → piStr/ i a aₛ a₁ b bₛ b₁))


lamStr/ : (B : DCtx (suc (suc n))) (u : DMor (suc n) (suc (suc n))) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) {w1 : _} {w2 : _}
        → Mor→ f₀ (lamStrS (proj B) (proj u) uₛ u₁) ≡ lamStr sC (Ob→ f₀ (proj B)) (Mor→ f₀ (proj u)) w1 w2
lamStr/ B@(((_ , _) , B') , ((_ , _) , _)) u uₛ u₁ =
  lemmaMor→S' (lamStrS-// B u uₛ u₁) (lamStrₛS-// B u uₛ u₁)
  ∙ ap-irr-lamStr refl (lemmaMor→S u uₛ u₁ refl)

lamStr→S : (B : ObS (suc (suc n))) (u : MorS (suc n) (suc (suc n))) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ B) {w1 : _} {w2 : _}
        → Mor→ f₀ (lamStrS B u uₛ u₁) ≡ lamStr sC (Ob→S B) (Mor→S u) w1 w2
lamStr→S = //-elimP (λ B → //-elimP (lamStr/ B))


appStr/ : (B : DCtx (suc (suc n))) (f : DMor n (suc n)) (fₛ : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B))
           {w1 : _} {w2 : _} {w3 : _} {w4 : _}
        → Mor→ f₀ (appStrS (proj B) (proj f) fₛ f₁ (proj a) aₛ a₁) ≡ appStr sC (Ob→S (proj B)) (Mor→S (proj f)) w1 w2 (Mor→S (proj a)) w3 w4
appStr/ B@(((_ , A') , B') , ((_ , _) , _)) f fₛ f₁ a aₛ a₁ =
  lemmaMor→S' (appStrS-// B f fₛ f₁ a aₛ a₁) (appStrₛS-// B f fₛ f₁ a aₛ a₁)
  ∙ ap-irr-appStr refl
                  (lemmaMor→S f fₛ f₁ refl)
                  (lemmaMor→S a aₛ a₁ refl)

appStr→S : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fₛ : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B)
           {w1 : _} {w2 : _} {w3 : _} {w4 : _}
        → Mor→ f₀ (appStrS B f fₛ f₁ a aₛ a₁) ≡ appStr sC (Ob→S B) (Mor→S f) w1 w2 (Mor→S a) w3 w4
appStr→S = //-elimP (λ B → //-elimP (λ f fₛ f₁ → //-elimP (appStr/ B f fₛ f₁)))


sigStr/ : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (b : DMor (suc n) (suc (suc n))) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁))
         {w1 : _} {w2 : _} {w3 : _} {w4 : _}
       → Mor→ f₀ (sigStrS i (proj a) aₛ a₁ (proj b) bₛ b₁) ≡ sigStr sC i (Mor→ f₀ (proj a)) w1 w2 (Mor→ f₀ (proj b)) w3 w4
sigStr/ i a aₛ a₁ b bₛ b₁ =
  lemmaMor→S' (sigStrS-// i a aₛ a₁ b bₛ b₁) (sigStrₛS-// i a aₛ a₁ b bₛ b₁)
  ∙ ap-irr-sigStr (lemmaMor→S a aₛ a₁ refl)
                  (lemmaMor→S b bₛ b₁ refl)

sigStr→S : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (b : MorS (suc n) (suc (suc n))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁))
           {w1 : _} {w2 : _} {w3 : _} {w4 : _}
         → Mor→ f₀ (sigStrS i a aₛ a₁ b bₛ b₁) ≡ sigStr sC i (Mor→ f₀ a) w1 w2 (Mor→ f₀ b) w3 w4
sigStr→S i = //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → sigStr/ i a aₛ a₁ b bₛ b₁))


pairStr/ : (B : DCtx (suc (suc n))) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (b : DMor n (suc n)) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj B) a₁)
            {w1 : _} {w2 : _} {w3 : _} {w4 : _}
          → Mor→ f₀ (pairStrS (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁) ≡ pairStr sC (Ob→ f₀ (proj B)) (Mor→ f₀ (proj a)) w1 w2 (Mor→ f₀ (proj b)) w3 w4
pairStr/ B@(((Γ , A') , B') , ((_ , _) , _)) a@(dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) aₛ a₁ b bₛ b₁ =
  lemmaMor→S' (pairStrS-// B a aₛ a₁ b bₛ b₁) (pairStrₛS-// B a aₛ a₁ b bₛ b₁)
  ∙ ap-irr-pairStr refl
                   (lemmaMor→S a aₛ a₁ refl)
                   (lemmaMor→S b bₛ b₁ (eq (snd (fst (reflect (! aₛ)))) ∙ ap ftS a₁))

pairStr→S : (B : ObS (suc (suc n))) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) (b : MorS n (suc n)) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ starS a B a₁)
            {w1 : _} {w2 : _} {w3 : _} {w4 : _}
          → Mor→ f₀ (pairStrS B a aₛ a₁ b bₛ b₁) ≡ pairStr sC (Ob→ f₀ B) (Mor→ f₀ a) w1 w2 (Mor→ f₀ b) w3 w4
pairStr→S = //-elimP (λ B → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → pairStr/ B a aₛ a₁ b bₛ b₁)))


pr1Str/ : (B : DCtx (suc (suc n))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B))
          {w1 : _} {w2 : _}
        → Mor→ f₀ (pr1StrS (proj B) (proj u) uₛ u₁) ≡ pr1Str sC (Ob→ f₀ (proj B)) (Mor→ f₀ (proj u)) w1 w2
pr1Str/ B@(((Γ , A') , B') , ((_ , _) , _)) u@(dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) uₛ u₁ =
  lemmaMor→S' (pr1StrS-// B u uₛ u₁) (pr1StrₛS-// B u uₛ u₁)
  ∙ ap-irr-pr1Str refl
                   (lemmaMor→S u uₛ u₁ refl)

pr1Str→S : (B : ObS (suc (suc n))) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B)
           {w1 : _} {w2 : _}
         → Mor→ f₀ (pr1StrS B u uₛ u₁) ≡ pr1Str sC (Ob→ f₀ B) (Mor→ f₀ u) w1 w2
pr1Str→S = //-elimP (λ B → //-elimP (λ u uₛ u₁ → pr1Str/ B u uₛ u₁))


pr2Str/ : (B : DCtx (suc (suc n))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B))
          {w1 : _} {w2 : _}
        → Mor→ f₀ (pr2StrS (proj B) (proj u) uₛ u₁) ≡ pr2Str sC (Ob→ f₀ (proj B)) (Mor→ f₀ (proj u)) w1 w2
pr2Str/ B@(((Γ , A') , B') , ((_ , _) , _)) u@(dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) uₛ u₁ =
  lemmaMor→S' (pr2StrS-// B u uₛ u₁) (pr2StrₛS-// B u uₛ u₁)
  ∙ ap-irr-pr2Str refl
                   (lemmaMor→S u uₛ u₁ refl)

pr2Str→S : (B : ObS (suc (suc n))) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B)
           {w1 : _} {w2 : _}
         → Mor→ f₀ (pr2StrS B u uₛ u₁) ≡ pr2Str sC (Ob→ f₀ B) (Mor→ f₀ u) w1 w2
pr2Str→S = //-elimP (λ B → //-elimP (λ u uₛ u₁ → pr2Str/ B u uₛ u₁))


natStr/ : (i : ℕ) (X : DCtx n)
        → Mor→ f₀ (natStrS i (proj X)) ≡ natStr sC i (Ob→ f₀ (proj X))
natStr/ i X =
  lemmaMor→S' (natStrS-// i X) (natStrₛS-// i X)

natStr→S : (i : ℕ) (X : ObS n)
        → Mor→ f₀ (natStrS i X) ≡ natStr sC i (Ob→ f₀ X)
natStr→S i = //-elimP (λ X → natStr/ i X)


zeroStr/ : (X : DCtx n)
        → Mor→ f₀ (zeroStrS (proj X)) ≡ zeroStr sC (Ob→ f₀ (proj X))
zeroStr/ X =
  lemmaMor→S' (zeroStrS-// X) (zeroStrₛS-// X)

zeroStr→S : (X : ObS n)
        → Mor→ f₀ (zeroStrS X) ≡ zeroStr sC (Ob→ f₀ X)
zeroStr→S = //-elimP (λ X → zeroStr/ X)


sucStr/ : (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (∂₀S (proj u)))
          {w1 : _} {w2 : _}
        → Mor→ f₀ (sucStrS (proj u) uₛ u₁) ≡ sucStr sC (Mor→ f₀ (proj u)) w1 w2
sucStr/ u uₛ u₁ =
  lemmaMor→S' (sucStrS-// u uₛ u₁) (sucStrₛS-// u uₛ u₁)
  ∙ ap-irr2 (sucStr sC) (lemmaMor→S u uₛ u₁ refl)

sucStr→S : (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ NatStrS (∂₀S u))
           {w1 : _} {w2 : _}
         → Mor→ f₀ (sucStrS u uₛ u₁) ≡ sucStr sC (Mor→ f₀ u) w1 w2
sucStr→S = //-elimP (λ u uₛ u₁ → sucStr/ u uₛ u₁)


idStr/ : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a)))
                 (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj a) aₛ a₁)
                 (v : DMor n (suc n)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj a) aₛ a₁)
         {w1 : _} {w2 : _} {w3 : _} {w4 : _} {w5 : _} {w6 : _}
       → Mor→ f₀ (idStrS i (proj a) aₛ a₁ (proj u) uₛ u₁ (proj v) vₛ v₁) ≡ idStr sC i (Mor→ f₀ (proj a)) w1 w2 (Mor→ f₀ (proj u)) w3 w4 (Mor→ f₀ (proj v)) w5 w6
idStr/ i a aₛ a₁ u uₛ u₁ v vₛ v₁ =
  lemmaMor→S' (idStrS-// i a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStrₛS-// i a aₛ a₁ u uₛ u₁ v vₛ v₁)
  ∙ ap-irr-idStr (lemmaMor→S a aₛ a₁ refl)
                 (lemmaMor→S u uₛ u₁ refl)
                 (lemmaMor→S v vₛ v₁ refl)

idStr→S : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a))
                  (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ ElStrS i a aₛ a₁)
                  (v : MorS n (suc n)) (vₛ : is-sectionS v) (v₁ : ∂₁S v ≡ ElStrS i a aₛ a₁)
           {w1 : _} {w2 : _} {w3 : _} {w4 : _} {w5 : _} {w6 : _}
         → Mor→ f₀ (idStrS i a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ idStr sC i (Mor→ f₀ a) w1 w2 (Mor→ f₀ u) w3 w4 (Mor→ f₀ v) w5 w6
idStr→S i = //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → idStr/ i a aₛ a₁ u uₛ u₁ v vₛ v₁)))


reflStr/ : (A : DCtx (suc n)) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ proj A)
           {w1 : _} {w2 : _}
         → Mor→ f₀ (reflStrS (proj A) (proj u) uₛ u₁) ≡ reflStr sC (Ob→ f₀ (proj A)) (Mor→ f₀ (proj u)) w1 w2
reflStr/ A@((_ , _) , (_ , _)) u uₛ u₁ =
  lemmaMor→S' (reflStrS-// A u uₛ u₁) (reflStrₛS-// A u uₛ u₁)
  ∙ ap-irr-reflStr refl
                   (lemmaMor→S u uₛ u₁ refl)

reflStr→S : (A : ObS (suc n)) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ A)
            {w1 : _} {w2 : _}
          → Mor→ f₀ (reflStrS A u uₛ u₁) ≡ reflStr sC (Ob→ f₀ A) (Mor→ f₀ u) w1 w2
reflStr→S = //-elimP (λ A → //-elimP (λ u uₛ u₁ → reflStr/ A u uₛ u₁))


existence : StructuredCCatMor strSynCCat sC
ccat→ existence = f₀

UUStr→ existence i X = UUStr→S i X
ElStr→ existence i v vₛ v₁ = ElStr→S i v vₛ v₁
PiStr→ existence B = PiStr→S B
SigStr→ existence B = SigStr→S B
NatStr→ existence X = NatStr→S X
IdStr→ existence A a aₛ a₁ b bₛ b₁ = IdStr→S A a aₛ a₁ b bₛ b₁

uuStr→ existence i X = uuStr→S i X
piStr→ existence i a aₛ a₁ b bₛ b₁ = piStr→S i a aₛ a₁ b bₛ b₁
lamStr→ existence B u uₛ u₁ = lamStr→S B u uₛ u₁
appStr→ existence B f fₛ f₁ a aₛ a₁ = appStr→S B f fₛ f₁ a aₛ a₁
sigStr→ existence i a aₛ a₁ b bₛ b₁ = sigStr→S i a aₛ a₁ b bₛ b₁
pairStr→ existence B a aₛ a₁ b bₛ b₁ = pairStr→S B a aₛ a₁ b bₛ b₁
pr1Str→ existence B u uₛ u₁ = pr1Str→S B u uₛ u₁
pr2Str→ existence B u uₛ u₁ = pr2Str→S B u uₛ u₁
natStr→ existence i X = natStr→S i X
zeroStr→ existence X = zeroStr→S X
sucStr→ existence u uₛ u₁ = sucStr→S u uₛ u₁
idStr→ existence i a aₛ a₁ u uₛ u₁ v vₛ v₁ = idStr→S i a aₛ a₁ u uₛ u₁ v vₛ v₁
reflStr→ existence A u uₛ u₁ = reflStr→S A u uₛ u₁


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
