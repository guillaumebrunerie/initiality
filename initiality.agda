{-# OPTIONS --rewriting --prop --without-K #-}

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
open CCatMor
open partialinterpretation sC
module S = partialinterpretation strSynCCat
open totality sC


private
  C = ccat sC

open CCat (ccat sC)

ap-irr-appStr : {B B' : Ob (suc (suc n))} (B= : B ≡ B') {f f' : Mor n (suc n)} {fs : is-section f} {f₁ : ∂₁ f ≡ PiStr sC B} {fs' : is-section f'} {f₁' : ∂₁ f' ≡ PiStr sC B'} (f= : f ≡ f') {a a' : Mor n (suc n)} {as : is-section a} {a₁ : ∂₁ a ≡ ft B} {as' : is-section a'} {a₁' : ∂₁ a' ≡ ft B'} (a= : a ≡ a') → appStr sC B f fs f₁ a as a₁ ≡ appStr sC B' f' fs' f₁' a' as' a₁'
ap-irr-appStr refl refl refl = refl

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

id/ : (X : DCtx n) → Mor→S (idS n (proj X)) ≡ id (Ob→S (proj X))
id/ (Γ , dΓ) = ⟦idMor⟧= refl

id→S : (X : ObS n) → Mor→S (idS n X) ≡ id (Ob→S X)
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
pp/ ((Γ , A) , (dΓ , dA)) = ⟦weaken⟧= (ap ft (! pp₀)) (⟦⟧Ty-ft A) (idMor _) (⟦idMor⟧ᵈ (! (ap ft pp₀ ∙ ⟦⟧Ty-ft A))) ∙ ap2-irr comp refl (ap2-irr qq (⟦idMor⟧= (! (⟦⟧Ty-ft A) ∙ ap ft (! pp₀))) (! pp₀) ∙ qq-id) ∙ id-left

pp→S : (X : ObS (suc n)) → Mor→S (ppS X) ≡ pp (Ob→S X)
pp→S = //-elimP pp/

star/ : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → Ob→S (starS (proj f) (proj X) p) ≡ star (Mor→S (proj f)) (Ob→S (proj X)) (! (∂₁→S (proj f)) ∙ ap Ob→S p ∙ ft→S (proj X))
star/ (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) ((Δ' , A) , (dΔ' , dA')) p =
  let dA = ConvTy dA' (reflect (! p)) in
  ⟦tsubst⟧Ty= A (⟦⟧Tyᵈ respects⟦⟧Ctx dA) δ (⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ) ∙ ap2-irr star refl (ap-irr (λ x z → ⟦ A ⟧Ty x $ z) (⟦⟧CtxEq (reflect p)))

star→S : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → Ob→S (starS f X p) ≡ star (Mor→S f) (Ob→S X) (! (∂₁→S f) ∙ ap Ob→S p ∙ ft→S X)
star→S = //-elimP (λ f → //-elimP (star/ f))

qq/ : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → Mor→S (qqS (proj f) (proj X) p) ≡ qq (Mor→S (proj f)) (Ob→S (proj X)) (! (∂₁→S (proj f)) ∙ ap Ob→S p ∙ ft→S (proj X))
qq/ (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) ((Δ' , A) , (dΔ' , dA')) p =
  let dA = ConvTy dA' (reflect (! p)) in
  ⟦weaken+⟧= (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A ∙ ⟦⟧CtxEq (reflect (! p))) δ (⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδ)

qq→S : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → Mor→S (qqS f X p) ≡ qq (Mor→S f) (Ob→S X) (! (∂₁→S f) ∙ ap Ob→S p ∙ ft→S X)
qq→S = //-elimP (λ f → //-elimP (qq/ f))

ss/ : (f : DMor m (suc n)) → Mor→S (ssS (proj f)) ≡ ss (Mor→S (proj f))
ss/ (dmor (Γ , dΓ) ((Δ , A) , (dΔ , dA)) (δ , u) (dδ , du)) = ap2-irr comp (ap2-irr qq (⟦idMor⟧= (⟦⟧Ty-ft (A [ δ ]Ty)) ∙ ap id (! (⟦⟧Ty-ft (A [ δ ]Ty)))) refl ∙ qq-id ∙ ap id (! (⟦⟧Tm₁ respects⟦⟧Ctx u du))) refl ∙ id-right ∙ ! (ss-of-section _ (⟦⟧Tmₛ u)) ∙ ss-comp {f₁ = ⟦⟧Tm₁ respects⟦⟧Ctx u du ∙ ⟦tsubst⟧Ty= A (⟦⟧Tyᵈ aux dA) δ (⟦⟧Morᵈ respects⟦⟧Ctx aux dδ) ∙ ap2-irr star refl (ap-irr (λ x z → ⟦ A ⟧Ty x $ z) (⟦⟧Ty-ft A))}  where

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

open StructuredCCatMor

get-term : DMor n (suc n) → TmExpr n
get-term (dmor _ _ (_ , u) _) = u

lemmaMor→S : (u : DMor n (suc n)) (uₛ : CCat.is-section synCCat (proj u)) (Γ : Ctx n) (dΓ : ⊢ Γ) (A : TyExpr n) (dA : Derivable (Γ ⊢ A)) (u₁ : ∂₁S (proj u) ≡ proj ((Γ , A) , (dΓ , dA))) {w : _} → Mor→S (proj u) ≡ ⟦ get-term u ⟧Tm (Ob/ (Γ , dΓ)) $ w
lemmaMor→S uu@(dmor (Γu , dΓu) ((Γu' , Au) , (dΓu' , dAu)) (δu , u) (dδu , du~)) uₛ Γ dΓ A dA u₁ =
  let (dΓu= , _ , _ , duTy= , _) = reflect u₁

      u₀ : ∂₀S (proj uu) ≡ proj (Γ , dΓ)
      u₀ = is-section₀S {u = proj uu} uₛ ∙ ap ftS u₁

      du : Derivable (Γ ⊢ u :> A)
      du = ConvTm2 du~ (reflect u₀) (congTyEq refl ([idMor]Ty A) (SubstTyMorEq2 dΓu dΓu' duTy= (sectionS-eq {dA = dAu} {dδ = dδu} {du = du~} uₛ)))

      δu= : Γu ⊢ δu == idMor _ ∷> Γu'
      δu= = congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor δu) refl (snd (reflect uₛ))

      dΓu=' : ⊢ Γu' == Γu
      dΓu=' = snd (fst (reflect uₛ))
  in
  ap2-irr comp (ap2-irr qq (⟦⟧MorEq {Γ' = Γu} {Δ' = Γu'} respects⟦⟧Ctx δu= ∙ ⟦idMor⟧= (⟦⟧Ty-ft Au ∙ ⟦⟧CtxEq dΓu=') ∙ ap id (! (⟦⟧Tm₁-ft u))) (! (⟦⟧Tm₁ respects⟦⟧Ctx u du~ ∙ ⟦tsubst⟧Ty= Au (⟦⟧Tyᵈ respects⟦⟧Ctx dAu) δu (⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδu) ∙ ap2-irr star (⟦⟧MorEq {Γ' = Γu} {Δ' = Γu'} respects⟦⟧Ctx δu= ∙ ⟦idMor⟧= (⟦⟧CtxEq dΓu=') ∙ ap id (! (⟦⟧Ty-ft Au ∙ ⟦⟧CtxEq dΓu='))) refl ∙ star-id)) ∙ qq-id) refl ∙ id-right ∙ ap-irr (λ x z → ⟦ u ⟧Tm x $ z) (⟦⟧CtxEq (reflect u₀))

PiStr→S : (B : ObS (suc (suc n))) → Ob→ f₀ (PiStr strSynCCat B) ≡ PiStr sC (Ob→ f₀ B)
PiStr→S = //-elimP (λ {(((Γ , A) , B) , ((dΓ , dA) , dB)) → refl})

lamStr/ : (u : DMor (suc n) (suc (suc n))) (us : CCat.is-section synCCat (proj u))
         → Mor→S (lamStrS (proj u) us) ≡ lamStr sC (Mor→S (proj u)) (ap2-irr comp (ap pp (! (∂₁→S (proj u))) ∙ ! (pp→S (∂₁S (proj u)))) refl ∙ ! (comp→S (ppS (∂₁S (proj u))) (proj u) (! (pp₀S (∂₁S (proj u))))) ∙ ap Mor→S us ∙ id→S (∂₀S (proj u)) ∙ ap id (∂₀→S (proj u)))
lamStr/ {n = n} uu@(dmor ((Γ' , A') , (dΓ' , dA')) (((Γ , A) , B) , ((dΓ , dA) , dB)) ((δ , v) , u) ((dδ , dv) , du)) us =
  let u₀ : ∂₀S (proj uu) ≡ proj ((Γ , A) , (dΓ , dA))
      u₀ = is-section₀S {u = proj uu} us

      du' : Derivable ((Γ , A) ⊢ u :> B)
      du' = ConvTm2 du (reflect u₀) (congTyEq refl ([idMor]Ty B) (SubstTyMorEq dB (dδ , dv) (sectionS-eq {dA = dB} {dδ = (dδ , dv)} {du = du} us)))
  in
  ap2-irr comp (ap2-irr qq (⟦idMor⟧= (⟦⟧Ty-ft (pi A B)) ∙ ap id (! (⟦⟧Ty-ft (pi A B)))) refl ∙ qq-id ∙ ap id (! (⟦⟧Tm₁ respects⟦⟧Ctx (lam A B u) {uᵈ = ⟦⟧Tmᵈ respects⟦⟧Ctx (Lam dA dB du')} (Lam dA dB du')))) refl ∙ id-right ∙ ap-irr (lamStr sC) (! (lemmaMor→S uu us (Γ , A) (dΓ , dA) B dB refl))

lamStr→S : (u : MorS (suc n) (suc (suc n))) (us : CCat.is-section synCCat u)
         → Mor→S (lamStrS u us) ≡ lamStr sC (Mor→S u) (ap2-irr comp (ap pp (! (∂₁→S u)) ∙ ! (pp→S (∂₁S u))) refl ∙ ! (comp→S (ppS (∂₁S u)) u (! (pp₀S (∂₁S u)))) ∙ ap Mor→S us ∙ id→S (∂₀S u) ∙ ap id (∂₀→S u))
lamStr→S = //-elimP lamStr/

appStr/ : (B : DCtx (suc (suc n))) (f : DMor n (suc n)) (fs : CCat.is-section synCCat (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor n (suc n)) (as : CCat.is-section synCCat (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) {w1 : _} {w2 : _} {w3 : _} {w4 : _}
         → Mor→S (appStrS (proj B) (proj f) fs f₁ (proj a) as a₁) ≡
           appStr sC (Ob→S (proj B)) (Mor→S (proj f)) w1 w2 (Mor→S (proj a)) w3 w4
appStr/ (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γf' , Af) , (dΓf' , dAf)) (δf , f) (dδf , df~)) fs f₁ aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) as a₁ =
  let a₀ : ∂₀S (proj aa) ≡ proj (Γ , dΓ)
      a₀ = is-section₀S {u = proj aa} as ∙ ap ftS a₁

      (_ , _ , _ , daTy= , _) = reflect a₁

      da[] : Derivable (Γ ⊢ a :> A [ idMor _ ]Ty)
      da[] = ConvTm2 da~ (reflect a₀) (SubstTyMorEq2 dΓa dΓa' daTy= (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} as))

      da : Derivable (Γ ⊢ a :> A)
      da = congTm ([idMor]Ty A) refl da[]

      f₀ : ∂₀S (proj ff) ≡ proj (Γ , dΓ)
      f₀ = is-section₀S {u = proj ff} fs ∙ ap ftS f₁

      (dΓf= , _ , _ , dfTy= , _) = reflect f₁

      df : Derivable (Γ ⊢ f :> pi A B)
      df = ConvTm2 df~ (reflect f₀) (congTyEq refl ([idMor]Ty (pi A B)) (SubstTyMorEq2 dΓf dΓf' dfTy= (sectionS-eq {dA = dAf} {dδ = dδf} {du = df~} fs)))

      δf= : Γf ⊢ δf == idMor _ ∷> Γf'
      δf= = congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor δf) refl (snd (reflect fs))

      dΓf=' : ⊢ Γf' == Γf
      dΓf=' = snd (fst (reflect fs))

      δa= : Γa ⊢ δa == idMor _ ∷> Γa'
      δa= = congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor δa) refl (snd (reflect as))

      dΓa=' : ⊢ Γa' == Γa
      dΓa=' = snd (fst (reflect as))
  in
  ap2-irr comp (ap2-irr qq (⟦idMor⟧= (⟦⟧Ty-ft (B [ idMor _ , a ]Ty)) ∙ ap id (! (⟦⟧Ty-ft (B [ idMor _ , a ]Ty)))) refl ∙ qq-id ∙ ap id (! (appStr₁ sC ∙ ! (⟦subst⟧Ty= (⟦⟧Ty-ft A) B {u = a} (⟦⟧Tyᵈ (respectsCtxExt respects⟦⟧Ctx A) dB) (⟦⟧Tmᵈ respects⟦⟧Ctx da) (⟦⟧Tm₁ respects⟦⟧Ctx a da))))) refl ∙ id-right
  ∙ ap-irr-appStr refl (! (lemmaMor→S ff fs Γ dΓ (pi A B) (Pi dA dB) f₁))
                       (! (lemmaMor→S aa as Γ dΓ A dA a₁))

appStr→S : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fs : CCat.is-section synCCat f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (as : CCat.is-section synCCat a) (a₁ : ∂₁S a ≡ ftS B) {w1 : _} {w2 : _} {w3 : _} {w4 : _}
         → Mor→S (appStrS B f fs f₁ a as a₁) ≡
           appStr sC (Ob→S B) (Mor→S f) w1 w2 (Mor→S a) w3 w4
appStr→S = //-elimP (λ B → //-elimP (λ f fs f₁ → //-elimP (appStr/ B f fs f₁)))

UUStr→S : (X : ObS n) → Ob→S (UUStrS X) ≡ UUStr sC (Ob→S X)
UUStr→S = //-elimP (λ _ → refl)

ap2-irr2 : {A B E : Set} {C D : (a : A) (b : B) → Prop} (f : (a : A) (b : B) (c : C a b) (d : D a b) → E) {a a' : A} (p : a ≡ a') {b b' : B} (q : b ≡ b') {c : C a b} {c' : C a' b'} {d : D a b} {d' : D a' b'} → f a b c d ≡ f a' b' c' d'
ap2-irr2 f refl refl = refl

ElStr/ : (v : DMor n (suc n)) (vs : CCat.is-section synCCat (proj v)) (v₁ : ∂₁S (proj v) ≡ UUStrS (∂₀S (proj v))) {w1 : _} {w2 : _} → Ob→S (ElStrS (proj v) vs v₁) ≡ ElStr sC (Mor→S (proj v)) w1 w2
ElStr/ (dmor (Γv , dΓv) ((Γv' , Av'), (dΓv' , dAv')) (δv , v) (dδv , dv)) vs v₁ =
  let
      δv= : Γv ⊢ δv == idMor _ ∷> Γv'
      δv= = congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor δv) refl (snd (reflect vs))

      dΓv=' : ⊢ Γv' == Γv
      dΓv=' = snd (fst (reflect vs))
  in
  ap-irr2 (ElStr sC) (! (ap2-irr comp (ap2-irr qq (⟦⟧MorEq {Γ' = Γv} {Δ' = Γv'} respects⟦⟧Ctx δv= ∙ ⟦idMor⟧= (⟦⟧Ty-ft Av' ∙ ⟦⟧CtxEq dΓv=') ∙ ap id (! (⟦⟧Tm₁-ft v))) (! (⟦⟧Tm₁ respects⟦⟧Ctx v dv ∙ ⟦tsubst⟧Ty= Av' (⟦⟧Tyᵈ respects⟦⟧Ctx  dAv') δv (⟦⟧Morᵈ respects⟦⟧Ctx respects⟦⟧Ctx dδv) ∙ ap2-irr star (⟦⟧MorEq {Γ' = Γv} {Δ' = Γv'} respects⟦⟧Ctx δv= ∙ ⟦idMor⟧= (⟦⟧CtxEq dΓv=') ∙ ap id (! (⟦⟧Ty-ft Av' ∙ ⟦⟧CtxEq dΓv='))) refl ∙ star-id)) ∙ qq-id) refl ∙ id-right))

ElStr→S : (v : MorS n (suc n)) (vs : CCat.is-section synCCat v) (v₁ : ∂₁S v ≡ UUStrS (∂₀S v)) {w1 : _} {w2 : _} → Ob→S (ElStrS v vs v₁) ≡ ElStr sC (Mor→S v) w1 w2
ElStr→S = //-elimP ElStr/

f-ex : StructuredCCatMor strSynCCat sC
ccat→ f-ex = f₀
PiStr→ f-ex = PiStr→S
lamStr→ f-ex = lamStr→S
appStr→ f-ex B {f} fs f₁ {a} as a₁ = appStr→S B f fs f₁ a as a₁ 
UUStr→ f-ex = UUStr→S
ElStr→ f-ex v vₛ v₁ = ElStr→S v vₛ v₁


{- Uniqueness of the morphism -}

module _ (sf sg : StructuredCCatMor strSynCCat sC) where

  private
    f = ccat→ sf
    g = ccat→ sg

  uniqueness-Ob-// : (Γ : DCtx n) → Ob→ f (proj Γ) ≡ Ob→ g (proj Γ)
  uniqueness-Mor-// : (δ : DMor n m) → Mor→ f (proj δ) ≡ Mor→ g (proj δ)

  uniqueness-Ob-// (◇ , tt) = pt→ f ∙ ! (pt→ g)
  uniqueness-Ob-// ((Γ , pi A B) , (dΓ , Pi dA dB)) = PiStr→ sf (proj (((Γ , A) , B) , ((dΓ , dA) , dB))) ∙ ap (PiStr sC) (uniqueness-Ob-// (((Γ , A) , B) , ((dΓ , dA) , dB))) ∙ ! (PiStr→ sg (proj (((Γ , A) , B) , ((dΓ , dA) , dB))))
  uniqueness-Ob-// ((Γ , uu) , (dΓ , UU)) = UUStr→ sf (proj (Γ , dΓ)) ∙ ap (UUStr sC) (uniqueness-Ob-// (Γ , dΓ)) ∙ ! (UUStr→ sg (proj (Γ , dΓ)))
  uniqueness-Ob-// ((Γ , el v) , (dΓ , El dv)) =
    let thing = eq ((CtxRefl dΓ , CtxRefl dΓ) , MorSymm dΓ dΓ (congMorRefl (! (weakenMorInsert _ _ _ ∙ idMor[]Mor _)) (idMorDerivable dΓ)))
    in ElStr→ sf (proj (dmor (Γ , dΓ) ((Γ , uu) , (dΓ , UU)) (idMor _ , v) (idMorDerivable dΓ , dv))) thing refl
      ∙ ap-irr2 (ElStr sC) (uniqueness-Mor-// _)
      ∙ ! (ElStr→ sg (proj (dmor (Γ , dΓ) ((Γ , uu) , (dΓ , UU)) (idMor _ , v) (idMorDerivable dΓ , dv))) thing refl)

  uniqueness-Mor-// (dmor (Γ , dΓ) (◇ , tt) ◇ tt) = ptmor→ f {X = proj (Γ , dΓ)} ∙ ap ptmor (uniqueness-Ob-// (Γ , dΓ)) ∙ ! (ptmor→ g)
  uniqueness-Mor-// (dmor (Γ , dΓ) ((Δ , C) , (dΔ , dC)) (δ , u) (dδ , du)) = {!du!}
  -- TODO: We need to split (δ , u) into a combination of pp, qq, ss, and do the appropriate thing for each

  uniqueness-Ob : (X : ObS n) → Ob→ f X ≡ Ob→ g X
  uniqueness-Ob = //-elimP uniqueness-Ob-//

  uniqueness-Mor : (X : MorS n m) → Mor→ f X ≡ Mor→ g X
  uniqueness-Mor = //-elimP uniqueness-Mor-//

  uniqueness : sf ≡ sg
  uniqueness = structuredCCatMorEq uniqueness-Ob uniqueness-Mor
