{-# OPTIONS --irrelevant-projections --rewriting --allow-unsolved-metas #-}

open import common
open import contextualcat
open import quotients
open import syntx
open import rules

open CCat hiding (Mor)

{- Preliminary definitions -}

DCtx : ℕ → Set
DCtx n = Σ' (Ctx n) (λ Γ → ⊢ Γ)

DMor : ℕ → ℕ → Set
DMor n m = Σ (DCtx n ×R DCtx m) (λ {((Γ , _) , (Δ , _)) → Σ' (Mor n m) (λ δ → (Γ ⊢ δ ∷> Δ))})

pair-DMor : (δ : DMor n m) {u : TmExpr n} {A : TyExpr m} (dA : Derivable (fst' (snd (fst δ)) ⊢ A)) .(du : Derivable (fst' (fst (fst δ)) ⊢ u :> A [ fst' (snd δ) ]Ty)) → DMor n (suc m)
pair-DMor (((Γ , dΓ), (Δ , dΔ)), (δ , dδ)) {u = u} {A = A} dA du = ((Γ , dΓ) , ((Δ , A) , (dΔ , dA))) , ((δ , u) , (dδ , du))

ObEquiv : (n : ℕ) → EquivRel (DCtx n)
EquivRel._≃_ (ObEquiv n) (Γ , _) (Γ' , _) = ⊢ Γ == Γ'
EquivRel.ref (ObEquiv n) (Γ , dΓ) = CtxRefl dΓ
EquivRel.sym (ObEquiv n) p = CtxSymm p
EquivRel.tra (ObEquiv n) p q = CtxTran p q

MorEquiv : (n m : ℕ) → EquivRel (DMor n m)
EquivRel._≃_ (MorEquiv n m) (((Γ , _), (Δ , _)), (δ , _)) (((Γ' , _), (Δ' , _)), (δ' , _)) = ((⊢ Γ == Γ') × (⊢ Δ == Δ')) × (Γ ⊢ δ == δ' ∷> Δ)
EquivRel.ref (MorEquiv n m) (((_ , dΓ), (_ , dΔ)) , (_ , dδ)) = (CtxRefl dΓ , CtxRefl dΔ) , (MorRefl dδ)
EquivRel.sym (MorEquiv n m) {a = a} ((Γ= , Δ=) , δ=) = (CtxSymm Γ= , CtxSymm Δ=) , ConvMorEq (MorSymm (snd' (snd (fst a))) δ=) Γ= Δ=
EquivRel.tra (MorEquiv n m) {a = a} ((Γ= , Δ=) , δ=) ((Γ'= , Δ'=) , δ'=) = ((CtxTran Γ= Γ'=) , (CtxTran Δ= Δ'=)) , (MorTran (snd' (snd (fst a))) δ= (ConvMorEq δ'= (CtxSymm Γ=) (CtxSymm Δ=)))

ObS : ℕ → Set
ObS n = DCtx n // ObEquiv n

MorS : ℕ → ℕ → Set
MorS n m = DMor n m // MorEquiv n m

∂₀S : {n m : ℕ} → MorS n m → ObS n
∂₀S = //-rec (ObS _) (λ {((Γ , _), _) → proj Γ}) (λ _ _ r → eq (fst (fst r)))

∂₁S : {n m : ℕ} → MorS n m → ObS m
∂₁S = //-rec (ObS _) (λ {((_ , Δ), _) → proj Δ}) (λ _ _ r → eq (snd (fst r)))

idS-u : (n : ℕ) → DCtx n → DMor n n
idS-u n (Γ , dΓ) = (((Γ , dΓ) , (Γ , dΓ)) , (idMor n , idMorDerivable dΓ))

idS : (n : ℕ) → ObS n → MorS n n
idS n = //-rec (MorS _ _) (λ Γ → proj (idS-u n Γ)) (λ {(Γ , dΓ) (Γ' , dΓ') r → eq ((r , r) , MorRefl (idMorDerivable dΓ))})

id₀S : (n : ℕ) (X : ObS n) → ∂₀S (idS n X) ≡ X
id₀S n = //-elimId _ _ (λ Γ → refl)

id₁S : (n : ℕ) (X : ObS n) → ∂₁S (idS n X) ≡ X
id₁S n = //-elimId _ _ (λ Γ → refl)

compS-// : (g : DMor m k) (f : DMor n m) .(_ : ∂₁S (proj f) ≡ ∂₀S (proj g)) → MorS n k
compS-// ((Δd@(Δ , dΔ) , Θd) , (θ , dθ)) ((Γd@(Γ , dΓ) , Δd'@(Δ' , dΔ')) , (δ , dδ)) p = proj ((Γd , Θd) , (θ [ δ ]Mor , (SubstMor dθ (ConvMor dδ (CtxRefl dΓ) (reflect p)))))

postulate
  #TODO# : {A : Set} → A

compS : (g : MorS m k) (f : MorS n m) .(_ : ∂₁S f ≡ ∂₀S g) → MorS n k
compS = //-elimPiCstIdCst compS-// #TODO#

comp₀S-// : (g : DMor m k) (f : DMor n m) .(p : ∂₁S (proj f) ≡ ∂₀S (proj g)) → ∂₀S (compS (proj g) (proj f) p) ≡ ∂₀S (proj f)
comp₀S-// g f p = refl

comp₀S : (g : MorS m k) (f : MorS n m) .(p : ∂₁S f ≡ ∂₀S g) → ∂₀S (compS g f p) ≡ ∂₀S f
comp₀S = //-elimPiCstIdId comp₀S-//

comp₁S-// : (g : DMor m k) (f : DMor n m) .(p : ∂₁S (proj f) ≡ ∂₀S (proj g)) → ∂₁S (compS (proj g) (proj f) p) ≡ ∂₁S (proj g)
comp₁S-// g f p = refl

comp₁S : (g : MorS m k) (f : MorS n m) .(p : ∂₁S f ≡ ∂₀S g) → ∂₁S (compS g f p) ≡ ∂₁S g
comp₁S = //-elimPiCstIdId comp₁S-//

dft : DCtx (suc n) → DCtx n
dft ((Γ , A), (dΓ , dA)) = (Γ , dΓ)

ftS-// : (n : ℕ) → DCtx (suc n) → ObS n
ftS-// n Γ = proj (dft Γ)

ftS : {n : ℕ} → ObS (suc n) → ObS n
ftS {n = n} = //-rec (ObS n) (ftS-// n) (λ {((Γ , _) , (_ , _)) ((Γ' , _) , (_ , _)) r → eq (fst r)})

ppS-// : (X : DCtx (suc n)) → MorS (suc n) n
ppS-// {n = n} Γd@((Γ , A), (dΓ , dA)) = proj ((Γd , (Γ , dΓ)) , (weakenMor (idMor n) , WeakMor (idMorDerivable dΓ)))

ppS-eq : (X X' : DCtx (suc n)) (_ : EquivRel._≃_ (ObEquiv (suc n)) X X') → ppS-// X ≡ ppS-// X'
ppS-eq ((Γ , A), (dΓ , dA)) ((Γ' , A'), (dΓ' , dA')) (dΓ= , dA=) = eq (((dΓ= , dA=) , dΓ=) , (MorRefl (WeakMor (idMorDerivable dΓ))))

ppS : (X : ObS (suc n)) → MorS (suc n) n
ppS {n = n} = //-rec _ ppS-// ppS-eq

pp₀S : (X : ObS (suc n)) → ∂₀S (ppS X) ≡ X
pp₀S X = //-elimId (λ X → ∂₀S (ppS X)) (λ X → X) (λ {((Γ , A), (dΓ , dA)) → refl}) X

pp₁S : (X : ObS (suc n)) → ∂₁S (ppS X) ≡ ftS X
pp₁S X = //-elimId (λ X → ∂₁S (ppS X)) (λ X → ftS X) (λ {((Γ , A), (dΓ , dA)) → refl}) X

ptS : ObS 0
ptS = proj (◇ , tt)

ptmorS : (X : ObS n) → MorS n 0
ptmorS = //-rec _ (λ Γ → proj ((Γ , (◇ , tt)) , (◇ , tt))) (λ a b r → eq ((r , tt) , tt))

.ptmor-uniqueS-// : (X : DCtx n) (f : DMor n 0) (p : ∂₀S (proj f) ≡ proj X) (q : ∂₁S (proj f) ≡ ptS) → proj f ≡ ptmorS (proj X)
ptmor-uniqueS-// X ((Γ , (◇ , tt)), (◇ , tt)) p q = eq ((reflect p , tt) , tt)

.ptmor-uniqueS : (X : ObS n) (f : MorS n 0) (p : ∂₀S f ≡ X) (q : ∂₁S f ≡ ptS) → f ≡ ptmorS X
ptmor-uniqueS = //-elimPiCstIdIdId ptmor-uniqueS-//

.id-rightS-// : (f : DMor n m) → compS (idS m (∂₁S (proj f))) (proj f) (! (id₀S m (∂₁S (proj f)))) ≡ (proj f)
id-rightS-// {m = m} (((Γ , dΓ), (Δ , dΔ)), (δ , dδ)) = apP-irr (λ x z → proj (((Γ , dΓ), (Δ , dΔ)) , (x , z))) (toS (idMor[]Mor δ))

.id-rightS : (f : MorS n m) → compS (idS m (∂₁S f)) f (! (id₀S m (∂₁S f))) ≡ f
id-rightS = //-elimId _ _ id-rightS-//

.id-leftS-// : (f : DMor n m) → compS (proj f) (idS n (∂₀S (proj f))) (id₁S n (∂₀S (proj f))) ≡ (proj f)
id-leftS-// {n = n} (((Γ , dΓ), (Δ , dΔ)), (δ , dδ)) = apP-irr (λ x z → proj (((Γ , dΓ), (Δ , dΔ)) , (x , z))) (toS ([idMor]Mor δ))

.id-leftS : (f : MorS n m) → compS f (idS n (∂₀S f)) (id₁S n (∂₀S f)) ≡ f
id-leftS = //-elimId _ _ id-leftS-//

.assocS-// : (h : DMor k l) (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj g) ≡ ∂₀S (proj h)) → compS (compS (proj h) (proj g) q) (proj f) (p ∙ ! (comp₀S (proj h) (proj g) q)) ≡ compS (proj h) (compS (proj g) (proj f) p) (comp₁S (proj g) (proj f) p ∙ q)
assocS-// (((Θ' , dΘ'), (Φ , dΦ)), (φ , dφ)) (((Δ' , dΔ'), (Θ , dΘ)), (θ , dθ)) (((Γ , dΓ), (Δ , dΔ)), (δ , dδ)) p q =
  apP-irr (λ x z → proj (((Γ , dΓ), (Φ , dΦ)) , (x , z)))
         (toS ([]Mor-assoc δ θ φ))

.assocS : (h : MorS k l) (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) (q : ∂₁S g ≡ ∂₀S h) → compS (compS h g q) f (p ∙ ! (comp₀S h g q)) ≡ compS h (compS g f p) (comp₁S g f p ∙ q)
assocS = //-elimPiCstCstIdIdId assocS-//

starS-//-u : (f : DMor m n) (X : DCtx (suc n)) .(_ : ∂₁S (proj f) ≡ ftS (proj X)) → DCtx (suc m)
starS-//-u (((Γ , dΓ), (Δ' , dΔ')) , (δ , dδ)) ((Δ , B) , (dΔ , dB)) p = ((Γ , B [ δ ]Ty) , (dΓ , (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)))))

starS-// : (f : DMor m n) (X : DCtx (suc n)) .(_ : ∂₁S (proj f) ≡ ftS (proj X)) → ObS (suc m)
starS-// f x p = proj (starS-//-u f x p)

starS : (f : MorS m n) (X : ObS (suc n)) .(_ : ∂₁S f ≡ ftS X) → ObS (suc m)
starS = //-elimPiCstIdCst starS-// #TODO#

qqS-// : (f : DMor m n) (X : DCtx (suc n)) .(_ : ∂₁S (proj f) ≡ ftS (proj X)) → MorS (suc m) (suc n)
qqS-// f@(((Γ , dΓ), (Δ' , dΔ')) , (δ , dδ)) X@((Δ , A) , (dΔ , dA)) p = proj ((starS-//-u f X p , X) , ((weakenMor δ , var last) , ((WeakMor (ConvMor dδ (CtxRefl dΓ) (reflect p))) , aux)))  where
  .aux : Derivable ((Γ , (A [ δ ]Ty)) ⊢ var last :> (A [ weakenMor δ ]Ty))
  aux = congTm (weaken[]Ty A δ last) (VarRule last (WeakTy (SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflect p)))))

qqS : (f : MorS m n) (X : ObS (suc n)) .(_ : ∂₁S f ≡ ftS X) → MorS (suc m) (suc n)
qqS = //-elimPiCstIdCst qqS-// #TODO#

qq₀S-// : (f : DMor m n) (X : DCtx (suc n)) .(p : ∂₁S (proj f) ≡ ftS (proj X)) → ∂₀S (qqS (proj f) (proj X) p) ≡ starS (proj f) (proj X) p
qq₀S-// f X@((Δ , A) , (dΔ , dA)) p = refl

qq₀S : (f : MorS m n) (X : ObS (suc n)) .(p : ∂₁S f ≡ ftS X) → ∂₀S (qqS f X p) ≡ starS f X p
qq₀S = //-elimPiCstIdId qq₀S-//

qq₁S-// : (f : DMor m n) (X : DCtx (suc n)) .(p : ∂₁S (proj f) ≡ ftS (proj X)) → ∂₁S (qqS (proj f) (proj X) p) ≡ proj X
qq₁S-// f X@((Δ , A) , (dΔ , dA)) p = refl

qq₁S : (f : MorS m n) (X : ObS (suc n)) .(p : ∂₁S f ≡ ftS X) → ∂₁S (qqS f X p) ≡ X
qq₁S = //-elimPiCstIdId qq₁S-//

ssS-//-u : (f : DMor m (suc n)) → DMor m (suc m)
ssS-//-u {m = m} f@(((Γ , dΓ), ((Δ , B), (dΔ , dB))), ((δ , u), (dδ , du))) = pair-DMor (idS-u m (Γ , dΓ)) (SubstTy dB dδ) (congTm (!R ([idMor]Ty _)) du)

ssS-// : (f : DMor m (suc n)) → MorS m (suc m)
ssS-// f = proj (ssS-//-u f)

ssS-eq : (f f' : DMor m (suc n)) (_ : EquivRel._≃_ (MorEquiv m (suc n)) f f') → ssS-// f ≡ ssS-// f'
ssS-eq {m = m} f@(((Γ , dΓ), ((Δ , B), (dΔ , dB))), ((δ , u), (dδ , du))) f'@(((Γ' , dΓ'), ((Δ' , B'), (dΔ' , dB'))), ((δ' , u'), (dδ' , du'))) p@((dΓ= , (dΔ= , dB=)) , (dδ= , du=))
  = eq {a = ssS-//-u f} {b = ssS-//-u f'} ((dΓ= , (dΓ= , (SubstTySubstEq dB= dδ=))) , (MorRefl (idMorDerivable dΓ) , congTmEq (!R ([idMor]Ty _)) du=))

ssS : (f : MorS m (suc n)) → MorS m (suc m)
ssS {n = n} = //-rec _ ssS-// ssS-eq

ss₀S : (f : MorS m (suc n)) → ∂₀S (ssS f) ≡ ∂₀S f
ss₀S = //-elimId _ _ (λ {(((Γ , dΓ), ((Δ , B), (dΔ , dB))), ((δ , u), (dδ , du))) → refl})

.ss₁S-// : (f : DMor m (suc n)) → ∂₁S (ssS (proj f)) ≡ starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S _))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S _)) ∙ pp₁S (∂₁S (proj f)))
ss₁S-// (((Γ , dΓ), ((Δ , B), (dΔ , dB))), ((δ , u), (dδ , du))) = apP-irr (λ x z → proj (x , z)) (ap (λ γ → (Γ , B [ γ ]Ty)) (! (toS (weakenidMor[]Mor δ u))))

.ss₁S : (f : MorS m (suc n)) → ∂₁S (ssS f) ≡ starS (compS (ppS (∂₁S f)) f (! (pp₀S _))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S _)) ∙ pp₁S (∂₁S f))
ss₁S = //-elimId _ _ ss₁S-//

ft-starS-// : (f : DMor m n) (X : DCtx (suc n)) .(p : ∂₁S (proj f) ≡ ftS (proj X)) → ftS (starS (proj f) (proj X) p) ≡ ∂₀S (proj f)
ft-starS-// (((Γ , dΓ), (Δ' , dΔ')), (δ , dδ)) ((Δ , B), (dΔ , dB)) p = refl

ft-starS : (f : MorS m n) (X : ObS (suc n)) .(p : ∂₁S f ≡ ftS X) → ftS (starS f X p) ≡ ∂₀S f
ft-starS = //-elimPiCstIdId ft-starS-//

pp-qqS-// : (f : DMor m n) (X : DCtx (suc n)) .(p : ∂₁S (proj f) ≡ ftS (proj X)) → compS (ppS (proj X)) (qqS (proj f) (proj X) p) (qq₁S (proj f) (proj X) p ∙ ! (pp₀S (proj X))) ≡ compS (proj f) (ppS (starS (proj f) (proj X) p)) (pp₁S (starS (proj f) (proj X) p) ∙ ft-starS (proj f) (proj X) p)
pp-qqS-// (((Γ , dΓ), (Δ' , dΔ')), (δ , dδ)) ((Δ , B), (dΔ , dB)) p = {!ap (λ z → proj (_ , z)) ? !}

pp-qqS : (f : MorS m n) (X : ObS (suc n)) .(p : ∂₁S f ≡ ftS X) → compS (ppS X) (qqS f X p) (qq₁S f X p ∙ ! (pp₀S X)) ≡ compS f (ppS (starS f X p)) (pp₁S (starS f X p) ∙ ft-starS f X p)
pp-qqS = //-elimPiCstIdId pp-qqS-//

.star-idS : {n : ℕ} (X : ObS (suc n)) → starS (idS n (ftS X)) X (id₁S n (ftS X)) ≡ X
star-idS = //-elimId _ _ (λ {((Γ , A), (dΓ , dA)) → apP-irr (λ x z → proj ((Γ , x) , z)) (toS ([idMor]Ty A))})

.qq-idS : (X : ObS (suc n)) → qqS (idS n (ftS X)) X (id₁S n (ftS X)) ≡ idS (suc n) X
qq-idS {n = n} = //-elimId _ _ (λ {((Γ , A), (dΓ , dA)) → apP-irr2 (λ x z t → (proj ((((Γ , x) , (dΓ , z)), ((Γ , A), (dΓ , dA))), ((weakenMor' last (idMor n) , var last) , t)))) (toS ([idMor]Ty A)) {b = SubstTy dA (idMorDerivable dΓ)} {b' = dA} {c = (WeakMor (idMorDerivable dΓ)) , (congTm (weaken[]Ty A (idMor n) last) (VarRule last (WeakTy (SubstTy dA (idMorDerivable dΓ)))))} {c' = (WeakMor (idMorDerivable dΓ)) , (congTm (apR weakenTy (!R ([idMor]Ty A)) ∙R weaken[]Ty A (idMor n) last) (VarRule last (WeakTy dA)))}})

.star-compS-// : (g : DMor m k) (f : DMor n m) (X : DCtx (suc k)) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj g) ≡ ftS (proj X)) → starS (compS (proj g) (proj f) p) (proj X) (comp₁S (proj g) (proj f) p ∙ q) ≡ starS (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q))
star-compS-// ((Δd@(Δ , dΔ) , Θd) , (θ , dθ)) ((Γd@(Γ , dΓ) , Δd'@(Δ' , dΔ')) , (δ , dδ)) ((Γ' , A), (dΓ' , dA)) p q =
  apP-irr (λ x z → proj ((Γ , x), z)) (! (toS ([]Ty-assoc δ θ A)))

.star-compS : (g : MorS m k) (f : MorS n m) (X : ObS (suc k)) (p : ∂₁S f ≡ ∂₀S g) (q : ∂₁S g ≡ ftS X) → starS (compS g f p) X (comp₁S g f p ∙ q) ≡ starS f (starS g X q) (p ∙ ! (ft-starS g X q))
star-compS = //-elimPiCstCstIdIdId star-compS-//

ss-ppS-// : {m n : ℕ} (f : DMor m (suc n)) → compS (ppS (starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f))))) (ssS (proj f)) (ss₁S (proj f) ∙ ! (pp₀S (starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))))) ≡ idS m (∂₀S (proj f))
ss-ppS-// (((Γ , dΓ), ((Δ , B), (dΔ , dB))), ((δ , u), (dδ , du))) = {!!}

ss-ppS : {m n : ℕ} (f : MorS m (suc n)) → compS (ppS (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f)))) (ssS f) (ss₁S f ∙ ! (pp₀S (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))))) ≡ idS m (∂₀S f)
ss-ppS {m} {n} = //-elimId (λ f → compS (ppS (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f)))) (ssS f) (ss₁S f ∙ ! (pp₀S (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f)))))) (λ f → idS m (∂₀S f)) (ss-ppS-// {m} {n})

ss-qqS-// : {m n : ℕ} (f : DMor m (suc n)) → (proj f) ≡ compS (qqS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))) (ssS (proj f)) (ss₁S (proj f) ∙ ! (qq₀S (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))))
ss-qqS-// (((Γ , dΓ), ((Δ , B), (dΔ , dB))), ((δ , u), (dδ , du))) = {!!}

ss-qqS : {m n : ℕ} (f : MorS m (suc n)) → f ≡ compS (qqS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))) (ssS f) (ss₁S f ∙ ! (qq₀S (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))))
ss-qqS = //-elimId (λ f → f) (λ f → compS (qqS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))) (ssS f) (ss₁S f ∙ ! (qq₀S (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))))) ss-qqS-//

ss-compS-// : {m n k : ℕ} (U : DCtx (suc k)) (g : DMor n k) (f : DMor m (suc n)) (g₁ : ∂₁S (proj g) ≡ ftS (proj U)) (f₁ : ∂₁S (proj f) ≡ starS (proj g) (proj U) g₁) {-g₀ : ∂₀ g ≡ ft (∂₁ f)-} → ssS (proj f) ≡ ssS (compS (qqS (proj g) (proj U) g₁) (proj f) (! (qq₀S (proj g) (proj U) g₁ ∙ ! f₁)))
ss-compS-// U@((Θ' , C), (dΘ' , dC)) g@(((Δ' , dΔ'), (Θ , dΘ)), (θ , dθ)) f@(((Γ , dΓ), ((Δ , B), (dΔ , dB))), ((δ , u), (dδ , du))) g₁ f₁ = {!!}

.ss-compS : {m n k : ℕ} (U : ObS (suc k)) (g : MorS n k) (f : MorS m (suc n)) (g₁ : ∂₁S g ≡ ftS U) (f₁ : ∂₁S f ≡ starS g U g₁) {-g₀ : ∂₀ g ≡ ft (∂₁ f)-} → ssS f ≡ ssS (compS (qqS g U g₁) f (! (qq₀S g U g₁ ∙ ! f₁)))
ss-compS = //-elimPiCstCstIdIdId ss-compS-//

{- The syntactic model itself -}

synCCat : CCat
Ob synCCat = ObS
CCat.Mor synCCat = MorS
∂₀ synCCat = ∂₀S
∂₁ synCCat = ∂₁S
id synCCat = idS _
id₀ synCCat {n = n} {X = X} = id₀S n X
id₁ synCCat {n = n} {X = X} = id₁S n X
comp synCCat = compS
comp₀ synCCat {g = g} {f = f} {p = p} = comp₀S g f p
comp₁ synCCat {g = g} {f = f} {p = p} = comp₁S g f p
ft synCCat = ftS
pp synCCat = ppS
pp₀ synCCat {X = X} = pp₀S X
pp₁ synCCat {X = X} = pp₁S X
star synCCat = starS
qq synCCat = qqS
qq₀ synCCat {f = f} {X = X} {p = p} = qq₀S f X p
qq₁ synCCat {f = f} {X = X} {p = p} = qq₁S f X p
ss synCCat = ssS
ss₀ synCCat {f = f} = ss₀S f
ss₁ synCCat {f = f} = ss₁S f
pt synCCat = ptS
pt-unique synCCat = //-elimId (λ z → z) (λ _ → proj (◇ , tt)) (λ {(◇ , tt) → eq tt})
ptmor synCCat = ptmorS
ptmor₀ synCCat {X = X} = //-elimId (λ X → ∂₀S (ptmorS X)) (λ X → X) (λ Γ → refl) X
ptmor₁ synCCat {X = X} = //-elimId (λ X → ∂₁S (ptmorS X)) (λ X → proj (◇ , tt)) (λ Γ → refl) X
ptmor-unique synCCat = ptmor-uniqueS
id-right synCCat {f = f} = id-rightS f
id-left synCCat {f = f} = id-leftS f
assoc synCCat {h = h} {g = g} {f = f} {p = p} {q = q} = assocS h g f p q
ft-star synCCat {f = f} {X = X} {p = p} = ft-starS f X p
pp-qq synCCat {f = f} {X = X} {p = p} = pp-qqS f X p
star-id synCCat {X = X} = star-idS X
qq-id synCCat {X = X} = qq-idS X
star-comp synCCat {g = g} {f = f} {p = p} {X = X} q = star-compS g f X p q
ss-pp synCCat {f = f} = ss-ppS f
ss-qq synCCat {f = f} = ss-qqS f
ss-comp synCCat {U = U} {g = g} {g₁ = g₁} {f = f} {f₁ = f₁} = ss-compS U g f g₁ f₁
