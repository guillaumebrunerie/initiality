{-# OPTIONS --rewriting --prop --without-K --no-auto-inline #-}

open import common
open import typetheory
open import syntx
open import rules
open import contextualcat
open import quotients
open import termmodel-common

open CCat hiding (Mor) renaming (id to idC)


{- The syntactic contextual category -}

ObS : ℕ → Set
ObS n = DCtx n // ObEquiv

MorS : ℕ → ℕ → Set
MorS n m = DMor n m // MorEquiv

∂₀S : {n m : ℕ} → MorS n m → ObS n
∂₀S = //-rec (λ δ → proj (lhs δ)) (λ r → eq (box (unMor≃-lhs r)))

∂₁S : {n m : ℕ} → MorS n m → ObS m
∂₁S = //-rec (λ δ → proj (rhs δ)) (λ r → eq (box (unMor≃-rhs r)))

idS-u : (n : ℕ) → DCtx n → DMor n n
idS-u n Γ = dmor Γ Γ (idMor n) (idMorDerivable (der Γ))

idS : (n : ℕ) → ObS n → MorS n n
idS n = //-rec (λ Γ → proj (idS-u n Γ)) (λ {(box r) → eq (box r r (MorRefl (idMorDerivable (CtxEqCtx1 r))))})

id₀S : (n : ℕ) (X : ObS n) → ∂₀S (idS n X) ≡ X
id₀S n = //-elimP (λ Γ → refl)

id₁S : (n : ℕ) (X : ObS n) → ∂₁S (idS n X) ≡ X
id₁S n = //-elimP (λ Γ → refl)

compS-//-u : (g : DMor m k) (f : DMor n m) (_ : ∂₁S (proj f) ≡ ∂₀S (proj g)) → DMor n k
compS-//-u g f p = dmor (lhs f) (rhs g) (mor g [ mor f ]Mor) (# (SubstMor (morDer g) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb p))))

compS-// : (g : DMor m k) (f : DMor n m) (_ : ∂₁S (proj f) ≡ ∂₀S (proj g)) → MorS n k
compS-// g f p = proj (compS-//-u g f p)

compS-eq : (g g' : DMor m k) (r : g ≃ g') (f f' : DMor n m) (r' : f ≃ f') (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj f') ≡ ∂₀S (proj g')) → compS-// g f p ≡ compS-// g' f' q
compS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ') (box dΓ= dΔ= dδ=) (dmor (Γ'' , dΓ'') (Δ'' , dΔ'') δ'' dδ'') (dmor (Γ''' , dΓ''') (Δ''' , dΔ''') δ''' dδ''') (box dΓ''= dΔ''= dδ''=) p q =
  eq (box dΓ''= dΔ= (SubstMorFullEq dΔ'' dΔ (ConvMor dδ' (CtxSymm (CtxTran (reflectOb p) dΓ=)) (CtxSymm dΔ=)) (ConvMorEq dδ= (CtxSymm (CtxTran (reflectOb p) (CtxRefl dΓ))) (CtxRefl dΔ)) dδ'' dδ''=))


compS : (g : MorS m k) (f : MorS n m) (_ : ∂₁S f ≡ ∂₀S g) → MorS n k
compS {m = m} {k = k} {n = n} =
 //-elim-PiS (λ g → //-elim-PiP (λ f p → compS-// g f p)
                        (λ {a} {b} r → compS-eq g g (ref g) a b r))
         (λ {a} {b} r → //-elimP-PiP (λ f → compS-eq a b r f f (ref f)))

comp₀S-// : (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) → ∂₀S (compS (proj g) (proj f) p) ≡ ∂₀S (proj f)
comp₀S-// g f p = refl

comp₀S : (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) → ∂₀S (compS g f p) ≡ ∂₀S f
comp₀S = //-elimP (λ g → //-elimP (comp₀S-// g))

comp₁S-// : (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) → ∂₁S (compS (proj g) (proj f) p) ≡ ∂₁S (proj g)
comp₁S-// g f p = refl

comp₁S : (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) → ∂₁S (compS g f p) ≡ ∂₁S g
comp₁S = //-elimP (λ g → //-elimP (comp₁S-// g))

ftS-// : {n : ℕ} → DCtx (suc n) → DCtx n
ftS-// Γ = (getCtx Γ , getdCtx Γ)

ftS-eq : {Γ Γ' : DCtx (suc n)} → Γ ≃ Γ' → proj {R = ObEquiv} (ftS-// Γ) ≡ proj (ftS-// Γ')
ftS-eq {Γ = (_ , _) , _} {(_ , _) , _} (box r) = eq (box (fst r))

ftS : {n : ℕ} → ObS (suc n) → ObS n
ftS = //-rec (λ X → proj (ftS-// X)) ftS-eq

ppS-// : (X : DCtx (suc n)) → MorS (suc n) n
ppS-// Γ = proj (dmor Γ (ftS-// Γ) (weakenMor (idMor _)) (ConvMor (WeakMor (idMorDerivable (getdCtx Γ))) (CtxTy=Ctx' Γ) (CtxRefl (getdCtx Γ)) ))

ppS-eq : {X X' : DCtx (suc n)} (_ : X ≃ X') → ppS-// X ≡ ppS-// X'
ppS-eq {X = (Γ , A), (dΓ , dA)} {(Γ' , A'), (dΓ' , dA')} (box (dΓ= , dA=)) = eq (box (dΓ= , dA=) dΓ= (MorRefl (WeakMor (idMorDerivable dΓ))))

ppS : (X : ObS (suc n)) → MorS (suc n) n
ppS = //-rec ppS-// ppS-eq

pp₀S : (X : ObS (suc n)) → ∂₀S (ppS X) ≡ X
pp₀S = //-elimP (λ {((Γ , A), (dΓ , dA)) → refl})

pp₁S : (X : ObS (suc n)) → ∂₁S (ppS X) ≡ ftS X
pp₁S = //-elimP (λ {((Γ , A), (dΓ , dA)) → refl})

ptS : ObS 0
ptS = proj (◇ , tt)

pt-uniqueS : (X : ObS 0) → X ≡ proj (◇ , tt)
pt-uniqueS = //-elimP (λ {(◇ , tt) → eq (box tt)})

ptmorS : (X : ObS n) → MorS n 0
ptmorS = //-rec (λ Γ → proj (dmor Γ (◇ , tt) ◇ tt)) (λ r → eq (box (unOb≃ r) tt tt))

ptmor₀S : (X : ObS n) → ∂₀S (ptmorS X) ≡ X
ptmor₀S = //-elimP (λ Γ → refl)

ptmor₁S : (X : ObS n) → ∂₁S (ptmorS X) ≡ ptS
ptmor₁S = //-elimP (λ Γ → refl)

ptmor-uniqueS-// : (X : DCtx n) (f : DMor n 0) (p : ∂₀S (proj f) ≡ proj X) (q : ∂₁S (proj f) ≡ ptS) → proj f ≡ ptmorS (proj X)
ptmor-uniqueS-// X (dmor Γ (◇ , tt) ◇ tt) p q = eq (box (reflectOb p) tt tt)

ptmor-uniqueS : (X : ObS n) (f : MorS n 0) (p : ∂₀S f ≡ X) (q : ∂₁S f ≡ ptS) → f ≡ ptmorS X
ptmor-uniqueS = //-elimP (λ X → //-elimP (ptmor-uniqueS-// X))

id-rightS-// : (f : DMor n m) → compS (idS m (∂₁S (proj f))) (proj f) (! (id₀S m (∂₁S (proj f)))) ≡ (proj f)
id-rightS-// {m = m} (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) = DMor= refl refl (idMor[]Mor δ) --ap-irr (λ x z → proj (dmor (Γ , dΓ) (Δ , dΔ) x z)) (idMor[]Mor δ)

id-rightS : (f : MorS n m) → compS (idS m (∂₁S f)) f (! (id₀S m (∂₁S f))) ≡ f
id-rightS = //-elimP id-rightS-//

id-leftS-// : (f : DMor n m) → compS (proj f) (idS n (∂₀S (proj f))) (id₁S n (∂₀S (proj f))) ≡ (proj f)
id-leftS-// {n = n} (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) = DMor= refl refl ([idMor]Mor δ) --ap-irr (λ x z → proj (dmor (Γ , dΓ) (Δ , dΔ) x z)) ([idMor]Mor δ)

id-leftS : (f : MorS n m) → compS f (idS n (∂₀S f)) (id₁S n (∂₀S f)) ≡ f
id-leftS = //-elimP id-leftS-//

assocS-// : (h : DMor k l) (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj g) ≡ ∂₀S (proj h)) → compS (compS (proj h) (proj g) q) (proj f) (p ∙ ! (comp₀S (proj h) (proj g) q)) ≡ compS (proj h) (compS (proj g) (proj f) p) (comp₁S (proj g) (proj f) p ∙ q)
assocS-// (dmor (Θ' , dΘ') (Φ , dΦ) φ dφ) (dmor (Δ' , dΔ') (Θ , dΘ) θ dθ) (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) p q = DMor= refl refl ([]Mor-assoc δ θ φ)
  --ap-irr (λ x z → proj (dmor (Γ , dΓ) (Φ , dΦ) x z)) ([]Mor-assoc δ θ φ)

assocS : (h : MorS k l) (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) (q : ∂₁S g ≡ ∂₀S h) → compS (compS h g q) f (p ∙ ! (comp₀S h g q)) ≡ compS h (compS g f p) (comp₁S g f p ∙ q)
assocS = //-elimP (λ h → //-elimP (λ g → //-elimP (λ f → assocS-// h g f)))

starS-//-u : (f : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj f) ≡ ftS (proj X)) → DCtx (suc m)
starS-//-u f X p = ((ctx (lhs f) , getTy X [ mor f ]Ty) , # (der (lhs f) , (SubstTy (getdTy X) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb p)))))

starS-// : (f : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj f) ≡ ftS (proj X)) → ObS (suc m)
starS-// f x p = proj (starS-//-u f x p)

starS-eq : (f g : DMor m n) (r : f ≃ g) (X Y : DCtx (suc n)) (r' : X ≃ Y) (p : ∂₁S (proj f) ≡ ftS (proj X)) (q : ∂₁S (proj g) ≡ ftS (proj Y)) → starS-// f X p ≡ starS-// g Y q
starS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ)
         (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ')
         (box dΓ= dΔ= dδ=)
         ((Γ'' , A) , (dΓ'' , dA))
         ((Δ'' , B) , (dΔ'' , dB))
         (box (dΓ''= , dA , dB , dA= , dA='))
         p q = eq (box (dΓ= ,, SubstTyFullEq dB (ConvMor dδ (CtxRefl dΓ) (CtxTran dΔ= (reflectOb q)))
                                                (ConvTyEq dA= dΓ''=)
                                                (ConvMorEq dδ= (CtxRefl dΓ) (CtxTran dΔ= (reflectOb q)))))

starS : (f : MorS m n) (X : ObS (suc n)) (_ : ∂₁S f ≡ ftS X) → ObS (suc m)
starS {m = m} {n = n} =
  //-elim-PiS (λ f → //-elim-PiP (starS-// f)
                         (λ r → starS-eq f f (ref f) _ _ r))
          (λ r → //-elimP-PiP (λ X → starS-eq _ _ r X X (ref X)))

qqS-// : (δ : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj δ) ≡ ftS (proj X)) → MorS (suc m) (suc n)
qqS-// f X p = proj (dmor (starS-//-u f X p) X (weakenMor+ (mor f)) (ConvMor
                                                                       (WeakMor+ (getdTy X)
                                                                        (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb p)))
                                                                       (CtxRefl ((der (lhs f)) , SubstTy (getdTy X) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb p)))) (CtxTy=Ctx' X)))

qqS-eq : (f g : DMor m n) (r : f ≃ g) (Γ Δ : DCtx (suc n)) (r' : Γ ≃ Δ) (p : ∂₁S (proj f) ≡ ftS (proj Γ)) (q : ∂₁S (proj g) ≡ ftS (proj Δ)) → qqS-// f Γ p ≡ qqS-// g Δ q
qqS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ') (box dΓ= dΔ= dδ=) ((Γ'' , A) , (dΓ'' , dA)) ((Δ'' , B) , (dΔ'' , dB)) (box (dΓ''= , dA , dB , dA= , dA=')) p q = eq (((box (dΓ= , SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflectOb p)) , SubstTy dB (ConvMor dδ' (CtxRefl dΓ') (reflectOb q)) , SubstTyFullEq dB (ConvMor dδ (CtxRefl dΓ) (CtxTran dΔ= (reflectOb q))) (ConvTyEq dA= dΓ''=) (ConvMorEq dδ= (CtxRefl dΓ) (CtxTran dΔ= (reflectOb q))) , SubstTyFullEq dB (ConvMor dδ dΓ= (CtxTran dΔ= (reflectOb q))) (ConvTyEq dA= dΓ''=) (ConvMorEq dδ= dΓ= (CtxTran dΔ= (reflectOb q)))) (dΓ''= , dA , dB , dA= , dA=') (WeakMorEq (ConvMorEq dδ= (CtxRefl dΓ) (reflectOb p)) , congTmRefl (congTmTy (weaken[]Ty _ _ _) (VarLast (SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflectOb p))))) refl))))



qqS : (f : MorS m n) (X : ObS (suc n)) (_ : ∂₁S f ≡ ftS X) → MorS (suc m) (suc n)
qqS {m = m} {n = n} =
  //-elim-PiS
    (λ f → //-elim-PiP (qqS-// f)
                       (λ r → qqS-eq f f (ref f) _ _ r))
    (λ r → //-elimP-PiP (λ X → qqS-eq _ _ r X X (ref X)))


qq₀S-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → ∂₀S (qqS (proj f) (proj X) p) ≡ starS (proj f) (proj X) p
qq₀S-// f X@((Δ , A) , (dΔ , dA)) p = refl

qq₀S : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → ∂₀S (qqS f X p) ≡ starS f X p
qq₀S = //-elimP (λ f → //-elimP (qq₀S-// f))

qq₁S-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → ∂₁S (qqS (proj f) (proj X) p) ≡ proj X
qq₁S-// f X@((Δ , A) , (dΔ , dA)) p = refl

qq₁S : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → ∂₁S (qqS f X p) ≡ X
qq₁S = //-elimP (λ f → //-elimP (qq₁S-// f))

ssS-//-u : (f : DMor m (suc n)) → DMor m (suc m)
ssS-//-u {m = m} f = dmor (lhs f) ((ctx (lhs f) , getTy (rhs f) [ getMor f ]Ty) , # (der (lhs f) , SubstTy (getdTy (rhs f)) (getdMor f))) (idMor _ , getTm f) (# (idMor+ (der (lhs f)) (getdTm f)))

ssS-// : (f : DMor m (suc n)) → MorS m (suc m)
ssS-// f = proj (ssS-//-u f)

ssS-eq : {f f' : DMor m (suc n)} (_ : f ≃ f') → ssS-// f ≡ ssS-// f'
ssS-eq {m = m} {f = f@(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du))} {f'@(dmor (Γ' , dΓ') ((Δ' , B'), (dΔ' , dB')) (δ' , u') (dδ' , du'))} p@(box dΓ= (dΔ= , dB , dB' , dB= , dB=') (dδ= , du=))
  = eq {a = ssS-//-u f} {b = ssS-//-u f'} (box dΓ= (dΓ= ,, SubstTyMorEq2 dΓ dΔ dB= dδ=) (idMor+= dΓ du=))

ssS : (f : MorS m (suc n)) → MorS m (suc m)
ssS {n = n} = //-rec ssS-// ssS-eq

ss₀S : (f : MorS m (suc n)) → ∂₀S (ssS f) ≡ ∂₀S f
ss₀S = //-elimP (λ {(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) → refl})

ss₁S-// : (f : DMor m (suc n)) → ∂₁S (ssS (proj f)) ≡ starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S _))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S _)) ∙ pp₁S (∂₁S (proj f)))
ss₁S-// (dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = DCtx= (ap (_,_ Γ) (ap (_[_]Ty B) (! (weakenMorInsert (idMor _) δ u ∙ idMor[]Mor δ)))) --ap-irr (λ x z → proj ((Γ , B [ x ]Ty) , z)) (! (weakenMorInsert (idMor _) δ u ∙ idMor[]Mor δ)) 

ss₁S : (f : MorS m (suc n)) → ∂₁S (ssS f) ≡ starS (compS (ppS (∂₁S f)) f (! (pp₀S _))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S _)) ∙ pp₁S (∂₁S f))
ss₁S = //-elimP ss₁S-//
 
ft-starS-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → ftS (starS (proj f) (proj X) p) ≡ ∂₀S (proj f)
ft-starS-// (dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) ((Δ , B), (dΔ , dB)) p = refl 

ft-starS : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → ftS (starS f X p) ≡ ∂₀S f
ft-starS = //-elimP (λ f → //-elimP (ft-starS-// f))

pp-qqS-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → compS (ppS (proj X)) (qqS (proj f) (proj X) p) (qq₁S (proj f) (proj X) p ∙ ! (pp₀S (proj X))) ≡ compS (proj f) (ppS (starS (proj f) (proj X) p)) (pp₁S (starS (proj f) (proj X) p) ∙ ft-starS (proj f) (proj X) p)
pp-qqS-// (dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) ((Δ , B), (dΔ , dB)) p = eq (box (CtxRefl dΓ , SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflectOb p)) , SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflectOb p)) , TyRefl (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflectOb p))) , TyRefl (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflectOb p)))) (CtxSymm (reflectOb p)) (MorSymm (dΓ , (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflectOb p)))) dΔ (congMorRefl ( ! (weaken[]Mor δ (idMor _) last) ∙ ap weakenMor ([idMor]Mor δ) ∙ ! ([weakenMor]Mor δ (idMor _) ∙ ap weakenMor (idMor[]Mor δ))) (SubstMor (ConvMor dδ (CtxRefl dΓ) (reflectOb p)) (WeakMor (idMorDerivable dΓ))))))

pp-qqS : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → compS (ppS X) (qqS f X p) (qq₁S f X p ∙ ! (pp₀S X)) ≡ compS f (ppS (starS f X p)) (pp₁S (starS f X p) ∙ ft-starS f X p)
pp-qqS = //-elimP (λ f → //-elimP (pp-qqS-// f))

star-idS : {n : ℕ} (X : ObS (suc n)) → starS (idS n (ftS X)) X (id₁S n (ftS X)) ≡ X
star-idS = //-elimP (λ {((Γ , A), (dΓ , dA)) → DCtx= (ap (_,_ Γ) ([idMor]Ty A))}) --ap-irr (λ x z → proj ((Γ , x) , z)) ([idMor]Ty A)

qq-idS : (X : ObS (suc n)) → qqS (idS n (ftS X)) X (id₁S n (ftS X)) ≡ idS (suc n) X
qq-idS {n = n} = //-elimP (λ {((Γ , A), (dΓ , dA)) → DMor= (ap (_,_ Γ) ([idMor]Ty A)) refl refl})

star-compS-// : (g : DMor m k) (f : DMor n m) (X : DCtx (suc k)) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj g) ≡ ftS (proj X)) → starS (compS (proj g) (proj f) p) (proj X) (comp₁S (proj g) (proj f) p ∙ q) ≡ starS (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q))
star-compS-// (dmor Δd@(Δ , dΔ) Θd θ dθ) (dmor Γd@(Γ , dΓ) Δd'@(Δ' , dΔ') δ dδ) ((Γ' , A), (dΓ' , dA)) p q = DCtx= (ap (_,_ Γ) (! ([]Ty-assoc _ _ _))) --ap-irr (λ x z → proj ((Γ , x), z)) (! ([]Ty-assoc δ θ A))

star-compS : (g : MorS m k) (f : MorS n m) (X : ObS (suc k)) (p : ∂₁S f ≡ ∂₀S g) (q : ∂₁S g ≡ ftS X) → starS (compS g f p) X (comp₁S g f p ∙ q) ≡ starS f (starS g X q) (p ∙ ! (ft-starS g X q))
star-compS = //-elimP (λ g → //-elimP (λ f → //-elimP (star-compS-// g f)))


qq-compS-// : (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (X : DCtx (suc k)) (q : ∂₁S (proj g) ≡ ftS (proj X)) → qqS (compS (proj g) (proj f) p) (proj X) (comp₁S (proj g) (proj f) p ∙ q) ≡ compS (qqS (proj g) (proj X) q) (qqS (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q))) (qq₁S (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q)) ∙ ! (qq₀S (proj g) (proj X) q))
qq-compS-// (dmor Δd@(Δ , dΔ) Θd θ dθ) (dmor Γd@(Γ , dΓ) Δd'@(Δ' , dΔ') δ dδ) p ((Γ' , A), (dΓ' , dA)) q = DMor= (ap (_,_ Γ) (! ([]Ty-assoc _ _ _))) refl (ap (λ z → z , var last) (weaken[]Mor _ _ _ ∙ ! (weakenMorInsert _ _ _ )))

qq-compS : (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) (X : ObS (suc k)) (q : ∂₁S g ≡ ftS X) → qqS (compS g f p) X (comp₁S g f p ∙ q) ≡ compS (qqS g X q) (qqS f (starS g X q) (p ∙ ! (ft-starS g X q))) (qq₁S f (starS g X q) (p ∙ ! (ft-starS g X q)) ∙ ! (qq₀S g X q))
qq-compS = //-elimP (λ g → //-elimP (λ f p → //-elimP λ X → qq-compS-// g f p X))


ss-ppS-// : {m n : ℕ} (f : DMor m (suc n)) → compS (ppS (starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f))))) (ssS (proj f)) (ss₁S (proj f) ∙ ! (pp₀S (starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))))) ≡ idS m (∂₀S (proj f))
ss-ppS-// (dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = DMor= refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor _) --eq (((CtxRefl dΓ) , (CtxRefl dΓ)) , MorSymm dΓ dΓ (congMorRefl (! (weakenMorInsert (idMor _) (idMor _) u ∙ idMor[]Mor (idMor _))) (idMorDerivable dΓ)))

ss-ppS : {m n : ℕ} (f : MorS m (suc n)) → compS (ppS (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f)))) (ssS f) (ss₁S f ∙ ! (pp₀S (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))))) ≡ idS m (∂₀S f)
ss-ppS {m} {n} = //-elimP (ss-ppS-// {m} {n})

ss-qqS-// : {m n : ℕ} (f : DMor m (suc n)) → (proj f) ≡ compS (qqS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))) (ssS (proj f)) (ss₁S (proj f) ∙ ! (qq₀S (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))))
ss-qqS-// (dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = DMor= refl refl (ap (λ z → z , u) (! (weakenMorInsert _ _ _ ∙ [idMor]Mor _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor δ))) -- eq ((CtxRefl dΓ , CtxRefl dΔ , dB , dB , (TyRefl dB) , (TyRefl dB)) , (congMorRefl (! (weakenMorInsert _ (idMor _) u ∙ [idMor]Mor _ ∙ weakenMorInsert _ δ u ∙ idMor[]Mor δ)) dδ) , (TmRefl du))

ss-qqS : {m n : ℕ} (f : MorS m (suc n)) → f ≡ compS (qqS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))) (ssS f) (ss₁S f ∙ ! (qq₀S (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))))
ss-qqS = //-elimP ss-qqS-//

ss-compS-// : {m n k : ℕ} (U : DCtx (suc k)) (g : DMor n k) (f : DMor m (suc n)) (g₁ : ∂₁S (proj g) ≡ ftS (proj U)) (f₁ : ∂₁S (proj f) ≡ starS (proj g) (proj U) g₁) {-g₀ : ∂₀ g ≡ ft (∂₁ f)-} → ssS (proj f) ≡ ssS (compS (qqS (proj g) (proj U) g₁) (proj f) (! (qq₀S (proj g) (proj U) g₁ ∙ ! f₁)))
ss-compS-// U@((Γ , A), (dΓ , dA)) g@(dmor (Δg , dΔg) (Γg , dΓg) δ dδ) f@(dmor (Θ , dΘ) ((Δf , A[g]), (dΔf , dA[g])) (θ , u) (dθ , du)) g₁ f₁ =
                  let (dΔf=Δg , _ , _ , dA[g]=A[δ] , _) = reflectOb f₁
                  in
                  eq (box (CtxRefl dΘ) (CtxRefl dΘ ,, TyTran (SubstTy (SubstTy dA (ConvMor dδ (CtxSymm dΔf=Δg) (reflectOb g₁))) dθ) (SubstTyEq dA[g]=A[δ] dθ) (congTyEq (! ([]Ty-assoc _ _ _)) (ap (_[_]Ty A) (! (weakenMorInsert _ _ _))) (TyRefl (SubstTy dA (SubstMor (ConvMor dδ (CtxSymm dΔf=Δg) (reflectOb g₁)) dθ))))) (idMor+= dΘ (TmRefl du)))


ss-compS : {m n k : ℕ} (U : ObS (suc k)) (g : MorS n k) (f : MorS m (suc n)) (g₁ : ∂₁S g ≡ ftS U) (f₁ : ∂₁S f ≡ starS g U g₁) → ssS f ≡ ssS (compS (qqS g U g₁) f (! (qq₀S g U g₁ ∙ ! f₁)))
ss-compS = //-elimP (λ U → //-elimP (λ g → //-elimP (ss-compS-// U g)))

{- The syntactic contextual category -}

synCCat : CCat
Ob synCCat = ObS
CCat.Mor synCCat = MorS
∂₀ synCCat = ∂₀S
∂₁ synCCat = ∂₁S
CCat.id synCCat = idS _
id₀ synCCat {n = n} {X = X} = id₀S n X
id₁ synCCat {n = n} {X = X} = id₁S n X
comp synCCat g f g₀ f₁ = compS g f (f₁ ∙ ! g₀)
comp₀ synCCat {g = g} {f = f} {g₀ = g₀} {f₁ = f₁} = comp₀S g f (f₁ ∙ ! g₀)
comp₁ synCCat {g = g} {f = f} {g₀ = g₀} {f₁ = f₁} = comp₁S g f (f₁ ∙ ! g₀)
ft synCCat = ftS
pp synCCat = ppS
pp₀ synCCat {X = X} = pp₀S X
pp₁ synCCat {X = X} = pp₁S X
star synCCat f X q f₁ = starS f X (f₁ ∙ ! q)
qq synCCat f X q f₁ = qqS f X (f₁ ∙ ! q)
qq₀ synCCat {f = f} {X = X} {q = q} {f₁ = f₁} = qq₀S f X (f₁ ∙ ! q)
qq₁ synCCat {f = f} {X = X} {q = q} {f₁ = f₁} = qq₁S f X (f₁ ∙ ! q)
ss synCCat f = ssS f
ss₀ synCCat {f = f} = ss₀S f
ss₁ synCCat {f = f} refl = ss₁S f
pt synCCat = ptS
pt-unique synCCat = pt-uniqueS
ptmor synCCat = ptmorS
ptmor₀ synCCat {X = X} = ptmor₀S X
ptmor₁ synCCat {X = X} = ptmor₁S X
ptmor-unique synCCat = ptmor-uniqueS
id-right synCCat {f = f} refl = id-rightS f
id-left synCCat {f = f} refl = id-leftS f
assoc synCCat {h = h} {g = g} {f = f} {f₁ = f₁} {g₀ = g₀} {g₁ = g₁} {h₀ = h₀} = assocS h g f (f₁ ∙ ! g₀) (g₁ ∙ ! h₀)
ft-star synCCat {f = f} {X = X} {p = p} {f₁ = f₁} = ft-starS f X (f₁ ∙ ! p)
pp-qq synCCat {f = f} {X = X} {p = p} {f₁ = f₁} = pp-qqS f X (f₁ ∙ ! p)
star-id synCCat {X = X} {p = refl} = star-idS X
qq-id synCCat {X = X} {p = refl} = qq-idS X
star-comp synCCat {g = g} {f = f} {f₁ = f₁} {g₀ = g₀} {X = X} {p = p} {g₁ = g₁} = star-compS g f X (f₁ ∙ ! g₀) (g₁ ∙ ! p)
qq-comp synCCat {g = g} {f} {f₁ = f₁} {g₀ = g₀} {X = X} {p = p} {g₁ = g₁} = qq-compS g f (f₁ ∙ ! g₀) X (g₁ ∙ ! p)
ss-pp synCCat {f = f} refl {f₁ = refl} = ss-ppS f
ss-qq synCCat {f = f} {f₁ = refl} = ss-qqS f
ss-comp synCCat {U = U} {p = p} {g = g} {g₁ = g₁} {f = f} {f₁ = f₁} = ss-compS U g f (g₁ ∙ ! p) f₁

{- The syntactic structured contextual category. We start with some helper functions. -}

module S = CCat+ synCCat

sectionS-eq : {Γ Δ : Ctx n} {dΓ : ⊢ Γ} {A : TyExpr n} {dΔ : ⊢ Δ} {dA : Derivable (Δ ⊢ A)} {δ : Mor n n} {dδ : Γ ⊢ δ ∷> Δ} {u : TmExpr n} {du : Derivable (Γ ⊢ u :> A [ δ ]Ty)}
            → S.is-section (proj (dmor (Γ , dΓ) ((Δ , A), (dΔ , dA)) (δ , u) (dδ , du)))
            → Γ ⊢ δ == idMor n ∷> Δ
sectionS-eq uₛ with reflect (S.is-section= refl uₛ refl)
... | box _ dΔ= dδ= = congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor _) refl dδ=

sectionS-eq-ctx : {Γ Δ : Ctx n} {dΓ : ⊢ Γ} {A : TyExpr n} {dΔ : ⊢ Δ} {dA : Derivable (Δ ⊢ A)} {δ : Mor n n} {dδ : Γ ⊢ δ ∷> Δ} {u : TmExpr n} {du : Derivable (Γ ⊢ u :> A [ δ ]Ty)}
            → S.is-section (proj (dmor (Γ , dΓ) ((Δ , A), (dΔ , dA)) (δ , u) (dδ , du)))
            → ⊢ Δ == Γ
sectionS-eq-ctx uₛ with reflect (S.is-section= refl uₛ refl)
... | box dΓ= dΔ= dδ= = CtxSymm dΓ=

getMor=idMor' : {a : DMor n (suc n)} (aₛ : S.is-section (proj a)) → ctx (lhs a) ⊢ getMor a == idMor n ∷> getCtx (rhs a)
getMor=idMor' {a = dmor _ _ (δ , _) _} aₛ = congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor _) refl (unMor≃-mor (reflect (S.is-section= refl aₛ refl)))

morTm=idMorTm' : {a : DMor n (suc n)} (aₛ : S.is-section (proj a)) → ctx (lhs a) ⊢ mor a == idMor n , getRHS (mor a) ∷> (ctx (rhs a))
morTm=idMorTm' {a = dmor _ ((_ , _) , (_ , _)) (δ , _) (_ , du)} aₛ = (getMor=idMor' aₛ) , (TmRefl du)


dTy : {Γ : DCtx n} (A : DCtx (suc n)) (A= : proj {R = ObEquiv} (getCtx A , getdCtx A) ≡ proj Γ) → Derivable (ctx Γ ⊢ getTy A)
dTy ((_ , _ ) , (_ , dA)) dA= = ConvTy dA (reflectOb dA=)

dTy= : {Γ : DCtx n} {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : ftS (proj A) ≡ proj Γ) → Derivable (ctx Γ ⊢ getTy A == getTy A')
dTy= {A = ((ΓA , A) , (dΓA , dA))} {A' = ((ΓA' , A') , (dΓA' , dA'))} (box (_ , _ , _ , dA= , _)) A= = ConvTyEq dA= (reflectOb A=)


combine : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : ftS (proj B) ≡ proj A) → ftS (proj B) ≡ proj ((ctx Γ , getTy A) , (der Γ , dTy A A=))
combine {A = A} A= B B= = B= ∙ eq (box (CtxTran (CtxSymm (CtxTy=Ctx' A)) (reflectOb A= ,, TyRefl (getdTy A)) ))

dTy+ : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : ftS (proj B) ≡ proj A) → Derivable ((ctx Γ , getTy A) ⊢ getTy B)
dTy+ A= B B= = dTy B (combine A= B B=)

dTy+= : {Γ : DCtx n} {A  : DCtx (suc n)} {B B' : DCtx (suc (suc n))} (A= : ftS (proj A) ≡ proj Γ) (rB : B ≃ B') (B= : ftS (proj B) ≡ proj A) → Derivable ((ctx Γ , getTy A) ⊢ getTy B == getTy B')
dTy+= {B = B} A= rB B= = dTy= rB (combine A= B B=)

lemmathing : {Γ Δ : DCtx (suc n)} → Γ ≃ Δ → Derivable (ctx (ftS-// Δ) ⊢ getTy Γ == getTy Δ)
lemmathing {Γ = ((Γ , A) , (dΓ , dA))} {Δ = ((Δ , B) , (dΔ , dB))} (box (_ , _ , _ , _ , dA=)) = dA=


dMor : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) → ctx Γ ⊢ mor a ∷> (ctx Γ , getTy A)
dMor {A = A} A= a aₛ a₁ = ConvMor (morDer a) (reflectOb (S.is-section₀ aₛ a₁ ∙ A=)) (CtxTran (reflectOb a₁) (CtxSymm (CtxTy=Ctx A A=)))

--ConvMor (getdMor a) (reflectOb (S.is-section₀ aₛ a₁ ∙ A=)) (CtxTran (getCtx= (reflect a₁)) (reflectOb A=))

getMor=idMor : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) → ctx Γ ⊢ getMor a == idMor n ∷> ctx Γ
getMor=idMor A= a aₛ a₁ = ConvMorEq (getMor=idMor' aₛ) (reflectOb (S.is-section₀ aₛ a₁ ∙ A=)) (CtxTran (getCtx= (reflect a₁)) (reflectOb A=))

morTm=idMorTm : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A)  → ctx Γ ⊢ mor a == idMor n , getRHS (mor a) ∷> (ctx Γ , getTy A)
morTm=idMorTm {A = A} A= a aₛ a₁ = ConvMorEq (morTm=idMorTm' aₛ) (reflectOb (S.is-section₀ aₛ a₁ ∙ A=)) (CtxTran (reflectOb a₁) (CtxSymm (CtxTy=Ctx A A=)))

dTm : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) → Derivable (ctx Γ ⊢ getTm a :> getTy A)
dTm {A = A} A= a aₛ a₁ =
  let lhsa=Γ = reflectOb (S.is-section₀ aₛ a₁ ∙ A=)
      lhsa=ftA = reflectOb (S.is-section₀ aₛ a₁)     
  in
  ConvTm2 (getdTm a) lhsa=Γ (TyTran (ConvTy (getdTy (rhs a)) (CtxTran (getCtx= (reflect a₁)) (CtxSymm (lhsa=ftA)))) (congTyEq refl ([idMor]Ty _) (SubstTyMorEq (getdTy (rhs a)) (getdMor a) (getMor=idMor' aₛ))) (ConvTyEq (lemmathing (reflect a₁)) (CtxSymm lhsa=ftA)))
                        
dTmSubst : {Γ : DCtx n} {A : DCtx (suc n)} (A= : S.ft (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : S.ft (proj B) ≡ proj A) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : S.∂₁ (proj a) ≡ proj A) (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : S.∂₁ (proj b) ≡ S.star (proj a) (proj B) B= a₁) → Derivable (ctx Γ ⊢ getTm b :> substTy (getTy B) (getTm a)) 
dTmSubst {Γ = Γ} {A} A= B B= a aₛ a₁ b bₛ b₁ =
  let lhsa=Γ = reflectOb (S.is-section₀ aₛ a₁ ∙ A=)
      lhsa=ftA = reflectOb (S.is-section₀ aₛ a₁)
      rhsa=A = reflectOb a₁
  in
  Conv (SubstTy (dTy B B=) (ConvMor (morDer a) lhsa=Γ rhsa=A)) (dTm (S.is-section₀ aₛ a₁ ∙ A=) b bₛ b₁) (SubstTyMorEq (dTy B B=) (ConvMor (morDer a) lhsa=Γ rhsa=A) (ConvMorEq (morTm=idMorTm' aₛ) lhsa=Γ rhsa=A))

dTm+ : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) {B : DCtx (suc (suc n))} (B= : ftS (proj B) ≡ proj A) (u : DMor (suc n) (suc (suc n))) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) → Derivable ((ctx Γ , getTy A) ⊢ getTm u :> getTy B)
dTm+ A= {B = B} B= u uₛ u₁ = dTm (combine A= B B=) u uₛ u₁

dTm= : {Γ : DCtx n} {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : ftS (proj A) ≡ proj Γ) {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ proj A) (a'₁ : ∂₁S (proj a') ≡ proj A') → Derivable (ctx Γ ⊢ getTm a == getTm a' :> getTy A)
dTm= rA A= {a} {a'} ra aₛ a'ₛ a₁ a'₁ = 
  let lhsa=Γ = reflectOb (S.is-section₀ aₛ a₁ ∙ A=)
      lhsa=ftA = reflectOb (S.is-section₀ aₛ a₁)
      rhsa=A = reflectOb a₁
  in
  ConvTmEq2 (getRHS= (unMor≃-mor ra)) lhsa=Γ (TyTran (ConvTy (getdTy (rhs a)) (CtxTran (getCtx= (reflect a₁)) (CtxSymm (lhsa=ftA)))) (congTyEq refl ([idMor]Ty _) (SubstTyMorEq (getdTy (rhs a)) (getdMor a) (getMor=idMor' aₛ))) (ConvTyEq (lemmathing (reflect a₁)) (CtxSymm lhsa=ftA)))

dTmSubst= : {Γ : DCtx n} {A A' : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : ftS (proj B) ≡ proj A) (B'= : ftS (proj B') ≡ proj A') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ proj A) (a'₁ : ∂₁S (proj a') ≡ proj A') {b b' : DMor n (suc n)} (rb : b ≃ b') (bₛ : S.is-section (proj b)) (b'ₛ : S.is-section (proj b')) (b₁ : ∂₁S (proj b) ≡ S.star (proj a) (proj B) B= a₁) (b'₁ : ∂₁S (proj b') ≡ S.star (proj a') (proj B') B'= a'₁) → Derivable (ctx Γ ⊢ getTm b == getTm b' :> substTy (getTy B) (getTm a))
dTmSubst= {A = A} A= {B} {B'} rB B= B'= {a} {a'} ra aₛ a'ₛ a₁ a'₁ {b} {b'} rb bₛ b'ₛ b₁ b'₁  = 
  let lhsa=Γ = reflectOb (S.is-section₀ aₛ a₁ ∙ A=)
      lhsa=ftA = reflectOb (S.is-section₀ aₛ a₁)
      rhsa=A = reflectOb a₁     
  in
    ConvEq ((SubstTy (dTy B B=) (ConvMor (morDer a) lhsa=Γ rhsa=A))) (dTm= (box (unMor≃-lhs ra ,, SubstTyMorEq2 (der (lhs a)) (der (rhs a)) (ConvTyEq (dTy+= A= rB B=) (CtxTran (CtxTy=Ctx A A=) (CtxSymm rhsa=A))) (unMor≃-mor ra))) (S.is-section₀ aₛ a₁ ∙ A=) rb bₛ b'ₛ b₁ b'₁) (SubstTyMorEq (dTy B B=) (ConvMor (morDer a) lhsa=Γ rhsa=A) (ConvMorEq (morTm=idMorTm' aₛ) lhsa=Γ rhsa=A))


dTm+= : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : ftS (proj B) ≡ proj A) {u u' : DMor (suc n) (suc (suc n))} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : ∂₁S (proj u) ≡ proj B) (u'₁ : ∂₁S (proj u') ≡ proj B') → Derivable ((ctx Γ , getTy A) ⊢ getTm u == getTm u' :> getTy B)
dTm+= A= {B = B} rB B= ru uₛ u'ₛ u₁ u'₁ = dTm= rB (combine A= B B=) ru uₛ u'ₛ u₁ u'₁


up-to-rhsTyEq : {Γ : DCtx n} {A B : TyExpr n}  {δ : Mor n (suc n)} {w₁ : _} {w₂ : _} {w₃ : _} {w₄ : _} (Tyeq : A ≡ B) → proj {R = MorEquiv} (dmor Γ ((ctx Γ , A) , w₁) δ w₂) ≡ proj (dmor Γ ((ctx Γ , B) , w₃) δ w₄)
up-to-rhsTyEq refl = refl


{- Elimination principles for Ty and Tm -}

_×S_ : (A B : Set) → Set
A ×S B = ΣSS A (λ _ → B)

infixr 42 _×S_

//-elim-Ctx : ∀ {l} {C : (Γ : ObS n) → Set l}
           → (proj* : (Γ : DCtx n) → C (proj Γ))
           → (eq* : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → PathOver C (eqR rΓ) (proj* Γ) (proj* Γ'))
           → (Γ : ObS n) → C Γ
//-elim-Ctx proj* eq* = //-elim proj* eq*

uncurrifyTy : ∀ {l} {Γ : ObS n} (C : (A : ObS (suc n)) (A= : ftS A ≡ Γ) → Set l) → ΣS (ObS (suc n)) (λ A → ftS A ≡ Γ) → Set l
uncurrifyTy C (A , A=) = C A A=

uncurrifyTy+ : ∀ {l} {X : Set} {Γ : X → ObS n} (C : (x : X) (A : ObS (suc n)) (A= : ftS A ≡ Γ x) → Set l) → ΣS (X ×S ObS (suc n)) (λ {(x , A) → ftS A ≡ Γ x}) → Set l
uncurrifyTy+ C ((x , A) , A=) = C x A A=

//-elim-Ty : ∀ {l} {Γ : ObS n} {C : (A : ObS (suc n)) (A= : ftS A ≡ Γ) → Set l}
           → (proj* : (A : DCtx (suc n)) (A= : ftS (proj A) ≡ Γ) → C (proj A) A=)
           → (eq* : {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : ftS (proj A) ≡ Γ) (A'= : ftS (proj A') ≡ Γ) → PathOver (uncurrifyTy C) (Σ= (eqR rA)) (proj* A A=) (proj* A' A'=))
           → (A : ObS (suc n)) (A= : ftS A ≡ Γ) → C A A=
//-elim-Ty proj* eq* = //-elim proj* (λ a= → PathOver-PropPi (λ A= A'= → eq* a= A= A'=))

//-elimP-Ty : ∀ {l} {X : Set} {Γ : X → ObS n} {C : (x : X) (A : ObS (suc n)) (A= : ftS A ≡ Γ x) → Set l}
           → {x x' : X} {p : x ≡R x'}
           → {lhs : (A : ObS (suc n)) (A= : ftS A ≡ Γ x) → C x A A=}
           → {rhs : (A : ObS (suc n)) (A= : ftS A ≡ Γ x') → C x' A A=}
           → (proj* : (A : DCtx (suc n)) (A= : _) (A=' : _) → PathOver (uncurrifyTy+ C) (Σ= (apR (λ z → z , proj A) p)) (lhs (proj A) A=) (rhs (proj A) A='))
           → PathOver (λ x → (A : ObS (suc n)) (A= : ftS A ≡ Γ x) → C x A A=) p lhs rhs
//-elimP-Ty {p = reflR} proj* = PathOver-CstPi (//-elimP (λ A → PathOver-PropPi (λ A= A=' → PathOver-in (PathOver-out (proj* A A= A=')))))

uncurrifyTm : ∀ {l} {A : ObS (suc n)} (C : (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ A) → Set l) → ΣS (MorS n (suc n)) (λ u → (S.is-section u) × (S.∂₁ u ≡ A)) → Set l
uncurrifyTm C (u , (uₛ , u₁)) = C u uₛ u₁

uncurrifyTm+ : ∀ {l} {X : Set} {A : X → ObS (suc n)} (C : (x : X) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ A x) → Set l) → ΣS (X ×S MorS n (suc n)) (λ {(x , u) → (S.is-section u) × (S.∂₁ u ≡ A x)}) → Set l
uncurrifyTm+ C ((x , u) , (uₛ , u₁)) = C x u uₛ u₁

//-elim-Tm : ∀ {l} {A : ObS (suc n)} {C : (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ A) → Set l}
           → (proj* : (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : S.∂₁ (proj u) ≡ A) → C (proj u) uₛ u₁)
           → (eq* : {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : _) (u'ₛ : _) (u₁ :  S.∂₁ (proj u) ≡ A) (u'₁ : S.∂₁ (proj u') ≡ A ) → PathOver (uncurrifyTm C) (Σ= {b = uₛ , u₁} {b' = u'ₛ , u'₁} (eqR ru)) (proj* u uₛ u₁) (proj* u' u'ₛ u'₁))
           → (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ A) → C u uₛ u₁
//-elim-Tm {n = n} {C = C} proj* eq* = //-elim proj* (λ ru → PathOver-PropPi (λ uₛ uₛ' → PathOver-PropPi (λ u₁ u₁' → PathOver-in (PathOver-= (lemma (eqR ru)) (PathOver-out (eq* ru uₛ uₛ' u₁ u₁'))))))  where

  lemma : {u u' : MorS n (suc n)} (p : u ≡R u') {uₛ : _} {u'ₛ : _} {u₁ : _} {u'₁ : _}
        → apR (uncurrifyTm C) (Σ= {b = uₛ , u₁} {b' = u'ₛ , u'₁} p) ≡R apR (uncurrify (λ a z → C (fst a) (snd a) z)) (Σ= {b = u₁} {b' = u'₁} (Σ= {b = uₛ} {b' = u'ₛ} p))
  lemma reflR = reflR


//-elimP-Tm : ∀ {l} {X : Set} {A : X → ObS (suc n)} {C : (x : X) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ A x) → Set l}
           → {x x' : X} {p : x ≡R x'}
           → {lhs : (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ A x) → C x u uₛ u₁}
           → {rhs : (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ A x') → C x' u uₛ u₁}
           → (proj* : (u : DMor n (suc n)) (uₛ : _) (u₁ : _) (u₁' : _) → PathOver (uncurrifyTm+ C) (Σ= {b = uₛ , u₁} {b' = uₛ , u₁'} (apR (λ z → z , proj u) p)) (lhs (proj u) uₛ u₁) (rhs (proj u) uₛ u₁'))
           → PathOver (λ x → (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ A x) → C x u uₛ u₁) p lhs rhs
//-elimP-Tm {p = reflR} proj* = PathOver-CstPi (//-elimP (λ u → PathOver-CstPropPi (λ uₛ → PathOver-PropPi (λ u₁ u₁' → PathOver-in (PathOver-out (proj* u uₛ u₁ u₁'))))))

proj= : ∀ {l l'} {A : Set l} {B : Set l'} {a a' : A} {p : a ≡R a'} {u v : B}
      → u ≡ v → PathOver (λ _ → B) p u v
proj= {p = reflR} refl = reflo


-- This function does the pattern matching on g₀ needed for the naturalities
JforNat : {A : Set} {∂₀g : A} {T : (Δ : A) (g₀ : ∂₀g ≡ Δ) → Prop}
        → (T ∂₀g refl)
        → ((Δ : A) (g₀ : ∂₀g ≡ Δ) → T Δ g₀)
JforNat d _ refl = d

{-- Term formers --}

dmorTm : (Γ : DCtx n) (A : TyExpr n) (dA : Derivable (ctx Γ ⊢ A)) (u : TmExpr n) (du : Derivable (ctx Γ ⊢ u :> A)) → DMor n (suc n)
dmorTm Γ A dA u du = dmor Γ ((ctx Γ , A) , # (der Γ , dA)) (idMor _ , u) (# (idMor+ (der Γ) du))

dmorTm= : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ')
         → {A A' : TyExpr n} (dA : _) (dA' : _) (dA= : Derivable (ctx Γ ⊢ A == A'))
         → {u u' : TmExpr n} (du : _) (du' : _) (du= : Derivable (ctx Γ ⊢ u == u' :> A))
         → proj {R = MorEquiv} (dmorTm Γ A dA u du) ≡ proj (dmorTm Γ' A' dA' u' du')
dmorTm= {Γ = Γ} rΓ _ _ dA= _ _ du= = # (eq (box (unOb≃ rΓ) (unOb≃ rΓ ,, dA=) (idMor+= (der Γ) du=)))

dmorTmₛ : {Γ : DCtx n} {A : TyExpr n} (dA : Derivable (ctx Γ ⊢ A)) {u : TmExpr n} (du : Derivable (ctx Γ ⊢ u :> A)) → S.is-section (proj {R = MorEquiv} (dmorTm Γ A dA u du))
dmorTmₛ {Γ = Γ} dA du = S.is-section→ (eq (box (CtxRefl (der Γ)) (CtxRefl (der Γ)) (congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable (der Γ))))))

