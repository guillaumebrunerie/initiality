{-# OPTIONS --rewriting --allow-unsolved-metas --prop #-}

open import common
open import contextualcat
open import quotients
open import syntx
open import rules

open CCat hiding (Mor)

{- Preliminary definitions -}

record DCtx (n : ℕ) : Set where
  constructor _,_
  field
    ctx : Ctx n
    der : ⊢ ctx
open DCtx public

record DMor (n m : ℕ) : Set where
  constructor dmor
  field
    lhs : DCtx n
    rhs : DCtx m
    mor : Mor n m
    morDer : ctx lhs ⊢ mor ∷> ctx rhs
open DMor public

instance
  ObEquiv : (n : ℕ) → EquivRel (DCtx n)
  EquivRel._≃_ (ObEquiv n) (Γ , _) (Γ' , _) = ⊢ Γ == Γ'
  EquivRel.ref (ObEquiv n) (Γ , dΓ) = CtxRefl dΓ
  EquivRel.sym (ObEquiv n) p = CtxSymm p
  EquivRel.tra (ObEquiv n) p q = CtxTran p q

  MorEquiv : (n m : ℕ) → EquivRel (DMor n m)
  EquivRel._≃_ (MorEquiv n m) (dmor (Γ , _) (Δ , _) δ _) (dmor (Γ' , _) (Δ' , _) δ' _) = ((⊢ Γ == Γ') × (⊢ Δ == Δ')) × (Γ ⊢ δ == δ' ∷> Δ)
  EquivRel.ref (MorEquiv n m) (dmor (_ , dΓ) (_ , dΔ) _ dδ) = (CtxRefl dΓ , CtxRefl dΔ) , (MorRefl dδ)
  EquivRel.sym (MorEquiv n m) {a = dmor (_ , dΓ) (_ , dΔ) _ _} ((Γ= , Δ=), δ=) = (CtxSymm Γ= , CtxSymm Δ=) , ConvMorEq (MorSymm dΓ dΔ δ=) Γ= Δ=
  EquivRel.tra (MorEquiv n m) {a = dmor (_ , dΓ) (_ , dΔ) _ _} ((Γ= , Δ=), δ=) ((Γ'= , Δ'=), δ'=) = (CtxTran Γ= Γ'= , CtxTran Δ= Δ'=) , (MorTran dΓ dΔ δ= (ConvMorEq δ'= (CtxSymm Γ=) (CtxSymm Δ=)))


{- The syntactic contextual category -}

ObS : ℕ → Set
ObS n = DCtx n // ObEquiv n

MorS : ℕ → ℕ → Set
MorS n m = DMor n m // MorEquiv n m

∂₀S : {n m : ℕ} → MorS n m → ObS n
∂₀S = //-rec (λ δ → proj (lhs δ)) (λ r → eq (fst (fst r)))

∂₁S : {n m : ℕ} → MorS n m → ObS m
∂₁S = //-rec (λ δ → proj (rhs δ)) (λ r → eq (snd (fst r)))

idS-u : (n : ℕ) → DCtx n → DMor n n
idS-u n (Γ , dΓ) = dmor (Γ , dΓ) (Γ , dΓ) (idMor n) (idMorDerivable dΓ)

idS : (n : ℕ) → ObS n → MorS n n
idS n = //-rec (λ Γ → proj (idS-u n Γ)) (λ {r → eq ((r , r) , MorRefl (idMorDerivable (CtxEqCtx1 r)))})

id₀S : (n : ℕ) (X : ObS n) → ∂₀S (idS n X) ≡ X
id₀S n = //-elimP (λ Γ → refl)

id₁S : (n : ℕ) (X : ObS n) → ∂₁S (idS n X) ≡ X
id₁S n = //-elimP (λ Γ → refl)

compS-// : (g : DMor m k) (f : DMor n m) (_ : ∂₁S (proj f) ≡ ∂₀S (proj g)) → MorS n k
compS-// (dmor Δd@(Δ , dΔ) Θd θ dθ) (dmor Γd@(Γ , dΓ) Δd'@(Δ' , dΔ') δ dδ) p = proj (dmor Γd Θd (θ [ δ ]Mor) (SubstMor dθ (ConvMor dδ (CtxRefl dΓ) (reflect p))))

compS-eq : (g g' : DMor m k) (r : g ≃ g') (f f' : DMor n m) (r' : f ≃ f') (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj f') ≡ ∂₀S (proj g')) → compS-// g f p ≡ compS-// g' f' q
compS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ') ((dΓ= , dΔ=) , dδ=) (dmor (Γ'' , dΓ'') (Δ'' , dΔ'') δ'' dδ'') (dmor (Γ''' , dΓ''') (Δ''' , dΔ''') δ''' dδ''') ((dΓ''= , dΔ''=) ,  dδ''=) p q =
  eq ((dΓ''= , dΔ=) , SubstMorFullEq dΔ'' dΔ (ConvMor dδ' (CtxSymm (CtxTran (reflect p) dΓ=)) (CtxSymm dΔ=)) (ConvMorEq dδ= (CtxSymm (CtxTran (reflect p) (CtxRefl dΓ))) (CtxRefl dΔ)) dδ'' dδ''=)


compS : (g : MorS m k) (f : MorS n m) (_ : ∂₁S f ≡ ∂₀S g) → MorS n k
compS {n = n} {m = m} {k = k} =
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

ftS-// : {n : ℕ} → DCtx (suc n) → ObS n
ftS-// ((Γ , A), (dΓ , dA)) = proj (Γ , dΓ)

ftS-eq : {Γ Γ' : DCtx (suc n)} → ⊢ ctx Γ == ctx Γ' → ftS-// Γ ≡ ftS-// Γ'
ftS-eq {Γ = (_ , _) , _} {(_ , _) , _} r = eq (fst r)

ftS : {n : ℕ} → ObS (suc n) → ObS n
ftS = //-rec ftS-// ftS-eq

ppS-// : (X : DCtx (suc n)) → MorS (suc n) n
ppS-// {n = n} Γd@((Γ , A), (dΓ , dA)) = proj (dmor Γd (Γ , dΓ) (weakenMor (idMor n)) (WeakMor A (idMorDerivable dΓ)))

ppS-eq : {X X' : DCtx (suc n)} (_ : X ≃ X') → ppS-// X ≡ ppS-// X'
ppS-eq {X = (Γ , A), (dΓ , dA)} {(Γ' , A'), (dΓ' , dA')} (dΓ= , dA=) = eq (((dΓ= , dA=) , dΓ=) , (MorRefl (WeakMor A (idMorDerivable dΓ))))

ppS : (X : ObS (suc n)) → MorS (suc n) n
ppS {n = n} = //-rec ppS-// ppS-eq

pp₀S : (X : ObS (suc n)) → ∂₀S (ppS X) ≡ X
pp₀S = //-elimP (λ {((Γ , A), (dΓ , dA)) → refl})

pp₁S : (X : ObS (suc n)) → ∂₁S (ppS X) ≡ ftS X
pp₁S = //-elimP (λ {((Γ , A), (dΓ , dA)) → refl})

ptS : ObS 0
ptS = proj (◇ , tt)

pt-uniqueS : (X : ObS 0) → X ≡ proj (◇ , tt)
pt-uniqueS = //-elimP (λ {(◇ , tt) → eq tt})

ptmorS : (X : ObS n) → MorS n 0
ptmorS = //-rec (λ Γ → proj (dmor Γ (◇ , tt) ◇ tt)) (λ r → eq ((r , tt) , tt))

ptmor₀S : (X : ObS n) → ∂₀S (ptmorS X) ≡ X
ptmor₀S = //-elimP (λ Γ → refl)

ptmor₁S : (X : ObS n) → ∂₁S (ptmorS X) ≡ ptS
ptmor₁S = //-elimP (λ Γ → refl)

ptmor-uniqueS-// : (X : DCtx n) (f : DMor n 0) (p : ∂₀S (proj f) ≡ proj X) (q : ∂₁S (proj f) ≡ ptS) → proj f ≡ ptmorS (proj X)
ptmor-uniqueS-// X (dmor Γ (◇ , tt) ◇ tt) p q = eq ((reflect p , tt) , tt)

ptmor-uniqueS : (X : ObS n) (f : MorS n 0) (p : ∂₀S f ≡ X) (q : ∂₁S f ≡ ptS) → f ≡ ptmorS X
ptmor-uniqueS = //-elimP (λ X → //-elimP (ptmor-uniqueS-// X))

id-rightS-// : (f : DMor n m) → compS (idS m (∂₁S (proj f))) (proj f) (! (id₀S m (∂₁S (proj f)))) ≡ (proj f)
id-rightS-// {m = m} (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) = ap-irr (λ x z → proj (dmor (Γ , dΓ) (Δ , dΔ) x z)) (idMor[]Mor δ)

id-rightS : (f : MorS n m) → compS (idS m (∂₁S f)) f (! (id₀S m (∂₁S f))) ≡ f
id-rightS = //-elimP id-rightS-//

id-leftS-// : (f : DMor n m) → compS (proj f) (idS n (∂₀S (proj f))) (id₁S n (∂₀S (proj f))) ≡ (proj f)
id-leftS-// {n = n} (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) = ap-irr (λ x z → proj (dmor (Γ , dΓ) (Δ , dΔ) x z)) ([idMor]Mor δ)

id-leftS : (f : MorS n m) → compS f (idS n (∂₀S f)) (id₁S n (∂₀S f)) ≡ f
id-leftS = //-elimP id-leftS-//

assocS-// : (h : DMor k l) (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj g) ≡ ∂₀S (proj h)) → compS (compS (proj h) (proj g) q) (proj f) (p ∙ ! (comp₀S (proj h) (proj g) q)) ≡ compS (proj h) (compS (proj g) (proj f) p) (comp₁S (proj g) (proj f) p ∙ q)
assocS-// (dmor (Θ' , dΘ') (Φ , dΦ) φ dφ) (dmor (Δ' , dΔ') (Θ , dΘ) θ dθ) (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) p q =
  ap-irr (λ x z → proj (dmor (Γ , dΓ) (Φ , dΦ) x z))
         ([]Mor-assoc δ θ φ)

assocS : (h : MorS k l) (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) (q : ∂₁S g ≡ ∂₀S h) → compS (compS h g q) f (p ∙ ! (comp₀S h g q)) ≡ compS h (compS g f p) (comp₁S g f p ∙ q)
assocS = //-elimP (λ h → //-elimP (λ g → //-elimP (λ f → assocS-// h g f)))

starS-//-u : (f : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj f) ≡ ftS (proj X)) → DCtx (suc m)
starS-//-u (dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) ((Δ , B) , (dΔ , dB)) p = ((Γ , B [ δ ]Ty) , (dΓ , (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)))))

starS-// : (f : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj f) ≡ ftS (proj X)) → ObS (suc m)
starS-// f x p = proj (starS-//-u f x p)

starS-eq : (f g : DMor m n) (r : f ≃ g) (X Y : DCtx (suc n)) (r' : X ≃ Y) (p : ∂₁S (proj f) ≡ ftS (proj X)) (q : ∂₁S (proj g) ≡ ftS (proj Y)) → starS-// f X p ≡ starS-// g Y q
starS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ)
         (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ')
         ((dΓ= , dΔ=) , dδ=)
         ((Γ'' , A) , (dΓ'' , dA))
         ((Δ'' , B) , (dΔ'' , dB))
         (dΓ''= , dA , dB , dA= , dA=')
         p q = eq (dΓ= , SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflect p))
                       , SubstTy dB (ConvMor dδ' (CtxRefl dΓ') (reflect q))
                       , SubstTyFullEq dB (ConvMor dδ (CtxRefl dΓ) (CtxTran dΔ= (reflect q)))
                                          (ConvTyEq dA= dΓ''=)
                                          (ConvMorEq dδ= (CtxRefl dΓ) (CtxTran dΔ= (reflect q)))
                       , SubstTyFullEq dB (ConvMor dδ dΓ= (CtxTran dΔ= (reflect q)))
                                          (ConvTyEq dA= dΓ''=)
                                          (ConvMorEq dδ= dΓ= (CtxTran dΔ= (reflect q))))

starS : (f : MorS m n) (X : ObS (suc n)) (_ : ∂₁S f ≡ ftS X) → ObS (suc m)
starS {n = n} {m = m} =
  //-elim-PiS (λ f → //-elim-PiP (starS-// f)
                         (λ r → starS-eq f f (ref f) _ _ r))
          (λ r → //-elimP-PiP (λ X → starS-eq _ _ r X X (ref X)))

qqS-// : (f : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj f) ≡ ftS (proj X)) → MorS (suc m) (suc n)
qqS-// f@(dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) X@((Δ , A) , (dΔ , dA)) p = proj (dmor (starS-//-u f X p) X (weakenMor δ , var last) ((WeakMor _ (ConvMor dδ (CtxRefl dΓ) (reflect p))) , aux))  where
  aux : Derivable ((Γ , (A [ δ ]Ty)) ⊢ var last :> (A [ weakenMor δ ]Ty))
  aux = congTm (weaken[]Ty A δ last) refl (VarLast (SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflect p)))) 


qqS-eq : (f g : DMor m n) (r : f ≃ g) (Γ Δ : DCtx (suc n)) (r' : Γ ≃ Δ) (p : ∂₁S (proj f) ≡ ftS (proj Γ)) (q : ∂₁S (proj g) ≡ ftS (proj Δ)) → qqS-// f Γ p ≡ qqS-// g Δ q
qqS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ') ((dΓ= , dΔ=) , dδ=) ((Γ'' , A) , (dΓ'' , dA)) ((Δ'' , B) , (dΔ'' , dB)) (dΓ''= , dA , dB , dA= , dA=') p q = eq (((( dΓ= , SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflect p)) , SubstTy dB (ConvMor dδ' (CtxRefl dΓ') (reflect q)) , SubstTyFullEq dB (ConvMor dδ (CtxRefl dΓ) (CtxTran dΔ= (reflect q))) (ConvTyEq dA= dΓ''=) (ConvMorEq dδ= (CtxRefl dΓ) (CtxTran dΔ= (reflect q))) , SubstTyFullEq dB (ConvMor dδ dΓ= (CtxTran dΔ= (reflect q))) (ConvTyEq dA= dΓ''=) (ConvMorEq dδ= dΓ= (CtxTran dΔ= (reflect q))) ) , ( dΓ''= , dA , dB , dA= , dA=')) , ( WeakMorEq _ (ConvMorEq dδ= (CtxRefl dΓ) (reflect p)) , congTmRefl (weakenDerLast dA (ConvMor dδ (CtxRefl dΓ) (reflect p))) refl)))

qqS : (f : MorS m n) (X : ObS (suc n)) (_ : ∂₁S f ≡ ftS X) → MorS (suc m) (suc n)
qqS {n = n} {m = m} =
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
ssS-//-u {m = m} f@(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = dmor (Γ , dΓ) ((Γ , B [ δ ]Ty) , (dΓ , SubstTy dB dδ)) (idMor _ , u) (idMorDerivable _ , congTm (! ([idMor]Ty _)) refl du)

ssS-// : (f : DMor m (suc n)) → MorS m (suc m)
ssS-// f = proj (ssS-//-u f)

ssS-eq : {f f' : DMor m (suc n)} (_ : f ≃ f') → ssS-// f ≡ ssS-// f'
ssS-eq {m = m} {f@(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du))} {f'@(dmor (Γ' , dΓ') ((Δ' , B'), (dΔ' , dB')) (δ' , u') (dδ' , du'))} p@((dΓ= , (dΔ= , dB , dB' , dB= , dB=')) , (dδ= , du=))
  = eq {a = ssS-//-u f} {b = ssS-//-u f'} ((dΓ= , (dΓ= , SubstTy dB dδ , SubstTy dB' dδ' ,  SubstTyFullEq (ConvTy dB' (CtxSymm dΔ=)) dδ dB= dδ= , SubstTyFullEq (ConvTy dB' (CtxSymm dΔ=)) (ConvMor dδ dΓ= (CtxRefl dΔ)) dB= (ConvMorEq dδ= dΓ= (CtxRefl dΔ)))) , (MorRefl (idMorDerivable dΓ) , congTmEqTy (! ([idMor]Ty _)) du=))

ssS : (f : MorS m (suc n)) → MorS m (suc m)
ssS {n = n} = //-rec ssS-// ssS-eq

ss₀S : (f : MorS m (suc n)) → ∂₀S (ssS f) ≡ ∂₀S f
ss₀S = //-elimP (λ {(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) → refl})

ss₁S-// : (f : DMor m (suc n)) → ∂₁S (ssS (proj f)) ≡ starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S _))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S _)) ∙ pp₁S (∂₁S (proj f)))
ss₁S-// (dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = ap-irr (λ x z → proj ((Γ , B [ x ]Ty) , z)) (! (weakenMorInsert (idMor _) δ u ∙ idMor[]Mor δ))

ss₁S : (f : MorS m (suc n)) → ∂₁S (ssS f) ≡ starS (compS (ppS (∂₁S f)) f (! (pp₀S _))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S _)) ∙ pp₁S (∂₁S f))
ss₁S = //-elimP ss₁S-//

ft-starS-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → ftS (starS (proj f) (proj X) p) ≡ ∂₀S (proj f)
ft-starS-// (dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) ((Δ , B), (dΔ , dB)) p = refl 

ft-starS : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → ftS (starS f X p) ≡ ∂₀S f
ft-starS = //-elimP (λ f → //-elimP (ft-starS-// f))

pp-qqS-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → compS (ppS (proj X)) (qqS (proj f) (proj X) p) (qq₁S (proj f) (proj X) p ∙ ! (pp₀S (proj X))) ≡ compS (proj f) (ppS (starS (proj f) (proj X) p)) (pp₁S (starS (proj f) (proj X) p) ∙ ft-starS (proj f) (proj X) p)
pp-qqS-// (dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) ((Δ , B), (dΔ , dB)) p = eq (((CtxRefl dΓ , SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)) , SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)) , TyRefl (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p))) , TyRefl (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)))) , CtxSymm (reflect p)) , MorSymm (dΓ , (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)))) dΔ (congMorRefl ( ! (weaken[]Mor δ (idMor _) last) ∙ ap (λ z → weakenMor z) ([idMor]Mor δ) ∙ ! ([weakenMor]Mor δ (idMor _) ∙ ap (λ z → weakenMor z) (idMor[]Mor δ))) (SubstMor (ConvMor dδ (CtxRefl dΓ) (reflect p)) (WeakMor _ (idMorDerivable dΓ)))))

pp-qqS : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → compS (ppS X) (qqS f X p) (qq₁S f X p ∙ ! (pp₀S X)) ≡ compS f (ppS (starS f X p)) (pp₁S (starS f X p) ∙ ft-starS f X p)
pp-qqS = //-elimP (λ f → //-elimP (pp-qqS-// f))

star-idS : {n : ℕ} (X : ObS (suc n)) → starS (idS n (ftS X)) X (id₁S n (ftS X)) ≡ X
star-idS = //-elimP (λ {((Γ , A), (dΓ , dA)) → ap-irr (λ x z → proj ((Γ , x) , z)) ([idMor]Ty A)})

qq-idS : (X : ObS (suc n)) → qqS (idS n (ftS X)) X (id₁S n (ftS X)) ≡ idS (suc n) X
qq-idS {n = n} = //-elimP (λ {((Γ , A), (dΓ , dA)) → ap-irr2 (λ x z t → (proj (dmor ((Γ , x) , (dΓ , z)) ((Γ , A), (dΓ , dA)) (weakenMor' last (idMor n) , var last) t))) ([idMor]Ty A) {b = SubstTy dA (idMorDerivable dΓ)} {b' = dA} {c = (WeakMor (A [ idMor _ ]Ty) (idMorDerivable dΓ)) , (congTm (weaken[]Ty A (idMor n) last) refl (VarLast (congTy (! ([idMor]Ty _)) dA)))} {c' = (WeakMor A (idMorDerivable dΓ)) , (congTm (ap weakenTy (! ([idMor]Ty A)) ∙ weaken[]Ty A (idMor n) last) refl (VarLast dA))}})

star-compS-// : (g : DMor m k) (f : DMor n m) (X : DCtx (suc k)) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj g) ≡ ftS (proj X)) → starS (compS (proj g) (proj f) p) (proj X) (comp₁S (proj g) (proj f) p ∙ q) ≡ starS (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q))
star-compS-// (dmor Δd@(Δ , dΔ) Θd θ dθ) (dmor Γd@(Γ , dΓ) Δd'@(Δ' , dΔ') δ dδ) ((Γ' , A), (dΓ' , dA)) p q =  ap-irr (λ x z → proj ((Γ , x), z)) (! ([]Ty-assoc δ θ A))

star-compS : (g : MorS m k) (f : MorS n m) (X : ObS (suc k)) (p : ∂₁S f ≡ ∂₀S g) (q : ∂₁S g ≡ ftS X) → starS (compS g f p) X (comp₁S g f p ∙ q) ≡ starS f (starS g X q) (p ∙ ! (ft-starS g X q))
star-compS = //-elimP (λ g → //-elimP (λ f → //-elimP (star-compS-// g f)))


qq-compS-// : (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (X : DCtx (suc k)) (q : ∂₁S (proj g) ≡ ftS (proj X)) → qqS (compS (proj g) (proj f) p) (proj X) (comp₁S (proj g) (proj f) p ∙ q) ≡ compS (qqS (proj g) (proj X) q) (qqS (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q))) (qq₁S (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q)) ∙ ! (qq₀S (proj g) (proj X) q))
qq-compS-// (dmor Δd@(Δ , dΔ) Θd θ dθ) (dmor Γd@(Γ , dΓ) Δd'@(Δ' , dΔ') δ dδ) p ((Γ' , A), (dΓ' , dA)) q = eq (((CtxRefl dΓ ,, congTyRefl (SubstTy dA (SubstMor (ConvMor dθ (CtxSymm (reflect p)) (reflect q)) dδ)) (! ([]Ty-assoc δ θ A))) , (CtxRefl dΓ' ,, TyRefl dA)) , (congMorRefl (weaken[]Mor _ _ _ ∙ ! (weakenMorInsert _ _ _)) (WeakMor _ (SubstMor (ConvMor dθ (CtxSymm (reflect p)) (reflect q)) dδ)) , TmRefl (weakenDerLast dA (SubstMor (ConvMor dθ (CtxSymm (reflect p)) (reflect q)) dδ))))

qq-compS : (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) (X : ObS (suc k)) (q : ∂₁S g ≡ ftS X) → qqS (compS g f p) X (comp₁S g f p ∙ q) ≡ compS (qqS g X q) (qqS f (starS g X q) (p ∙ ! (ft-starS g X q))) (qq₁S f (starS g X q) (p ∙ ! (ft-starS g X q)) ∙ ! (qq₀S g X q))
qq-compS = //-elimP (λ g → //-elimP (λ f p → //-elimP λ X → qq-compS-// g f p X))


ss-ppS-// : {m n : ℕ} (f : DMor m (suc n)) → compS (ppS (starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f))))) (ssS (proj f)) (ss₁S (proj f) ∙ ! (pp₀S (starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))))) ≡ idS m (∂₀S (proj f))
ss-ppS-// (dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = eq (((CtxRefl dΓ) , (CtxRefl dΓ)) , MorSymm dΓ dΓ (congMorRefl (! (weakenMorInsert (idMor _) (idMor _) u ∙ idMor[]Mor (idMor _))) (idMorDerivable dΓ)))

ss-ppS : {m n : ℕ} (f : MorS m (suc n)) → compS (ppS (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f)))) (ssS f) (ss₁S f ∙ ! (pp₀S (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))))) ≡ idS m (∂₀S f)
ss-ppS {m} {n} = //-elimP (ss-ppS-// {m} {n})

ss-qqS-// : {m n : ℕ} (f : DMor m (suc n)) → (proj f) ≡ compS (qqS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))) (ssS (proj f)) (ss₁S (proj f) ∙ ! (qq₀S (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))))
ss-qqS-// (dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = eq ((CtxRefl dΓ , CtxRefl dΔ , dB , dB , (TyRefl dB) , (TyRefl dB)) , (congMorRefl (! (weakenMorInsert _ (idMor _) u ∙ [idMor]Mor _ ∙ weakenMorInsert _ δ u ∙ idMor[]Mor δ)) dδ) , (TmRefl du))

ss-qqS : {m n : ℕ} (f : MorS m (suc n)) → f ≡ compS (qqS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))) (ssS f) (ss₁S f ∙ ! (qq₀S (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))))
ss-qqS = //-elimP ss-qqS-//

ss-compS-// : {m n k : ℕ} (U : DCtx (suc k)) (g : DMor n k) (f : DMor m (suc n)) (g₁ : ∂₁S (proj g) ≡ ftS (proj U)) (f₁ : ∂₁S (proj f) ≡ starS (proj g) (proj U) g₁) {-g₀ : ∂₀ g ≡ ft (∂₁ f)-} → ssS (proj f) ≡ ssS (compS (qqS (proj g) (proj U) g₁) (proj f) (! (qq₀S (proj g) (proj U) g₁ ∙ ! f₁)))
ss-compS-// U@((Θ' , C), (dΘ' , dC)) g@(dmor (Δ' , dΔ') (Θ , dΘ) θ dθ) f@(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) g₁ f₁ =  eq (((CtxRefl dΓ) , CtxRefl dΓ , SubstTy dB dδ , TyEqTy1 dΓ (SubstTyMorEq dC (ConvMor (congMor refl refl (! (weakenMorInsert θ δ u)) (SubstMor dθ (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁))))) (CtxRefl dΓ) (reflect g₁)) (congMorRefl (weakenMorInsert θ δ u) (ConvMor (congMor refl refl (! (weakenMorInsert θ δ u)) (SubstMor dθ (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁))))) (CtxRefl dΓ) (reflect g₁)))) , TyTran (SubstTy (SubstTy (ConvTy dC (CtxSymm (reflect g₁))) dθ) (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁)))) (SubstTyEq (fst (snd (snd (snd (reflect f₁))))) dδ ) (congTyRefl (SubstTy (SubstTy dC (ConvMor dθ (CtxRefl dΔ') (reflect g₁))) (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁)))) ([]Ty-assoc δ θ C ∙ ap (λ z → C [ z ]Ty) (! (weakenMorInsert θ δ u)))) , TyTran (SubstTy (SubstTy (ConvTy dC (CtxSymm (reflect g₁))) dθ) (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁)))) (SubstTyEq (fst (snd (snd (snd (reflect f₁))))) dδ ) (congTyRefl (SubstTy (SubstTy dC (ConvMor dθ (CtxRefl dΔ') (reflect g₁))) (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁)))) ([]Ty-assoc δ θ C ∙ ap (λ z → C [ z ]Ty) (! (weakenMorInsert θ δ u))))) , congMorRefl refl (idMorDerivable dΓ) , congTmRefl (congTm (! ([idMor]Ty (B [ δ ]Ty))) refl du) refl)

ss-compS : {m n k : ℕ} (U : ObS (suc k)) (g : MorS n k) (f : MorS m (suc n)) (g₁ : ∂₁S g ≡ ftS U) (f₁ : ∂₁S f ≡ starS g U g₁) → ssS f ≡ ssS (compS (qqS g U g₁) f (! (qq₀S g U g₁ ∙ ! f₁)))
ss-compS = //-elimP (λ U → //-elimP (λ g → //-elimP (ss-compS-// U g)))

{- The syntactic contextual category -}

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
pt-unique synCCat = pt-uniqueS
ptmor synCCat = ptmorS
ptmor₀ synCCat {X = X} = ptmor₀S X
ptmor₁ synCCat {X = X} = ptmor₁S X
ptmor-unique synCCat = ptmor-uniqueS
id-right synCCat {f = f} = id-rightS f
id-left synCCat {f = f} = id-leftS f
assoc synCCat {h = h} {g = g} {f = f} {p = p} {q = q} = assocS h g f p q
ft-star synCCat {f = f} {X = X} {p = p} = ft-starS f X p
pp-qq synCCat {f = f} {X = X} {p = p} = pp-qqS f X p
star-id synCCat {X = X} = star-idS X
qq-id synCCat {X = X} = qq-idS X
star-comp synCCat {g = g} {f = f} {p = p} {X = X} q = star-compS g f X p q
qq-comp synCCat {g = g} {f} {p} {X} q = qq-compS g f p X q
ss-pp synCCat {f = f} = ss-ppS f
ss-qq synCCat {f = f} = ss-qqS f
ss-comp synCCat {U = U} {g = g} {g₁ = g₁} {f = f} {f₁ = f₁} = ss-compS U g f g₁ f₁


{- The syntactic structured contextual category -}

open StructuredCCat

is-sectionS : (u : MorS n (suc n)) → Prop
is-sectionS u = compS (ppS (∂₁S u)) u (! (pp₀S (∂₁S u))) ≡ idS _ (∂₀S u)

sectionS-eq : {Γ Δ : Ctx n} {dΓ : ⊢ Γ} {A : TyExpr n} {dΔ : ⊢ Δ} {dA : Derivable (Δ ⊢ A)} {δ : Mor n n} {dδ : Γ ⊢ δ ∷> Δ} {u : TmExpr n} {du : Derivable (Γ ⊢ u :> A [ δ ]Ty)}
            → is-sectionS (proj (dmor (Γ , dΓ) ((Δ , A), (dΔ , dA)) (δ , u) (dδ , du)))
            → Γ ⊢ δ == idMor n ∷> Δ
sectionS-eq us with reflect us
... | ((_ , dΔ=) , dδ=) = congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor _) refl dδ=

sectionS-eq-ctx : {Γ Δ : Ctx n} {dΓ : ⊢ Γ} {A : TyExpr n} {dΔ : ⊢ Δ} {dA : Derivable (Δ ⊢ A)} {δ : Mor n n} {dδ : Γ ⊢ δ ∷> Δ} {u : TmExpr n} {du : Derivable (Γ ⊢ u :> A [ δ ]Ty)}
            → is-sectionS (proj (dmor (Γ , dΓ) ((Δ , A), (dΔ , dA)) (δ , u) (dδ , du)))
            → ⊢ Δ == Γ
sectionS-eq-ctx us with reflect us
... | ((_ , dΔ=) , dδ=) = dΔ=

is-section₀S : {u : MorS n (suc n)} (us : is-sectionS u) → ∂₀S u ≡ ftS (∂₁S u)
is-section₀S {u = u} us = ! (id₁S _ (∂₀S u)) ∙ ap ∂₁S (! us) ∙ comp₁S (ppS (∂₁S u)) u (! (pp₀S _)) ∙ pp₁S (∂₁S u)

PiStrS-//  : (X : DCtx (suc (suc n))) → ObS (suc n)
PiStrS-// (((Γ , A) , B), ((dΓ , dA) , dB)) = proj ((Γ , pi A B) , (dΓ , Pi dA dB))

PiStrS-eq : {Γ Γ' : DCtx (suc (suc n))} → ⊢ ctx Γ == ctx Γ' → PiStrS-// Γ ≡ PiStrS-// Γ'
PiStrS-eq {Γ  = (((Γ  , A)  , B),  ((dΓ  , dA)  , dB))}
          {Γ' = (((Γ' , A') , B'), ((dΓ' , dA') , dB'))}
          ((dΓ= , dA , dA' , dA= , dA=') , (dB , dB' , dB= , dB='))
          = eq (dΓ= , Pi dA dB , Pi dA' dB' , PiCong dA dA= dB= , PiCong (ConvTy dA dΓ=) dA=' (ConvTyEq dB=' (CtxSymm (CtxRefl dΓ' , ConvTy dA dΓ= , dA' , dA=' , dA='))))

PiStrS : (B : ObS (suc (suc n))) → ObS (suc n)
PiStrS = //-rec PiStrS-// PiStrS-eq


PiStr=S-// : (Γ : DCtx (suc (suc n))) → ftS (PiStrS-// Γ) ≡ ftS (ftS (proj Γ))
PiStr=S-// (((Γ  , A)  , B),  ((dΓ  , dA)  , dB)) = refl

PiStr=S : (B : ObS (suc (suc n))) → ftS (PiStrS B) ≡ ftS (ftS B)
PiStr=S = //-elimP PiStr=S-//


lamStrS-//-der-type : (u : DMor (suc n) (suc (suc n))) (us : is-sectionS (proj u)) → Prop
lamStrS-//-der-type (dmor (Δ , dΔ) (((Γ , A) , B) , ((dΓ , dA) , dB)) ((δ , v) , u) ((dδ , dv) , du)) us = Γ ⊢ (idMor _ , lam A B u) ∷> (Γ , pi A B)

lamStrS-//-der : (u : DMor (suc n) (suc (suc n))) (us : is-sectionS (proj u)) → lamStrS-//-der-type u us
lamStrS-//-der (dmor (Δ , dΔ) (((Γ , A) , B) , ((dΓ , dA) , dB)) ((δ , v) , u) ((dδ , dv) , du)) us with reflect us
... | ((_ , dΔ=) , dδ= , dv=) rewrite [idMor]Ty A | [idMor]Ty B
  = (idMorDerivable dΓ , Lam dA dB (ConvTm (Conv (SubstTy dB (dδ , dv)) du (congTyEq refl ([idMor]Ty B) (SubstTyMorEq dB (dδ , dv) (sectionS-eq {dA = dB} {dδ = (dδ , dv)} {du = du} us)))) (CtxSymm dΔ=)))

lamStrS-// : (u : DMor (suc n) (suc (suc n))) (us : is-sectionS (proj u)) → MorS n (suc n)
lamStrS-// uu@(dmor (Δ , dΔ) (((Γ , A) , B) , ((dΓ , dA) , dB)) ((δ , v) , u) ((dδ , dv) , du)) us =
  proj (dmor (Γ , dΓ) ((Γ , pi A B), (dΓ , Pi dA dB)) (idMor _ , lam A B u) (lamStrS-//-der uu us))

lamStrS-eq : {u u' : DMor (suc n) (suc (suc n))} (u~u' : u ≃ u') (us : is-sectionS (proj u)) (us' : is-sectionS (proj u')) → lamStrS-// u us ≡ lamStrS-// u' us'
lamStrS-eq {u = (dmor (Δ , dΔ) (((Γ , A) , B) , ((dΓ , dA) , dB)) ((δ , v) , u) ((dδ , dv) , du))}
           {u' = (dmor (Δ' , dΔ') (((Γ' , A') , B') , ((dΓ' , dA') , dB')) ((δ' , v') , u') ((dδ' , dv') , du'))}
           ((dΔ= , (dΓ= , dA , dA' , dA= , dA='), dB , dB' , dB= , dB='), (dδ= , dv=), du=) us us'
           = eq ((dΓ= , dΓ= , Pi dA dB , Pi dA' dB' , PiCong dA dA= dB= , ConvTyEq (PiCong dA dA= dB=) dΓ=) , MorRefl (idMorDerivable dΓ) , ConvEq (Pi dA dB) (LamCong dA dA= dB= (congTmEqTy ([idMor]Ty B) (ConvTmEq (ConvEq (SubstTy dB (dδ , dv)) du= (SubstTyMorEq dB (dδ , dv) (sectionS-eq {dA = dB} {dδ = (dδ , dv)} {du = du} us))) (CtxSymm (sectionS-eq-ctx {dA = dB} {dδ = (dδ , dv)} {du = du} us))))) (congTyRefl (Pi dA dB) (! ([idMor]Ty (pi A B)))))

lamStrS : (u : MorS (suc n) (suc (suc n))) (us : is-sectionS u) → MorS n (suc n)
lamStrS = //-elim-PiP lamStrS-// lamStrS-eq


lamStrsS-// : (u : DMor (suc n) (suc (suc n))) (us : is-sectionS (proj u)) → is-sectionS (lamStrS-// u us)
lamStrsS-// (dmor (Δ , dΔ) (((Γ , A) , B) , ((dΓ , dA) , dB)) ((δ , v) , u) ((dδ , dv) , du)) us = eq ((CtxRefl dΓ , CtxRefl dΓ) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor _)) refl (MorRefl (idMorDerivable dΓ)))

lamStrsS : (u : MorS (suc n) (suc (suc n))) (us : is-sectionS u) → is-sectionS (lamStrS u us)
lamStrsS = //-elimP lamStrsS-//


lamStr₁S-// : (u : DMor (suc n) (suc (suc n))) (us : is-sectionS (proj u)) → ∂₁S (lamStrS-// u us) ≡ PiStrS (proj (rhs u))
lamStr₁S-// (dmor (Δ , dΔ) (((Γ , A) , B) , ((dΓ , dA) , dB)) ((δ , v) , u) ((dδ , dv) , du)) us = refl

lamStr₁S : (u : MorS (suc n) (suc (suc n))) (us : is-sectionS u) → ∂₁S (lamStrS u us) ≡ PiStrS (∂₁S u)
lamStr₁S = //-elimP lamStr₁S-//


appStrS-// : (B : DCtx (suc (suc n))) (f : DMor n (suc n)) (fs : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor n (suc n)) (as : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) → MorS n (suc n)
appStrS-// (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γf' , Af) , (dΓf' , dAf)) (δf , f) (dδf , df~)) fs f₁ aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) as a₁ =
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
  in
  proj (dmor (Γ , dΓ)
             ((Γ , B [ idMor _ , a ]Ty) , (dΓ , SubstTy dB (idMorDerivable dΓ , da[])))
             (idMor _ , app A B f a)
             (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl (App dA dB df da)))

appStr-eq : (B B' : DCtx (suc (suc n))) (rB : B ≃ B') (f f' : DMor n (suc n)) (rf : f ≃ f') (fs : is-sectionS (proj f)) (fs' : is-sectionS (proj f')) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (f₁' : ∂₁S (proj f') ≡ PiStrS (proj B')) (a a' : DMor n (suc n)) (ra : a ≃ a') (as : is-sectionS (proj a)) (as' : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (a₁' : ∂₁S (proj a') ≡ ftS (proj B')) → appStrS-// B f fs f₁ a as a₁ ≡ appStrS-// B' f' fs' f₁' a' as' a₁'
appStr-eq (((Γ , A) , B), ((dΓ , dA) , dB))
          (((Γ+ , A+) , B+), ((dΓ+ , dA+) , dB+))
          rB@((dΓ= , _ , _ , dA= , _) , _ , _ , dB= , _)
          (dmor (Γf , dΓf) ((Γf' , Af) , (dΓf' , dAf)) (δf , f) (dδf , df~))
          (dmor (Γf+ , dΓf+) ((Γf'+ , Af+) , (dΓf'+ , dAf+)) (δf+ , f+) (dδf+ , df~+))
          rf@(_ , _ , df=~)
          fs fs' f₁ f₁'
          (dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~))
          (dmor (Γa+ , dΓa+) ((Γa'+ , Aa+) , (dΓa'+ , dAa+)) (δa+ , a+) (dδa+ , da~+))
          ra@(_ , _ , da=~)
          as as' a₁ a₁' =
  let (dΓa'= , _ , _ , dAa= , _) = reflect a₁
      (dΓf'= , _ , _ , dAf= , _) = reflect f₁

      da=[] : Derivable (Γ ⊢ a == a+ :> A [ idMor _ ]Ty)
      da=[] = ConvTmEq2 da=~ (CtxTran (CtxSymm (sectionS-eq-ctx {dA = dAa} {dδ = dδa} {du = da~} as)) dΓa'=) (SubstTyMorEq2 dΓa dΓa' dAa= (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} as))

      da= : Derivable (Γ ⊢ a == a+ :> A)
      da= = congTmEqTy ([idMor]Ty A) da=[]

      dΓf= = sectionS-eq-ctx {dA = dAf} {dδ = dδf} {du = df~} fs

      df= : Derivable (Γ ⊢ f == f+ :> pi A B)
      df= = ConvTmEq2 df=~ (CtxTran (CtxSymm (sectionS-eq-ctx {dA = dAf} {dδ = dδf} {du = df~} fs)) dΓf'=) (TyTran (SubstTy dAf (eqMorDer dΓf=)) (SubstTyMorEq dAf dδf (sectionS-eq {dA = dAf} {dδ = dδf} {du = df~} fs)) (ConvTyEq (congTyEq (! ([idMor]Ty _)) refl dAf=) dΓf=))
  in
  eq ((dΓ= , (dΓ= ,, SubstTyMorEq2 dΓ (dΓ , dA) dB= ((MorRefl (idMorDerivable dΓ)) , da=[]))) , MorRefl (idMorDerivable dΓ) , congTmEqTy (! ([idMor]Ty _)) (AppCong dA dA= dB= df= da=))

appStrS : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fs : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) → MorS n (suc n)
appStrS =
  //-elim-PiS (λ B → //-elim-PiP2 (λ f fs f₁ → //-elim-PiP2 (appStrS-// B f fs f₁)
    (λ ra as as' → PathOver-Prop→Cst (λ a₁ a₁' → appStr-eq B B (ref B) f f (ref f) fs fs f₁ f₁ _ _ ra as as' a₁ a₁')))
    (λ rf fs fs' → PathOver-Prop→Cst (λ f₁ f₁' → funext (//-elimP (λ a → funextP (λ as → funextP (λ a₁ → appStr-eq B B (ref B) _ _ rf fs fs' f₁ f₁' a a (ref a) as as a₁ a₁)))))))
    (λ rB → //-elimP λ f → PathOver-CstPropPi (λ fs → PathOver-Prop→ (λ f₁ f₁' → PathOver-CstPi (//-elimP (λ a → PathOver-CstPropPi (λ as → PathOver-Prop→Cst (λ a₁ a₁' → appStr-eq _ _ rB f f (ref f) fs fs f₁ f₁' a a (ref a) as as a₁ a₁')))))))

appStrsS-// : (B : DCtx (suc (suc n))) (f : DMor n (suc n)) (fs : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor n (suc n)) (as : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) → is-sectionS (appStrS (proj B) (proj f) fs f₁ (proj a) as a₁)
appStrsS-// (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γf' , Af) , (dΓf' , dAf)) (δf , f) (dδf , df~)) fs f₁ aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) as a₁
  = eq ((CtxRefl dΓ , CtxRefl dΓ) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ idMor[]Mor _)) refl (MorRefl (idMorDerivable dΓ)))

appStrsS : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fs : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) → is-sectionS (appStrS B f fs f₁ a as a₁)
appStrsS = //-elimP (λ B → //-elimP (λ f fs f₁ → //-elimP (appStrsS-// B f fs f₁)))

appStr₁S-// : (B : DCtx (suc (suc n))) (f : DMor n (suc n)) (fs : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor n (suc n)) (as : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) → ∂₁S (appStrS (proj B) (proj f) fs f₁ (proj a) as a₁) ≡ starS (proj a) (proj B) a₁
appStr₁S-// (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γf' , Af) , (dΓf' , dAf)) (δf , f) (dδf , df~)) fs f₁ aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) as a₁
  = let (dΓ= , _ , _ , daTy= , _) = reflect a₁

        dΓ=' = CtxTran (CtxSymm dΓ=) (sectionS-eq-ctx {dA = dAa} {dδ = dδa} {du = da~} as)

        da[] : Derivable (Γ ⊢ a :> A [ idMor _ ]Ty)
        da[] = ConvTm2 da~ (CtxSymm dΓ=') (SubstTyMorEq2 dΓa dΓa' daTy= (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} as))

    in eq (dΓ=' ,, SubstTyMorEq dB (idMorDerivable dΓ , da[]) ((ConvMorEq (MorSymm dΓa dΓa' (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} as)) (CtxSymm dΓ=') dΓ=) , TmRefl da[]))

appStr₁S : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fs : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) → ∂₁S (appStrS B f fs f₁ a as a₁) ≡ starS a B a₁
appStr₁S = //-elimP (λ B → //-elimP (λ f fs f₁ → //-elimP (appStr₁S-// B f fs f₁)))


UUStrS-// : DCtx n → ObS (suc n)
UUStrS-// (Γ , dΓ) = proj ((Γ , uu) , (dΓ , UU))

UUStrS-eq : {Γ Γ' : DCtx n} → ⊢ ctx Γ == ctx Γ' → UUStrS-// Γ ≡ UUStrS-// Γ'
UUStrS-eq dΓ= = eq (dΓ= , UU , UU , UUCong , UUCong)

UUStrS : ObS n → ObS (suc n)
UUStrS = //-rec UUStrS-// (λ {a} {b} r → UUStrS-eq {Γ = a} {Γ' = b} r)


UUStr=S : (X : ObS n) → ftS (UUStrS X) ≡ X
UUStr=S = //-elimP (λ _ → refl)


ElStrS-// : (u : DMor n (suc n)) (us : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ UUStrS (∂₀S (proj u))) → ObS (suc n)
ElStrS-// (dmor (Γ , dΓ) ((_ , u) , (_ , du)) (δ , v) (dδ , dv)) us u₁ =
  let (_ , _ , _ , du= , _) = reflect u₁
      dv = Conv (SubstTy du dδ) dv (SubstTyEq du= dδ)
  in proj ((Γ , el v) , (dΓ , El dv))

ElStrS-eq : (u u' : DMor n (suc n)) (r : u ≃ u') (us : is-sectionS (proj u)) (us' : is-sectionS (proj u')) (u₁ : ∂₁S (proj u) ≡ UUStrS (∂₀S (proj u))) (u₁' : ∂₁S (proj u') ≡ UUStrS (∂₀S (proj u'))) → ElStrS-// u us u₁ ≡ ElStrS-// u' us' u₁'
ElStrS-eq (dmor (Γ , dΓ) ((_ , u) , (_ , du)) (δ , v) (dδ , dv~)) (dmor (Γ' , dΓ') ((_ , u') , (_ , du')) (δ' , v') (dδ' , dv~')) ((dΓ= , _ , _ , _ , _ , _), dδ= , dv=~) us us' u₁ u₁' =
  let (_ , _ , _ , du= , _) = reflect u₁ in
  let (_ , _ , _ , du=' , _) = reflect u₁' in
  let dv : Derivable (Γ ⊢ v :> uu)
      dv = Conv (SubstTy du dδ) dv~ (SubstTyEq du= dδ)
  in
  let dv' : Derivable (Γ' ⊢ v' :> uu)
      dv' = Conv (SubstTy du' dδ') dv~' (SubstTyEq du=' dδ')
  in
  let dv= : Derivable (Γ ⊢ v == v' :> uu)
      dv= = ConvEq (SubstTy du dδ) dv=~ (SubstTyEq du= dδ)
  in
  let dv=' : Derivable (Γ' ⊢ v == v' :> uu)
      dv=' = ConvTmEq dv= dΓ=
  in
  eq (dΓ= , El dv , El dv' , ElCong dv= , ElCong dv=')

ElStrS : (u : MorS n (suc n)) (us : is-sectionS u) (u₁ : ∂₁S u ≡ UUStrS (∂₀S u)) → ObS (suc n)
ElStrS = //-elim-PiP2 ElStrS-// (λ r us us' → PathOver-Prop→Cst (ElStrS-eq _ _ r us us'))


ElStr=S-// : (u : DMor n (suc n)) (us : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ UUStrS (∂₀S (proj u))) → ftS (ElStrS (proj u) us u₁) ≡ ∂₀S (proj u)
ElStr=S-// (dmor (Γ , dΓ) ((_ , u) , (_ , du)) (δ , v) (dδ , dv~)) us u₁ = refl

ElStr=S : (u : MorS n (suc n)) (us : is-sectionS u) (u₁ : ∂₁S u ≡ UUStrS (∂₀S u)) → ftS (ElStrS u us u₁) ≡ ∂₀S u
ElStr=S = //-elimP ElStr=S-//

PiStrNatS-// : (g : DMor n m) (B : DCtx (suc (suc m))) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g)) → starS (proj g) (PiStrS (proj B)) (! (PiStr=S (proj B) ∙ p)) ≡ PiStrS (starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p)))
PiStrNatS-// (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (((_ , A) , B), ((_ , dA) , dB)) p = refl

PiStrNatS : (g : MorS n m) (B : ObS (suc (suc m))) (p : ftS (ftS B) ≡ ∂₁S g) → starS g (PiStrS B) (! (PiStr=S B ∙ p)) ≡ PiStrS (starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p)))
PiStrNatS = //-elimP (λ g → //-elimP (PiStrNatS-// g))

lamStr₀S : (u : MorS (suc n) (suc (suc n))) (us : is-sectionS u) → ∂₀S (lamStrS u us) ≡ ftS (∂₀S u)
lamStr₀S u us = is-section₀S (lamStrsS u us) ∙ ap ftS (lamStr₁S u us) ∙ PiStr=S (∂₁S u) ∙ ap ftS (! (is-section₀S us)) 


ss-is-sectionS : (f : MorS m (suc n)) → is-sectionS (ssS f)
ss-is-sectionS f = ap2-irr compS (ap ppS (ss₁S f)) refl ∙ (ss-ppS f) ∙ ap (idS _) (! (ss₀S f))

ss-comp-section₁S : {m n : ℕ} (g : MorS m n) (f : MorS n (suc n)) (fs : is-sectionS f) (p : ∂₁S g ≡ ∂₀S f) → ∂₁S (ssS (compS f g p)) ≡ starS g (∂₁S f) (p ∙ is-section₀S fs)
ss-comp-section₁S {m} {n} g f fs p = ss₁S (compS f g p) ∙ ap2-irr starS (! (assocS (ppS (∂₁S (compS f g p))) f g p (! (pp₀S (∂₁S (compS f g p)) ∙ (comp₁S f g p)))) ∙ ap2-irr compS (ap2-irr compS (ap ppS (comp₁S f g p)) refl ∙ fs ∙ ap (idS _) (! p)) refl ∙ (id-rightS g) ) (comp₁S f g p)



CtxSubstRefl : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} {A : TyExpr m} → (⊢ Γ) → (Γ ⊢ δ ∷> Δ) → Derivable (Δ ⊢ A) → ⊢ (Γ , A [ δ ]Ty) == (Γ , A [ δ ]Ty)
CtxSubstRefl dΓ dδ dA = (CtxRefl dΓ ,, TyRefl (SubstTy dA dδ))

WeakSubstTmEq : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} {A : TyExpr m} {B : TyExpr (suc m)} {u v : TmExpr (suc m)} → (⊢ Γ) → Derivable (Δ ⊢ A) →  Derivable ((Δ , A) ⊢ u == v :> B) → (Γ ⊢ δ ∷> Δ) → Derivable ((Γ , A [ δ ]Ty) ⊢ u [ (weakenMor δ , var last) ]Tm == v [ (weakenMor δ , var last) ]Tm :> B [ (weakenMor δ , var last)  ]Ty)
WeakSubstTmEq {δ = δ} {A = A} dΓ dA du=v dδ = ConvTmEq (SubstTmEq du=v ((WeakMor (A [ δ ]Ty) dδ) , weakenDerLast dA dδ)) (CtxSubstRefl dΓ dδ dA)


lamStrNatS-// : (g : DMor n m) (u : DMor (suc m) (suc (suc m))) (us : is-sectionS (proj u)) (p : ftS (∂₀S (proj u)) ≡ ∂₁S (proj g))
              →  ssS (compS (lamStrS (proj u) us) (proj g) (! (lamStr₀S (proj u) us ∙ p))) ≡ lamStrS (ssS (compS (proj u) (qqS (proj g) (∂₀S (proj u)) (! p)) (qq₁S (proj g) (∂₀S (proj u)) (! p )))) (ss-is-sectionS (compS (proj u) (qqS (proj g) (∂₀S (proj u)) (! p)) (qq₁S (proj g) (∂₀S (proj u)) (! p ))))
lamStrNatS-// (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (dmor ((Δ' , A) , (dΔ' , dA)) (((Δ'' , A') , B) , ((dΔ'' , dA') , dB)) ((θ , a) , u) ((dθ , da) , du)) us p =
              let dΔ'=Δ = reflect p
                  ((Δ'refl , (dΔ''=Δ' , _ , _ , _ , dΔ'A'=A)) , (dθ=wid , da=lastA')) = reflect us

                  wwθ=θ : weakenMor (weakenMor (idMor _)) [ (θ , a) , u ]Mor ≡ θ
                  wwθ=θ = (weakenMorInsert (weakenMor (idMor _)) (θ , a ) u) ∙ (weakenMorInsert (idMor _) θ a) ∙ (idMor[]Mor θ)
                  
                  dδΔ' : Γ ⊢ δ ∷> Δ'
                  dδΔ' = ConvMor dδ (CtxRefl dΓ) (CtxSymm (dΔ'=Δ))

                  dA'Δ' : Derivable (Δ' ⊢ A')
                  dA'Δ' = ConvTy dA' dΔ''=Δ'

                  dBΔ' : Derivable ((Δ' , A) ⊢ B)
                  dBΔ' = ConvTy dB (dΔ''=Δ' ,, (ConvTyEq dΔ'A'=A (CtxSymm dΔ''=Δ')))

                  dθΔ' : (Δ' , A) ⊢ θ ∷> Δ'
                  dθΔ' = ConvMor dθ Δ'refl dΔ''=Δ'
                  
                  dθ=widΔ' : (Δ' , A) ⊢ θ == weakenMor (idMor _) ∷> Δ'
                  dθ=widΔ' = ConvMorEq (congMorEq refl refl wwθ=θ refl dθ=wid) Δ'refl dΔ''=Δ'

                  wwθ : (Δ' , A) ⊢ weakenMor' last (weakenMor' last (idMor _)) [ (θ , a) , u ]Mor ∷> Δ'
                  wwθ = congMor refl refl (! wwθ=θ) dθΔ'

                  da=lastA : Derivable ((Δ' , A) ⊢ a == var last :> A [ weakenMor (idMor _) ]Ty )
                  da=lastA = ConvEq (SubstTy dA'Δ' wwθ) da=lastA' (SubstTyFullEq dA wwθ dΔ'A'=A (congMorEq refl refl (! wwθ=θ) refl dθ=widΔ'))
                  
                  dBθa : Derivable ((Δ' , A) ⊢ B [ θ , a ]Ty == B)
                  dBθa = TySymm (congTyEq ([idMor]Ty B) refl (SubstTyMorEq dBΔ' ((WeakMor _ (idMorDerivable dΔ')) , (ConvTm (weakenDerLast dA (idMorDerivable dΔ')) (CtxRefl dΔ' ,, TySymm (congTyRefl dA (! ([idMor]Ty A)))))) (MorSymm (dΔ' , dA) dΔ' dθ=widΔ' , TmSymm (da=lastA))))
                  
              in
              ! (eq ((CtxRefl dΓ , (CtxRefl dΓ ,, congTyEq (ap (pi (A [ δ ]Ty)) ([]Ty-assoc _ (θ , a) B)) (ap (λ z → pi (A' [ z ]Ty)  (B [ weakenMor z , var last ]Ty)) (! (idMor[]Mor δ))) (SubstTyEq (PiCong dA (TySymm dΔ'A'=A) dBθa) dδΔ'))) , (MorRefl (idMorDerivable dΓ)) , congTmEqTy (! ([idMor]Ty _ ∙ ap (pi (A [ δ ]Ty)) (! ([]Ty-assoc _ (θ , a) B)))) (congTmEqTm (ap (λ z → lam (A [ δ ]Ty) z _) ([]Ty-assoc _ (θ , a) B)) refl (SubstTmEq (LamCong dA (TySymm dΔ'A'=A) dBθa (TmRefl du)) dδΔ'))))



lamStrNatS : (g : MorS n m) (u : MorS (suc m) (suc (suc m))) (us : is-sectionS u) (p : ftS (∂₀S u) ≡ ∂₁S g)
           → ssS (compS (lamStrS u us) g (! (lamStr₀S u us ∙ p))) ≡ lamStrS (ssS (compS u (qqS g (∂₀S u) (! p)) (qq₁S g (∂₀S u) (! p )))) (ss-is-sectionS (compS u (qqS g (∂₀S u) (! p)) (qq₁S g (∂₀S u) (! p ))))
lamStrNatS = //-elimP (λ g → //-elimP (λ u → lamStrNatS-// g u))


appStr₀S : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fs : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) → ∂₀S (appStrS B f fs f₁ a as a₁) ≡ ftS (ftS B)
appStr₀S B f fs f₁ a as a₁ = is-section₀S (appStrsS B f fs f₁ a as a₁) ∙ ap ftS (appStr₁S B f fs f₁ a as a₁) ∙ (ft-starS a B a₁) ∙ is-section₀S as ∙ ap ftS a₁

appStrNatS-// : (g : DMor n m) (B : DCtx (suc (suc m))) (f : DMor m (suc m)) (fs : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor m (suc m)) (as : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))  → ssS (compS (appStrS (proj B) (proj f) fs f₁ (proj a) as a₁) (proj g) (! (appStr₀S (proj B) (proj f) fs f₁ (proj a) as a₁ ∙ p))) ≡ appStrS (starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p))) (ssS (compS (proj f) (proj g) (! (is-section₀S {u = proj f} fs ∙ ap ftS f₁ ∙ (PiStr=S (proj B)) ∙ p)))) (ss-is-sectionS (compS (proj f) (proj g) (! (is-section₀S {u = proj f} fs ∙ ap ftS f₁ ∙ (PiStr=S (proj B)) ∙ p)))) (ss-comp-section₁S (proj g) (proj f) fs (! (is-section₀S {u = proj f} fs ∙ ap ftS f₁ ∙ (PiStr=S (proj B)) ∙ p)) ∙  ap2-irr starS {a = (proj g)} refl f₁ {b = ! (is-section₀S {u = proj f} fs ∙ ap ftS f₁ ∙ PiStr=S (proj B) ∙ p) ∙ is-section₀S {u = proj f} fs} ∙ (PiStrNatS (proj g) (proj B) p)) (ssS (compS (proj a) (proj g) (! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p)))) (ss-is-sectionS (compS (proj a) (proj g) (! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p)))) (ss-comp-section₁S (proj g) (proj a) as (! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p)) ∙ ! (ft-starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p)) ∙ qq₀S (proj g) (ftS (proj B)) (! p) ∙ ap2-irr starS {a = (proj g)} refl (! a₁) {b = ! p} {b' = ! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p) ∙ is-section₀S {u = proj a} as}))
appStrNatS-// gg@(dmor (Δ , dΔ) (Γg , dΓg) δg dδg) (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γf' , piABf) , (dΓf' , dpiABf)) (δf , f) (dδf , df~)) fs f₁ aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) as a₁ p =
                            let ((_ , dΓf'=Γf) , dδf=id) = reflect fs
                                (dΓf'=Γ , _ , _ , dΓf'piABf=piAB , dΓpiABf=piAB) = reflect f₁
                                ((_ , dΓa'=Γa) , dδa=id) = reflect as
                                (dΓa'=Γ , _ , _ , dΓ'Aa=A , dΓAa=A) = reflect a₁
                                dΓ=Γg = reflect p

                                dδaΓ : Γa ⊢ δa ∷> Γ
                                dδaΓ = ConvMor dδa (CtxRefl dΓa) dΓa'=Γ
                                
                                dδa=idΓ : Γa ⊢ δa == idMor _ ∷> Γ
                                dδa=idΓ = ConvMorEq (congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor δa) refl dδa=id) (CtxRefl dΓa) dΓa'=Γ
                                dδf=idΓf' : Γf' ⊢ δf == idMor _ ∷> Γf'
                                dδf=idΓf' = ConvMorEq (congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor δf) refl dδf=id) (CtxSymm dΓf'=Γf) (CtxRefl dΓf')
                                                               
                                da[] : Derivable (Γ ⊢ a :> A [ idMor _ ]Ty)
                                da[] = ConvTm2 da~ (CtxTran (CtxSymm dΓa'=Γa) dΓa'=Γ) (SubstTyFullEq dA dδaΓ dΓAa=A dδa=idΓ)

                                dδgΓ : Δ ⊢ δg ∷> Γ
                                dδgΓ = ConvMor dδg (CtxRefl dΔ) (CtxSymm dΓ=Γg)
                                dAΓg : Derivable (Γg ⊢ A)
                                dAΓg = ConvTy dA dΓ=Γg
                                dBΓg : Derivable ((Γg , A) ⊢ B)
                                dBΓg = ConvTy dB (dΓ=Γg ,, (TyRefl dA))
                                dfΓg : Derivable (Γg ⊢ f :> pi A B)
                                dfΓg = ConvTm2 df~ (CtxTran (CtxSymm dΓf'=Γf) (CtxTran dΓf'=Γ dΓ=Γg)) (ConvTyEq (congTyEq refl ([idMor]Ty (pi A B)) (SubstTyFullEq (Pi (ConvTy dA (CtxSymm dΓf'=Γ)) (ConvTy dB (CtxSymm dΓf'=Γ ,, TyRefl dA))) (ConvMor dδf (CtxSymm dΓf'=Γf) (CtxRefl dΓf')) dΓf'piABf=piAB dδf=idΓf')) dΓf'=Γf)
                                daΓg : Derivable (Γg ⊢ a :> A)
                                daΓg = ConvTm2 da[] dΓ=Γg (TySymm (congTyRefl dA (! ([idMor]Ty A))))
                            in
                            eq ((CtxRefl dΔ , (CtxRefl dΔ ,, congTyRefl (SubstTy (SubstTy dB ((idMorDerivable dΓ) , da[])) (SubstMor (idMorDerivable dΓ) (ConvMor dδg (CtxRefl dΔ) (CtxSymm dΓ=Γg)))) ([]Ty-assoc _ _ B ∙ ! ([]Ty-assoc _ _ B ∙ ap (_[_]Ty B) (ap (λ z → (z , a [ δg ]Tm)) {b = idMor _ [ idMor _ [ δg ]Mor ]Mor} (weakenMorInsert _ _ (a [ δg ]Tm) ∙ [idMor]Mor δg ∙ ! (idMor[]Mor _ ∙ idMor[]Mor δg)) ∙ ap (λ z → (_ , z)) (ap (_[_]Tm a) (! (idMor[]Mor δg)))))))) , ((MorRefl (idMorDerivable dΔ)) , TmRefl (Conv (SubstTy (SubstTy dB ((idMorDerivable dΓ) , da[])) dδgΓ) (SubstTm (App {f = f} {a = a} dAΓg dBΓg dfΓg daΓg) dδg) (congTyRefl (SubstTy (SubstTy dB ((idMorDerivable dΓ) , da[])) dδgΓ) (! ([idMor]Ty _ ∙ ap (_[_]Ty _) (idMor[]Mor δg)))))))


appStrNatS : (g : MorS n m) (B : ObS (suc (suc m))) (f : MorS m (suc m)) (fs : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS m (suc m)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) (p : ftS (ftS B) ≡ ∂₁S g)              → ssS (compS (appStrS B f fs f₁ a as a₁) g (! (appStr₀S B f fs f₁ a as a₁ ∙ p))) ≡ appStrS (starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p))) (ssS (compS f g (! (is-section₀S fs ∙ ap ftS f₁ ∙ (PiStr=S B) ∙ p)))) (ss-is-sectionS (compS f g (! (is-section₀S fs ∙ ap ftS f₁ ∙ (PiStr=S B) ∙ p)))) (ss-comp-section₁S g f fs (! (is-section₀S fs ∙ ap ftS f₁ ∙ (PiStr=S B) ∙ p)) ∙ ap2-irr starS {a = g} refl f₁  ∙ (PiStrNatS g B p)) (ssS (compS a g (! (is-section₀S as ∙ ap ftS a₁ ∙ p)))) (ss-is-sectionS (compS a g (! (is-section₀S as ∙ ap ftS a₁ ∙ p)))) (ss-comp-section₁S g a as (! (is-section₀S as ∙ ap ftS a₁ ∙ p)) ∙ ! (ft-starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p)) ∙ qq₀S g (ftS B) (! p) ∙ ap2-irr starS {a = g} refl (! a₁)))
appStrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ f fs f₁ → //-elimP (λ a as a₁ → appStrNatS-// g B f fs f₁ a as a₁))))


UUStrNatS-// : (g : DMor n m) (X : DCtx m) (p : proj X ≡ ∂₁S (proj g)) → starS (proj g) (UUStrS (proj X)) (! p ∙ ! (UUStr=S (proj X))) ≡ UUStrS (∂₀S (proj g))
UUStrNatS-// (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (_ , _) p = refl

UUStrNatS : (g : MorS n m) (X : ObS m) (p : X ≡ ∂₁S g) → starS g (UUStrS X) (! p ∙ ! (UUStr=S X)) ≡ UUStrS (∂₀S g)
UUStrNatS = //-elimP (λ g → //-elimP (UUStrNatS-// g))


ElStrNatS-// :  (g : DMor n m) (v : DMor m (suc m)) (vs : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ UUStrS (∂₀S (proj v))) (p : ∂₀S (proj v) ≡ ∂₁S (proj g)) → starS (proj g) (ElStrS (proj v) vs v₁) (! p ∙ ! (ElStr=S (proj v) vs v₁)) ≡ ElStrS (ssS (compS (proj v) (proj g) (! p))) (ss-is-sectionS (compS (proj v) (proj g) (! p))) (ss-comp-section₁S (proj g) (proj v) vs (! p) ∙  ap2-irr starS {a = (proj g)} refl v₁ {b = ! p ∙ (is-section₀S {u = proj v} vs)} {b' = (! p ∙ ! (UUStr=S (∂₀S (proj v))))} ∙ UUStrNatS (proj g) (∂₀S (proj v)) p ∙ ap UUStrS (! (ss₀S (compS (proj v) (proj g) (! p)) ∙ (comp₀S (proj v) (proj g) (! p)))))
ElStrNatS-// (dmor (Θ , dΘ) (Γ' , dΓ') θ dθ) (dmor (Γ , dΓ) ((Δ , B) , (dΔ , dB)) (δ , v) (dδ ,  dv)) vs v₁ p = refl


ElStrNatS :  (g : MorS n m) (v : MorS m (suc m)) (vs : is-sectionS v) (v₁ : ∂₁S v ≡ UUStrS (∂₀S v)) (p : ∂₀S v ≡ ∂₁S g) → starS g (ElStrS v vs v₁) (! p ∙ ! (ElStr=S v vs v₁)) ≡ ElStrS (ssS (compS v g (! p))) (ss-is-sectionS (compS v g (! p))) (ss-comp-section₁S g v vs (! p) ∙ ap2-irr starS {a = g} refl v₁ ∙ UUStrNatS g (∂₀S v) p ∙ ap UUStrS (! (ss₀S (compS v g (! p)) ∙ (comp₀S v g (! p)))))
ElStrNatS = //-elimP λ g → //-elimP (λ v → ElStrNatS-// g v)  


betaStrS-// : (u : DMor (suc n) (suc (suc n))) (us : is-sectionS (proj u)) (a : DMor n (suc n)) (as : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (∂₁S (proj u)))
            → appStrS (∂₁S (proj u)) (lamStrS (proj u) us) (lamStrsS (proj u) us) (lamStr₁S (proj u) us) (proj a) as a₁ ≡ ssS (compS (proj u) (proj a) (a₁ ∙ ! (is-section₀S {u = proj u} us)))
betaStrS-// uu@(dmor ((Γ , A) , (dΓ , dA)) (((Γ' , A') , B) , ((dΓ' , dA') , dB)) ((δ , v) , u) ((dδ , dv) , du)) us
            aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) as a₁
            =
  let (dΓ= , _ , _ , dA= , dA=') = reflect (is-section₀S {u = proj uu} us)

      a₀ : ∂₀S (proj aa) ≡ proj (Γ , dΓ)
      a₀ = is-section₀S {u = proj aa} as ∙ ap ftS a₁ ∙ ! (eq dΓ=)

      (dΓa'= , _ , _ , daTy= , _) = reflect a₁

      dΓ'= = CtxTran (CtxSymm dΓ=) (reflect (! a₀))

      da : Derivable (Γ' ⊢ a :> A')
      da = ConvTm2 da~ (CtxSymm dΓ'=) (congTyEq refl ([idMor]Ty A') (SubstTyMorEq2 dΓa dΓa' daTy= (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} as)))

      da[] : Derivable (Γ' ⊢ a :> A' [ idMor _ ]Ty)
      da[] = ConvTm2 da~ (CtxSymm dΓ'=) (SubstTyMorEq2 dΓa dΓa' daTy= (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} as))

      dδv= = sectionS-eq {dA = dB} {dδ = dδ , dv} {du = du} us

      eq1 : Γ' ⊢ (idMor _) [ δa , a ]Mor == (δ , v) [ δa , a ]Mor ∷> (Γ' , A')
      eq1 = SubstMorEq (MorSymm (dΓ , dA) (dΓ' , dA') (sectionS-eq {dA = dB} {dδ = dδ , dv} {du = du} us)) (ConvMor {Δ = Γa' , Aa} (dδa , da~) (CtxSymm dΓ'=) (CtxTran dΓa'= (CtxSymm dΓ=) ,, TyTran (ConvTy dA' (CtxSymm dΓa'=)) daTy= (TySymm (ConvTyEq dA=' (CtxSymm dΓa'=)))))

      eq2 : Γ' ⊢ idMor _ , a == (idMor _) [ δa , a ]Mor ∷> (Γ' , A')
      eq2 = congMorEq refl refl refl (! (idMor[]Mor (δa , a))) ((ConvMorEq
                                                                   (MorSymm dΓa dΓa' (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} as)) (CtxSymm dΓ'=)
                                                                   dΓa'=) , (TmRefl da[]))

      du' : Derivable ((Γ' , A') ⊢ u :> B)
      du' = ConvTm2 du (dΓ= ,, dA=) (congTyEq refl ([idMor]Ty B) (SubstTyMorEq dB (dδ , dv) dδv=))

      du[]= : Derivable (Γ' ⊢ u [ idMor _ , a ]Tm == u [ δa , a ]Tm :> B [ idMor _ , a ]Ty)
      du[]= = SubstTmMorEq du' (idMorDerivable dΓ' , da[]) ((MorSymm dΓ' dΓ' (ConvMorEq (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} as) (CtxSymm dΓ'=) dΓa'=)) , (TmRefl da[]))
   in
   eq ((dΓ'= , (dΓ'= ,, SubstTyMorEq dB (idMorDerivable dΓ' , da[]) (MorTran dΓ' (dΓ' , dA') eq2 eq1))) , MorRefl (idMorDerivable dΓ') , congTmEqTy (! ([idMor]Ty _)) (TmTran (Beta dA' dB du' da) du[]=))

betaStrS : (u : MorS (suc n) (suc (suc n))) (us : is-sectionS u) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS (∂₁S u))
            → appStrS (∂₁S u) (lamStrS u us) (lamStrsS u us) (lamStr₁S u us) a as a₁ ≡ ssS (compS u a (a₁ ∙ ! (is-section₀S us)))
betaStrS = //-elimP (λ u us → //-elimP (betaStrS-// u us))

strSynCCat : StructuredCCat
ccat strSynCCat = synCCat
PiStr strSynCCat = PiStrS
PiStr= strSynCCat {B = B} = PiStr=S B
lamStr strSynCCat = lamStrS
lamStrs strSynCCat {u = u} {us = us} = lamStrsS u us
lamStr₁ strSynCCat {u = u} {us = us} = lamStr₁S u us
appStr strSynCCat = appStrS
appStrs strSynCCat {B = B} {f = f} {fs = fs} {f₁ = f₁} {a = a} {as = as} {a₁ = a₁} = appStrsS B f fs f₁ a as a₁
appStr₁ strSynCCat {B = B} {f = f} {fs = fs} {f₁ = f₁} {a = a} {as = as} {a₁ = a₁} = appStr₁S B f fs f₁ a as a₁
UUStr strSynCCat = UUStrS
UUStr= strSynCCat {X = X} = UUStr=S X
ElStr strSynCCat = ElStrS
ElStr= strSynCCat {v = v} {vs = vs} {v₁ = v₁} = ElStr=S v vs v₁
PiStrNat strSynCCat g {B = B} {p = p} = PiStrNatS g B p
lamStrNat strSynCCat g {u} {us} {p}= lamStrNatS g u us p
appStrNat strSynCCat g {B} {f} {fs} {f₁} {a} {as} {a₁} {p} = appStrNatS g B f fs f₁ a as a₁ p
UUStrNat strSynCCat g {X = X} {p = p} = UUStrNatS g X p
ElStrNat strSynCCat g {v} {vs} {p} {q} = ElStrNatS g v vs p q
betaStr strSynCCat {u = u} {us = us} {a = a} {as = as} {a₁ = a₁} = betaStrS u us a as a₁
