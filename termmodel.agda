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
open DCtx

record DMor (n m : ℕ) : Set where
  constructor dmor
  field
    lhs : DCtx n
    rhs : DCtx m
    mor : Mor n m
    morDer : ctx lhs ⊢ mor ∷> ctx rhs
open DMor

pair-DMor : (δ : DMor n m) {u : TmExpr n} {A : TyExpr m} (dA : Derivable (ctx (rhs δ) ⊢ A)) (du : Derivable (ctx (lhs δ) ⊢ u :> A [ mor δ ]Ty)) → DMor n (suc m)
pair-DMor (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) {u = u} {A = A} dA du = dmor (Γ , dΓ) ((Δ , A) , (dΔ , dA)) (δ , u) (dδ , du)

ObEquiv : (n : ℕ) → EquivRel (DCtx n)
EquivRel._≃_ (ObEquiv n) (Γ , _) (Γ' , _) = ⊢ Γ == Γ'
EquivRel.ref (ObEquiv n) (Γ , dΓ) = CtxRefl dΓ
EquivRel.sym (ObEquiv n) p = CtxSymm p
EquivRel.tra (ObEquiv n) p q = CtxTran p q

MorEquiv : (n m : ℕ) → EquivRel (DMor n m)
EquivRel._≃_ (MorEquiv n m) (dmor (Γ , _) (Δ , _) δ _) (dmor (Γ' , _) (Δ' , _) δ' _) = ((⊢ Γ == Γ') × (⊢ Δ == Δ')) × (Γ ⊢ δ == δ' ∷> Δ)
EquivRel.ref (MorEquiv n m) (dmor (_ , dΓ) (_ , dΔ) _ dδ) = (CtxRefl dΓ , CtxRefl dΔ) , (MorRefl dδ)
EquivRel.sym (MorEquiv n m) {a = a} ((Γ= , Δ=), δ=) = (CtxSymm Γ= , CtxSymm Δ=) , ConvMorEq (MorSymm (der (lhs a)) (der (rhs a)) δ=) Γ= Δ=
EquivRel.tra (MorEquiv n m) {a = a} ((Γ= , Δ=), δ=) ((Γ'= , Δ'=), δ'=) = (CtxTran Γ= Γ'= , CtxTran Δ= Δ'=) , (MorTran (der (lhs a)) (der (rhs a)) δ= (ConvMorEq δ'= (CtxSymm Γ=) (CtxSymm Δ=)))

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

-- postulate
--   #TODO# : {A : Set} → A
--   #TODOP# : {A : Prop} → A

compS-eq : (g g' : DMor m k) (r : EquivRel._≃_ (MorEquiv m k) g g') (f f' : DMor n m) (r' : EquivRel._≃_ (MorEquiv n m) f f') (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj f') ≡ ∂₀S (proj g')) → compS-// g f p ≡ compS-// g' f' q
compS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ') ((dΓ= , dΔ=) , dδ=) (dmor (Γ'' , dΓ'') (Δ'' , dΔ'') δ'' dδ'') (dmor (Γ''' , dΓ''') (Δ''' , dΔ''') δ''' dδ''') ((dΓ''= , dΔ''=) ,  dδ''=) p q =
  eq ((dΓ''= , dΔ=) , SubstMorFullEq dΔ'' dΔ (ConvMor dδ' (CtxSymm (CtxTran (reflect p) dΓ=)) (CtxSymm dΔ=)) (ConvMorEq dδ= (CtxSymm (CtxTran (reflect p) (CtxRefl dΓ))) (CtxRefl dΔ)) dδ'' dδ''=)


compS : (g : MorS m k) (f : MorS n m) (_ : ∂₁S f ≡ ∂₀S g) → MorS n k
compS {n = n} {m = m} {k = k} =
 //-elim-PiS (λ g → //-elim-PiP (λ f p → compS-// g f p)
                        (λ {a} {b} r → compS-eq g g (EquivRel.ref (MorEquiv m k) g) a b r))
         (λ {a} {b} r → //-elimP-PiP (λ f → compS-eq a b r f f (EquivRel.ref (MorEquiv n m) f)))

comp₀S-// : (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) → ∂₀S (compS (proj g) (proj f) p) ≡ ∂₀S (proj f)
comp₀S-// g f p = refl

comp₀S : (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) → ∂₀S (compS g f p) ≡ ∂₀S f
comp₀S = //-elimP (λ g → //-elimP (comp₀S-// g))

comp₁S-// : (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) → ∂₁S (compS (proj g) (proj f) p) ≡ ∂₁S (proj g)
comp₁S-// g f p = refl

comp₁S : (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) → ∂₁S (compS g f p) ≡ ∂₁S g
comp₁S = //-elimP (λ g → //-elimP (comp₁S-// g))

dft : DCtx (suc n) → DCtx n
dft ((Γ , A), (dΓ , dA)) = (Γ , dΓ)

ftS-// : {n : ℕ} → DCtx (suc n) → ObS n
ftS-// Γ = proj (dft Γ)

ftS-eq : {Γ Γ' : DCtx (suc n)} → ⊢ ctx Γ == ctx Γ' → ftS-// Γ ≡ ftS-// Γ'
ftS-eq {Γ = (_ , _) , _} {(_ , _) , _} r = eq (fst r)

ftS : {n : ℕ} → ObS (suc n) → ObS n
ftS = //-rec ftS-// ftS-eq

ppS-// : (X : DCtx (suc n)) → MorS (suc n) n
ppS-// {n = n} Γd@((Γ , A), (dΓ , dA)) = proj (dmor Γd (Γ , dΓ) (weakenMor (idMor n)) (WeakMor A (idMorDerivable dΓ)))

ppS-eq : {X X' : DCtx (suc n)} (_ : EquivRel._≃_ (ObEquiv (suc n)) X X') → ppS-// X ≡ ppS-// X'
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

starS-eq : (f g : DMor m n) (r : EquivRel._≃_ (MorEquiv m n) f g) (X Y : DCtx (suc n)) (r' : EquivRel._≃_ (ObEquiv (suc n)) X Y) (p : ∂₁S (proj f) ≡ ftS (proj X)) (q : ∂₁S (proj g) ≡ ftS (proj Y)) → starS-// f X p ≡ starS-// g Y q
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
                         (λ r → starS-eq f f (EquivRel.ref (MorEquiv m n) f) _ _ r))
          (λ r → //-elimP-PiP (λ X → starS-eq _ _ r X X (EquivRel.ref (ObEquiv (suc n)) X)))

qqS-// : (f : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj f) ≡ ftS (proj X)) → MorS (suc m) (suc n)
qqS-// f@(dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) X@((Δ , A) , (dΔ , dA)) p = proj (dmor (starS-//-u f X p) X (weakenMor δ , var last) ((WeakMor _ (ConvMor dδ (CtxRefl dΓ) (reflect p))) , aux))  where
  aux : Derivable ((Γ , (A [ δ ]Ty)) ⊢ var last :> (A [ weakenMor δ ]Ty))
  aux = congTm (weaken[]Ty A δ last) refl (VarLast (SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflect p)))) 


qqS-eq : (f g : DMor m n) (r : EquivRel._≃_ (MorEquiv m n) f g) (Γ Δ : DCtx (suc n)) (r' : EquivRel._≃_ (ObEquiv (suc n)) Γ Δ) (p : ∂₁S (proj f) ≡ ftS (proj Γ)) (q : ∂₁S (proj g) ≡ ftS (proj Δ)) → qqS-// f Γ p ≡ qqS-// g Δ q
qqS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ') ((dΓ= , dΔ=) , dδ=) ((Γ'' , A) , (dΓ'' , dA)) ((Δ'' , B) , (dΔ'' , dB)) (dΓ''= , dA , dB , dA= , dA=') p q = eq (((( dΓ= , SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflect p)) , SubstTy dB (ConvMor dδ' (CtxRefl dΓ') (reflect q)) , SubstTyFullEq dB (ConvMor dδ (CtxRefl dΓ) (CtxTran dΔ= (reflect q))) (ConvTyEq dA= dΓ''=) (ConvMorEq dδ= (CtxRefl dΓ) (CtxTran dΔ= (reflect q))) , SubstTyFullEq dB (ConvMor dδ dΓ= (CtxTran dΔ= (reflect q))) (ConvTyEq dA= dΓ''=) (ConvMorEq dδ= dΓ= (CtxTran dΔ= (reflect q))) ) , ( dΓ''= , dA , dB , dA= , dA=')) , ( WeakMorEq _ (ConvMorEq dδ= (CtxRefl dΓ) (reflect p)) , congTmRefl (weakenDerLast dA (ConvMor dδ (CtxRefl dΓ) (reflect p))) refl)))

qqS : (f : MorS m n) (X : ObS (suc n)) (_ : ∂₁S f ≡ ftS X) → MorS (suc m) (suc n)
qqS {n = n} {m = m} =
  //-elim-PiS
    (λ f → //-elim-PiP (qqS-// f)
                       (λ r → qqS-eq f f (EquivRel.ref (MorEquiv m n) f) _ _ r))
    (λ r → //-elimP-PiP (λ X → qqS-eq _ _ r X X (EquivRel.ref (ObEquiv (suc n)) X)))


qq₀S-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → ∂₀S (qqS (proj f) (proj X) p) ≡ starS (proj f) (proj X) p
qq₀S-// f X@((Δ , A) , (dΔ , dA)) p = refl

qq₀S : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → ∂₀S (qqS f X p) ≡ starS f X p
qq₀S = //-elimP (λ f → //-elimP (qq₀S-// f))

qq₁S-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → ∂₁S (qqS (proj f) (proj X) p) ≡ proj X
qq₁S-// f X@((Δ , A) , (dΔ , dA)) p = refl

qq₁S : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → ∂₁S (qqS f X p) ≡ X
qq₁S = //-elimP (λ f → //-elimP (qq₁S-// f))

ssS-//-u : (f : DMor m (suc n)) → DMor m (suc m)
ssS-//-u {m = m} f@(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = pair-DMor (idS-u m (Γ , dΓ)) (SubstTy dB dδ) (congTm (! ([idMor]Ty _)) refl du)

ssS-// : (f : DMor m (suc n)) → MorS m (suc m)
ssS-// f = proj (ssS-//-u f)

ssS-eq : {f f' : DMor m (suc n)} (_ : EquivRel._≃_ (MorEquiv m (suc n)) f f') → ssS-// f ≡ ssS-// f'
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

ss-ppS-// : {m n : ℕ} (f : DMor m (suc n)) → compS (ppS (starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f))))) (ssS (proj f)) (ss₁S (proj f) ∙ ! (pp₀S (starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))))) ≡ idS m (∂₀S (proj f))
ss-ppS-// (dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = eq (((CtxRefl dΓ) , (CtxRefl dΓ)) , MorSymm dΓ dΓ (congMorRefl (! (weakenMorInsert (idMor _) (idMor _) u ∙ idMor[]Mor (idMor _))) (idMorDerivable dΓ)))

ss-ppS : {m n : ℕ} (f : MorS m (suc n)) → compS (ppS (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f)))) (ssS f) (ss₁S f ∙ ! (pp₀S (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))))) ≡ idS m (∂₀S f)
ss-ppS {m} {n} = //-elimP (ss-ppS-// {m} {n})

ss-qqS-// : {m n : ℕ} (f : DMor m (suc n)) → (proj f) ≡ compS (qqS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))) (ssS (proj f)) (ss₁S (proj f) ∙ ! (qq₀S (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))))
ss-qqS-// (dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = eq ((CtxRefl dΓ , CtxRefl dΔ , dB , dB , (TyRefl dB) , (TyRefl dB)) , (congMorRefl (! (weakenMorInsert _ (idMor _) u ∙ [idMor]Mor _ ∙ weakenMorInsert _ δ u ∙ idMor[]Mor δ)) dδ) , (TmRefl du))

ss-qqS : {m n : ℕ} (f : MorS m (suc n)) → f ≡ compS (qqS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))) (ssS f) (ss₁S f ∙ ! (qq₀S (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))))
ss-qqS = //-elimP ss-qqS-//

ss-compS-// : {m n k : ℕ} (U : DCtx (suc k)) (g : DMor n k) (f : DMor m (suc n)) (g₁ : ∂₁S (proj g) ≡ ftS (proj U)) (f₁ : ∂₁S (proj f) ≡ starS (proj g) (proj U) g₁) {-g₀ : ∂₀ g ≡ ft (∂₁ f)-} → ssS (proj f) ≡ ssS (compS (qqS (proj g) (proj U) g₁) (proj f) (! (qq₀S (proj g) (proj U) g₁ ∙ ! f₁)))
ss-compS-// U@((Θ' , C), (dΘ' , dC)) g@(dmor (Δ' , dΔ') (Θ , dΘ) θ dθ) f@(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) g₁ f₁ = eq (((CtxRefl dΓ) , CtxRefl dΓ , SubstTy dB dδ , TyEqTy1 dΓ (SubstTyMorEq dC (ConvMor (congMor refl refl (! (weakenMorInsert θ δ u)) (SubstMor dθ (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁))))) (CtxRefl dΓ) (reflect g₁)) (congMorRefl (weakenMorInsert θ δ u) (ConvMor (congMor refl refl (! (weakenMorInsert θ δ u)) (SubstMor dθ (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁))))) (CtxRefl dΓ) (reflect g₁)))) , TyTran (SubstTy (SubstTy (ConvTy dC (CtxSymm (reflect g₁))) dθ) (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁)))) (SubstTyEq (fst (snd (snd (snd (reflect f₁))))) dδ ) (congTyRefl (SubstTy (SubstTy dC (ConvMor dθ (CtxRefl dΔ') (reflect g₁))) (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁)))) ([]Ty-assoc δ θ C ∙ ap (λ z → C [ z ]Ty) (! (weakenMorInsert θ δ u)))) , TyTran (SubstTy (SubstTy (ConvTy dC (CtxSymm (reflect g₁))) dθ) (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁)))) (SubstTyEq (fst (snd (snd (snd (reflect f₁))))) dδ ) (congTyRefl (SubstTy (SubstTy dC (ConvMor dθ (CtxRefl dΔ') (reflect g₁))) (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁)))) ([]Ty-assoc δ θ C ∙ ap (λ z → C [ z ]Ty) (! (weakenMorInsert θ δ u))))) , congMorRefl refl (idMorDerivable dΓ) , congTmRefl (congTm (! ([idMor]Ty (B [ δ ]Ty))) refl du) refl)

ss-compS : {m n k : ℕ} (U : ObS (suc k)) (g : MorS n k) (f : MorS m (suc n)) (g₁ : ∂₁S g ≡ ftS U) (f₁ : ∂₁S f ≡ starS g U g₁) {-g₀ : ∂₀ g ≡ ft (∂₁ f)-} → ssS f ≡ ssS (compS (qqS g U g₁) f (! (qq₀S g U g₁ ∙ ! f₁)))
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
ss-pp synCCat {f = f} = ss-ppS f
ss-qq synCCat {f = f} = ss-qqS f
ss-comp synCCat {U = U} {g = g} {g₁ = g₁} {f = f} {f₁ = f₁} = ss-compS U g f g₁ f₁

open StructuredCCat

{- The syntactic structured contextual category -}

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

-- lamStr  : (u : MorC (suc n) (suc (suc n))) (us : is-section u) → MorC n (suc n)
-- lamStrs : {u : MorC (suc n) (suc (suc n))} {us : is-section u} → is-section (lamStr u us)
-- lamStr₁ : {u : MorC (suc n) (suc (suc n))} {us : is-section u} → ∂₁ (lamStr u us) ≡ PiStr (∂₁ u)

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

lamStrS-//-der-type : (u : DMor (suc n) (suc (suc n))) (us : is-sectionS (proj u)) → Prop
lamStrS-//-der-type (dmor (Δ , dΔ) (((Γ , A) , B) , ((dΓ , dA) , dB)) ((δ , v) , u) ((dδ , dv) , du)) us = Γ ⊢ (idMor _ , lam A B u) ∷> (Γ , pi A B)

lamStrS-//-der : (u : DMor (suc n) (suc (suc n))) (us : is-sectionS (proj u)) → lamStrS-//-der-type u us
lamStrS-//-der (dmor (Δ , dΔ) (((Γ , A) , B) , ((dΓ , dA) , dB)) ((δ , v) , u) ((dδ , dv) , du)) us with reflect us
... | ((_ , dΔ=) , dδ= , dv=) rewrite [idMor]Ty A | [idMor]Ty B
  = (idMorDerivable dΓ , Lam dA dB (ConvTm (Conv (SubstTy dB (dδ , dv)) du (congTyEq refl ([idMor]Ty B) (SubstTyMorEq dB (dδ , dv) (sectionS-eq {dA = dB} {dδ = (dδ , dv)} {du = du} us)))) (CtxSymm dΔ=)))

lamStrS-// : (u : DMor (suc n) (suc (suc n))) (us : is-sectionS (proj u)) → MorS n (suc n)
lamStrS-// uu@(dmor (Δ , dΔ) (((Γ , A) , B) , ((dΓ , dA) , dB)) ((δ , v) , u) ((dδ , dv) , du)) us =
  proj (dmor (Γ , dΓ) ((Γ , pi A B), (dΓ , Pi dA dB)) (idMor _ , lam A B u) (lamStrS-//-der uu us))

lamStrS-eq : {u u' : DMor (suc n) (suc (suc n))} (u~u' : EquivRel._≃_ (MorEquiv (suc n) (suc (suc n))) u u') (us : is-sectionS (proj u)) (us' : is-sectionS (proj u')) → lamStrS-// u us ≡ lamStrS-// u' us'
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
appStrS-// (((Γ , A) , B), ((dΓ , dA) , dB)) (dmor (Γf , dΓf) ((_ , _) , (_ , dA'')) (δf , f) (dδf , df~)) fs f₁ (dmor (Γa , dΓa) ((_ , _) , (_ , dA')) (δa , a) (dδa , da~)) as a₁ =
  let (dΓf= , _ , _ , dfTy= , _) = reflect f₁
      (dΓa= , _ , _ , daTy= , _) = reflect a₁
      da : Derivable (Γ ⊢ a :> A)
      da = ConvTm (Conv (SubstTy dA' dδa) da~ (TyTran (SubstTy dA (ConvMor dδa (CtxRefl dΓa) dΓa=)) (SubstTyEq daTy= dδa) (congTyEq refl ([idMor]Ty A) (SubstTyMorEq dA (ConvMor dδa (CtxRefl dΓa) dΓa=) (ConvMorEq (sectionS-eq {dA = dA'} {dδ = dδa} {du = da~} as) (CtxRefl dΓa) dΓa=))))) (CtxTran (CtxSymm (sectionS-eq-ctx {dA = dA'} {dδ = dδa} {du = da~} as)) dΓa=)
      df : Derivable (Γ ⊢ f :> pi A B)
      df = ConvTm (Conv (SubstTy dA'' dδf) df~ (TyTran (SubstTy (Pi dA dB) (ConvMor dδf (CtxRefl dΓf) dΓf=)) (SubstTyEq dfTy= dδf) (congTyEq refl ([idMor]Ty (pi A B)) (SubstTyMorEq (Pi dA dB) (ConvMor dδf (CtxRefl dΓf) dΓf=) (ConvMorEq (sectionS-eq {dA = dA''} {dδ = dδf} {du = df~} fs) (CtxRefl dΓf) dΓf=))))) (CtxTran (CtxSymm (sectionS-eq-ctx {dA = dA''} {dδ = dδf} {du = df~} fs)) dΓf=)
  in
  proj (dmor (Γ , dΓ)
             ((Γ , B [ idMor _ , a ]Ty) , (dΓ , SubstTy dB (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl da)))
             (idMor _ , app A B f a)
             (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl (App dA dB df da)))

appStrS : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fs : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) → MorS n (suc n)
appStrS B f fs f₁ a as a₁  = //-elim-PiS {B = MorS _ (suc _)} {C = λ B f → ((a : MorS _ (suc _)) (fs : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) → MorS _ (suc _))} (λ B' → //-elim-PiS (λ f' → //-elim (λ a' fs' f₁' → appStrS-// B' f' fs' f₁' a') {!!}) {!!}) {!!} B f a fs f₁ as a₁

-- appStrs

-- appStr₁

UUStrS-// : DCtx n → ObS (suc n)
UUStrS-// (Γ , dΓ) = proj ((Γ , uu) , (dΓ , UU))

UUStrS-eq : {Γ Γ' : DCtx n} → ⊢ ctx Γ == ctx Γ' → UUStrS-// Γ ≡ UUStrS-// Γ'
UUStrS-eq dΓ= = eq (dΓ= , UU , UU , UUCong , UUCong)

UUStrS : ObS n → ObS (suc n)
UUStrS = //-rec UUStrS-// (λ {a} {b} r → UUStrS-eq {Γ = a} {Γ' = b} r)

-- UUStr=S : (X : ObS n) → ftS (UUStrS X) ≡ X
-- UUStr=S = //-elimP (λ _ → refl)

-- ElStrS-// : (u : DMor n (suc n)) (us : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ UUStrS (∂₀S (proj u))) → ObS (suc n)
-- ElStrS-// (dmor (Γ , dΓ) ((_ , u) , (_ , du)) (δ , v) (dδ , dv)) us u₁ =
--   let (_ , _ , _ , du= , _) = reflect u₁
--       dv = Conv (SubstTy du dδ) dv (SubstTyEq du= dδ)
--   in proj ((Γ , el v) , (dΓ , El dv))

-- ElStrS-eq : (u u' : DMor n (suc n)) (r : EquivRel._≃_ (MorEquiv n (suc n)) u u') (us : is-sectionS (proj u)) (us' : is-sectionS (proj u')) (u₁ : ∂₁S (proj u) ≡ UUStrS (∂₀S (proj u))) (u₁' : ∂₁S (proj u') ≡ UUStrS (∂₀S (proj u'))) → ElStrS-// u us u₁ ≡ ElStrS-// u' us' u₁'
-- ElStrS-eq (dmor (Γ , dΓ) ((_ , u) , (_ , du)) (δ , v) (dδ , dv~)) (dmor (Γ' , dΓ') ((_ , u') , (_ , du')) (δ' , v') (dδ' , dv~')) ((dΓ= , _ , _ , _ , _ , _), dδ= , dv=~) us us' u₁ u₁' =
--   let (_ , _ , _ , du= , _) = reflect u₁ in
--   let (_ , _ , _ , du=' , _) = reflect u₁' in
--   let dv : Derivable (Γ ⊢ v :> uu)
--       dv = Conv (SubstTy du dδ) dv~ (SubstTyEq du= dδ)
--   in
--   let dv' : Derivable (Γ' ⊢ v' :> uu)
--       dv' = Conv (SubstTy du' dδ') dv~' (SubstTyEq du=' dδ')
--   in
--   let dv= : Derivable (Γ ⊢ v == v' :> uu)
--       dv= = ConvEq (SubstTy du dδ) dv=~ (SubstTyEq du= dδ)
--   in
--   let dv=' : Derivable (Γ' ⊢ v == v' :> uu)
--       dv=' = ConvTmEq dv= dΓ=
--   in
--   eq (dΓ= , El dv , El dv' , ElCong dv= , ElCong dv=')

-- ElStrS : (u : MorS n (suc n)) (us : is-sectionS u) (u₁ : ∂₁S u ≡ UUStrS (∂₀S u)) → ObS (suc n)
-- ElStrS = //-elim ElStrS-// (λ r → PathOver-Prop→ (λ us us' → PathOver-Prop→Cst (λ u₁ u₁' → ElStrS-eq _ _ r us us' u₁ u₁')))

-- ElStr=S-// : (u : DMor n (suc n)) (us : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ UUStrS (∂₀S (proj u))) → ftS (ElStrS (proj u) us u₁) ≡ ∂₀S (proj u)
-- ElStr=S-// (dmor (Γ , dΓ) ((_ , u) , (_ , du)) (δ , v) (dδ , dv~)) us u₁ = refl

-- ElStr=S : (u : MorS n (suc n)) (us : is-sectionS u) (u₁ : ∂₁S u ≡ UUStrS (∂₀S u)) → ftS (ElStrS u us u₁) ≡ ∂₀S u
-- ElStr=S = //-elimP ElStr=S-//

-- PiStrNatS-// : (g : DMor n m) (B : DCtx (suc (suc m))) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g)) → starS (proj g) (PiStrS (proj B)) (! (PiStr=S (proj B) ∙ p)) ≡ PiStrS (starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p)))
-- PiStrNatS-// (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (((_ , A) , B), ((_ , dA) , dB)) p =
--   let dPi : Derivable (Γ ⊢ pi (A [ δ ]Ty) (B [ weakenMor δ , var last ]Ty))
--       dPi = SubstTy (Pi dA dB) (ConvMor dδ (CtxRefl dΓ) (CtxSymm (reflect p)))
--   in eq (CtxRefl dΓ , dPi , dPi , TyRefl dPi , TyRefl dPi)

-- PiStrNatS : (g : MorS n m) (B : ObS (suc (suc m))) (p : ftS (ftS B) ≡ ∂₁S g) → starS g (PiStrS B) (! (PiStr=S B ∙ p)) ≡ PiStrS (starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p)))
-- PiStrNatS = //-elimP (λ g → //-elimP (PiStrNatS-// g))

-- is-section₀S : {u : MorS n (suc n)} (us : is-sectionS u) → ∂₀S u ≡ ftS (∂₁S u)
-- is-section₀S {u = u} us = ! (id₁S _ (∂₀S u)) ∙ ap ∂₁S (! us) ∙ comp₁S (ppS (∂₁S u)) u (! (pp₀S _)) ∙ pp₁S (∂₁S u)

-- lamStr₀S : {u : MorS (suc n) (suc (suc n))} (us : is-sectionS u) → ∂₀S (lamStrS u us) ≡ ftS (∂₀S u)
-- lamStr₀S {u = u} us = is-section₀S (lamStrsS u us) ∙ ap ftS (lamStr₁S u us) ∙ PiStr=S (∂₁S u) ∙ ap ftS (! (is-section₀S us)) 

-- -- lamStrNat

-- -- appStrNat

-- UUStrNatS-// : (g : DMor n m) (X : DCtx m) (p : proj X ≡ ∂₁S (proj g)) → starS (proj g) (UUStrS (proj X)) (! p ∙ ! (UUStr=S (proj X))) ≡ UUStrS (∂₀S (proj g))
-- UUStrNatS-// (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (_ , _) p = refl

-- UUStrNatS : (g : MorS n m) (X : ObS m) (p : X ≡ ∂₁S g) → starS g (UUStrS X) (! p ∙ ! (UUStr=S X)) ≡ UUStrS (∂₀S g)
-- UUStrNatS = //-elimP (λ g → //-elimP (UUStrNatS-// g))

-- -- ElStrNat

-- -- betaStrS : (u : MorS (suc n) (suc (suc n))) (us : is-sectionS u) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS (∂₁S u))
-- --             → appStrS (∂₁S u) (lamStrS u us) (lamStrsS u us) (lamStr₁ u us) a as a₁ ≡ ssS (compS u a (a₁ ∙ ! (is-section₀S us)))
-- -- betaStrS u us a as a₁ = ?

-- strSynCCat : StructuredCCat
-- ccat strSynCCat = synCCat
-- PiStr strSynCCat = PiStrS
-- PiStr= strSynCCat {B = B} = PiStr=S B
-- lamStr strSynCCat = lamStrS
-- lamStrs strSynCCat {u = u} {us = us} = lamStrsS u us
-- lamStr₁ strSynCCat {u = u} {us = us} = lamStr₁S u us
-- appStr strSynCCat = {!!}
-- appStrs strSynCCat = {!!}
-- appStr₁ strSynCCat = {!!}
-- UUStr strSynCCat = UUStrS
-- UUStr= strSynCCat {X = X} = UUStr=S X
-- ElStr strSynCCat = ElStrS
-- ElStr= strSynCCat {v = v} {vs = vs} {v₁ = v₁} = ElStr=S v vs v₁
-- PiStrNat strSynCCat g {B = B} {p = p} = PiStrNatS g B p
-- lamStrNat strSynCCat = {!!}
-- appStrNat strSynCCat = {!!}
-- UUStrNat strSynCCat g {X = X} {p = p} = UUStrNatS g X p
-- ElStrNat strSynCCat = {!!}
-- betaStr strSynCCat = {!!}
