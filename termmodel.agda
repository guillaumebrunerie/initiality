{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import contextualcat
open import quotients
open import syntx
open import rules

open CCat hiding (Mor) renaming (id to idC)

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
  ObEquiv : {n : ℕ} → EquivRel (DCtx n)
  EquivRel._≃_ ObEquiv (Γ , _) (Γ' , _) = ⊢ Γ == Γ'
  EquivRel.ref ObEquiv (Γ , dΓ) = CtxRefl dΓ
  EquivRel.sym ObEquiv p = CtxSymm p
  EquivRel.tra ObEquiv p q = CtxTran p q

  MorEquiv : {n m : ℕ} → EquivRel (DMor n m)
  EquivRel._≃_ MorEquiv (dmor (Γ , _) (Δ , _) δ _) (dmor (Γ' , _) (Δ' , _) δ' _) = ((⊢ Γ == Γ') × (⊢ Δ == Δ')) × (Γ ⊢ δ == δ' ∷> Δ)
  EquivRel.ref MorEquiv (dmor (_ , dΓ) (_ , dΔ) _ dδ) = (CtxRefl dΓ , CtxRefl dΔ) , (MorRefl dδ)
  EquivRel.sym MorEquiv {a = dmor (_ , dΓ) (_ , dΔ) _ _} ((Γ= , Δ=), δ=) = (CtxSymm Γ= , CtxSymm Δ=) , ConvMorEq (MorSymm dΓ dΔ δ=) Γ= Δ=
  EquivRel.tra MorEquiv {a = dmor (_ , dΓ) (_ , dΔ) _ _} ((Γ= , Δ=), δ=) ((Γ'= , Δ'=), δ'=) = (CtxTran Γ= Γ'= , CtxTran Δ= Δ'=) , (MorTran dΓ dΔ δ= (ConvMorEq δ'= (CtxSymm Γ=) (CtxSymm Δ=)))

idMor+ : {Γ : Ctx n} {A : TyExpr n} {a : TmExpr n} → ⊢ Γ → Derivable (Γ ⊢ a :> A) → Γ ⊢ (idMor n , a) ∷> (Γ , A)
idMor+ dΓ da = (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl da)

idMor+= : {Γ : Ctx n} {A : TyExpr n} {a a' : TmExpr n} → ⊢ Γ → Derivable (Γ ⊢ a == a' :> A) → Γ ⊢ (idMor n , a) == (idMor n , a') ∷> (Γ , A)
idMor+= dΓ da= = (MorRefl (idMorDerivable dΓ) , congTmEqTy (! ([idMor]Ty _)) da=)


Ctx-Ty : (X : Ctx (suc n)) → Ctx n
Ctx-Ty (Γ , A) = Γ

Ty : (X : DCtx (suc n)) → TyExpr n
Ty ((_ , A) , (_ , dA)) = A

Tm : (a : DMor n (suc n)) → TmExpr n
Tm (dmor _ _ (_ , a) _) = a

{- The syntactic contextual category -}

ObS : ℕ → Set
ObS n = DCtx n // ObEquiv

MorS : ℕ → ℕ → Set
MorS n m = DMor n m // MorEquiv

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

compS-//-u : (g : DMor m k) (f : DMor n m) (_ : ∂₁S (proj f) ≡ ∂₀S (proj g)) → DMor n k
compS-//-u (dmor Δd@(Δ , dΔ) Θd θ dθ) (dmor Γd@(Γ , dΓ) Δd'@(Δ' , dΔ') δ dδ) p = dmor Γd Θd (θ [ δ ]Mor) (SubstMor dθ (ConvMor dδ (CtxRefl dΓ) (reflect p)))

compS-// : (g : DMor m k) (f : DMor n m) (_ : ∂₁S (proj f) ≡ ∂₀S (proj g)) → MorS n k
compS-// g f p = proj (compS-//-u g f p)

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
ssS-//-u {m = m} f@(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = dmor (Γ , dΓ) ((Γ , B [ δ ]Ty) , (dΓ , SubstTy dB dδ)) (idMor _ , u) (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl du)

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
CCat.id synCCat = idS _
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

is-section₀S : {u : MorS n (suc n)} (uₛ : is-sectionS u) {X : ObS (suc n)} (u₁ : ∂₁S u ≡ X) → ∂₀S u ≡ ftS X
is-section₀S {u = u} uₛ u₁ = ! (id₁S _ (∂₀S u)) ∙ ap ∂₁S (! uₛ) ∙ comp₁S (ppS (∂₁S u)) u (! (pp₀S _)) ∙ pp₁S (∂₁S u) ∙ ap ftS u₁


DMor-dTm : {Γ : DCtx (suc n)} (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ proj Γ) → Derivable (Ctx-Ty (ctx Γ) ⊢ Tm a :> Ty Γ)
DMor-dTm {Γ = ((Γ , A) , (dΓ , dA))} aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da)) aₛ a₁ =
           let (dΓa'=Γ , Γa'dAA , _ , Γa'dAa=A , ΓdAa=A)  = reflect a₁
               a₀ : ∂₀S (proj aa) ≡ proj (_ , dΓ)
               a₀ = is-section₀S {u = proj aa} aₛ a₁
           in
           congTm ([idMor]Ty _)
                  refl
                  (ConvTm2 da
                           (reflect a₀)
                           (SubstTyFullEq dA
                                          (ConvMor dδa
                                                   (CtxRefl dΓa)
                                                   dΓa'=Γ)
                                          ΓdAa=A
                                          (ConvMorEq (sectionS-eq {A = Aa} {dA = dAa} {dδ = dδa} {du = da}  aₛ)
                                                     (CtxRefl dΓa)
                                                     dΓa'=Γ)))
                   
DMor-dTm= : {Γ Γ' : DCtx (suc n)} (rΓ : Γ ≃ Γ') (a b : DMor n (suc n)) (rab : a ≃ b) (aₛ : is-sectionS (proj a)) (bₛ : is-sectionS (proj b)) (a₁ : ∂₁S (proj a) ≡ proj Γ) (b₁ : ∂₁S (proj b) ≡ proj Γ') → Derivable (Ctx-Ty (ctx Γ) ⊢ Tm a == Tm b :> Ty Γ)
DMor-dTm= {Γ = ((Γ , A) , (dΓ , dA))} {Γ' = ((Γ' , dA') , (dΓ' , dA'))} (dΓ= , _ , _ , ΓdA= , _) aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da)) bb@(dmor (Γb , dΓb) ((Γb' , Ab) , (dΓb' , dAb)) (δb , b) (dδb , db)) rab@(_ , _ , Γada=b) aₛ bₛ a₁ b₁ =
          let (dΓa'=Γ , _ , _ , _ , ΓdAa=A) = reflect a₁ in
          congTmEqTy ([idMor]Ty A)
                     (ConvTmEq2 Γada=b
                                (CtxTran (CtxSymm (sectionS-eq-ctx {dA = dAa} {dδ = dδa} {du = da} aₛ)) dΓa'=Γ)
                                (SubstTyFullEq dA
                                               (ConvMor dδa (CtxRefl dΓa) dΓa'=Γ)
                                               ΓdAa=A
                                               (ConvMorEq (sectionS-eq {A = Aa} {dA = dAa} {dδ = dδa} {du = da} aₛ) (CtxRefl dΓa) dΓa'=Γ)))
                                               
DMor-dMor= : {Γ Γ' : DCtx (suc n)} (rΓ : Γ ≃ Γ') (a b : DMor n (suc n)) (rab : a ≃ b) (aₛ : is-sectionS (proj a)) (bₛ : is-sectionS (proj b)) (a₁ : ∂₁S (proj a) ≡ proj Γ) (b₁ : ∂₁S (proj b) ≡ proj Γ') → (Ctx-Ty (ctx Γ) ⊢ mor a == mor b ∷> ctx Γ)
DMor-dMor= {Γ = ((Γ , A) , (dΓ , dA))} {Γ' = ((Γ' , A') , (dΓ' , dA'))} rΓ@(dΓ= , _ , _ , ΓdA= , _) aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da)) bb@(dmor (Γb , dΓb) ((Γb' , Ab) , (dΓb' , dAb)) (δb , b) (dδb , db)) rab@((_ , _) , Γada=b) aₛ bₛ a₁ b₁ =
                               let (dΓa'=Γ , _ , _ , Γa'dAa=A , _) = reflect a₁
                                   dlhsa= = (CtxTran (reflect (is-section₀S {u = (proj aa)} aₛ refl)) dΓa'=Γ)
                               in ConvMorEq Γada=b dlhsa= (dΓa'=Γ ,, Γa'dAa=A)
                           
DMor-dTm+ : (Γ : DCtx (suc (suc n))) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj Γ)) (b : DMor n (suc n)) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj Γ) a₁) → Derivable (Ctx-Ty (Ctx-Ty (ctx Γ)) ⊢ Tm b :> substTy (Ty Γ) (Tm a))
DMor-dTm+ (((Γ , A) , B) , ((dΓ , dA) , dB)) aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da)) aₛ a₁ bb@(dmor (Γb , dΓb) ((Γb' , Ab) , (dΓb' , dAb)) (δb , b) (dδb , db)) bₛ b₁ =
                    let (dΓa'=Γ , _ , _ , _ , ΓdAa=A) = reflect a₁
                        (dΓb'=Γ , _ , _ , _ , ΓdAb=A) = reflect b₁
                        ((_ , dΓa'=Γa) , _) = reflect aₛ
                        ((_ , dΓb'=Γb) , _) = reflect bₛ
                    in
                    ConvTm
                      (Conv (SubstTy (ConvTy dB (CtxSymm dΓa'=Γ ,, TySymm ΓdAa=A)) (dδa , da))
                       (DMor-dTm bb bₛ b₁)
                       (SubstTyMorEq (ConvTy dB (CtxSymm dΓa'=Γ ,, TySymm ΓdAa=A)) (dδa , da)
                        (sectionS-eq {A = Aa} {dA = dAa} {dδ = dδa} {du = da} aₛ ,
                         TmRefl da)))
                      (CtxTran (CtxSymm dΓa'=Γa) dΓa'=Γ)

DMor-dTm+= : (Γ Γ' : DCtx (suc (suc n))) (rΓ : Γ ≃ Γ') (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ ftS (proj Γ)) (a'₁ : ∂₁S (proj a') ≡ ftS (proj Γ')) (b b' : DMor n (suc n)) (rb : b ≃ b') (bₛ : is-sectionS (proj b)) (b'ₛ : is-sectionS (proj b')) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj Γ) a₁) (b'₁ : ∂₁S (proj b') ≡ starS (proj a') (proj Γ') a'₁)  → Derivable (Ctx-Ty (Ctx-Ty (ctx Γ)) ⊢ Tm b == Tm b' :> substTy (Ty Γ) (Tm a))
DMor-dTm+= (((Γ , A) , B) , ((dΓ , dA) , dB)) (((Γ' , A') , B') , ((dΓ' , dA') , dB')) rΓ@((dΓ= , _ , _ , dA= , _) , _ , _ , dB= , _) aa@(dmor (Γa , dΓa) ((Γ'a , Aa) , (dΓ'a , dAa)) (δa , a) (dδa , da)) aa'@(dmor (Γa' , dΓa') ((Γ'a' , Aa') , (dΓ'a' , dAa')) (δa' , a') (dδa' , da')) ra aₛ a'ₛ a₁ a'₁ bb@(dmor (Γb , dΓb) ((Γ'b , Ab) , (dΓ'b , dAb)) (δb , b) (dδb , db)) bb'@(dmor (Γb' , dΓb') ((Γ'b' , Ab') , (dΓ'b' , dAb')) (δb' , b') (dδb' , db')) rb bₛ b'ₛ b₁ b'₁ = let
                              (dΓ'a=Γ , _ , _ , _ , ΓdAa=A) = reflect a₁
                              (dΓ'b=Γ , _ , _ , _ , ΓdAb=A) = reflect b₁
                              ((_ , dΓ'a=Γa) , _) = reflect aₛ
                              ((_ , dΓ'b=Γb) , _) = reflect bₛ
                              (dΓ'a'=Γ' , _ , _ , _ , ΓdAa'=A) = reflect a'₁
                              (dΓ'b'=Γ' , _ , _ , _ , ΓdAb'=A) = reflect b'₁
                              ((_ , dΓ'a'=Γa') , _) = reflect a'ₛ
                              ((_ , dΓ'b'=Γb') , _) = reflect b'ₛ
                          in
                          ConvTmEq (ConvEq ((SubstTy (ConvTy dB ((CtxSymm dΓ'a=Γ) ,, TySymm ΓdAa=A)) (dδa , da)))
                                           (DMor-dTm= (CtxTran (CtxSymm dΓ'a=Γa) (CtxTran dΓ'a=Γ (CtxTran (CtxTran dΓ= (CtxSymm dΓ'a'=Γ')) dΓ'a'=Γa')) ,,
                                                      SubstTyMorEq2 dΓa (dΓ , dA) dB= (ConvMorEq (DMor-dMor= (dΓ= ,, dA=) aa aa' ra aₛ a'ₛ a₁ a'₁) (CtxTran (CtxSymm dΓ'a=Γ) dΓ'a=Γa) (CtxRefl (dΓ , dA))))
                                                      bb bb' rb bₛ b'ₛ b₁ b'₁)
                                           ((SubstTyMorEq (ConvTy dB
                                                                  ((CtxSymm dΓ'a=Γ) ,, TySymm ΓdAa=A))
                                                                  (dδa , da)
                                                                  (sectionS-eq {A = Aa} {dA = dAa} {dδ = dδa} {du = da} aₛ , (TmRefl da)))))
                                   (CtxTran (CtxSymm dΓ'a=Γa) dΓ'a=Γ)
                                   
--Type formers

UUStrS-//-u : (i : ℕ) → DCtx n → DCtx (suc n)
UUStrS-//-u i (Γ , dΓ) = ((Γ , uu i) , (dΓ , UU))

UUStrS-// : (i : ℕ) → DCtx n → ObS (suc n)
UUStrS-// i Γ = proj (UUStrS-//-u i Γ)

UUStrS-eq : {i : ℕ} {Γ Γ' : DCtx n} → ⊢ ctx Γ == ctx Γ' → UUStrS-// i Γ ≡ UUStrS-// i Γ'
UUStrS-eq dΓ= = eq (dΓ= , UU , UU , UUCong , UUCong)

UUStrS : (i : ℕ) → ObS n → ObS (suc n)
UUStrS i = //-rec (UUStrS-// i) (λ {a} {b} r → UUStrS-eq {Γ = a} {Γ' = b} r)


UUStr=S : (i : ℕ) (X : ObS n) → ftS (UUStrS i X) ≡ X
UUStr=S i = //-elimP (λ _ → refl)


ElStrS-// : (i : ℕ) (v : DMor n (suc n)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ UUStrS i (∂₀S (proj v))) → ObS (suc n)
ElStrS-// i v vₛ v₁ =
  proj ((ctx (lhs v) , el i (Tm v)) , (der (lhs v) , El (DMor-dTm v vₛ v₁)))

ElStrS-eq : {i : ℕ} (v v' : DMor n (suc n)) (r : v ≃ v') (vₛ : is-sectionS (proj v)) (v'ₛ : is-sectionS (proj v')) (v₁ : ∂₁S (proj v) ≡ UUStrS i (∂₀S (proj v))) (v'₁ : ∂₁S (proj v') ≡ UUStrS i (∂₀S (proj v'))) → ElStrS-// i v vₛ v₁ ≡ ElStrS-// i v' v'ₛ v'₁
ElStrS-eq {i = i} v v' r@((dv₀=v'₀ , _) , _) vₛ v'ₛ v₁ v'₁ =
  eq (dv₀=v'₀ ,, ElCong (DMor-dTm= (dv₀=v'₀ ,, UUCong) v v' r vₛ v'ₛ v₁ v'₁))

ElStrS : (i : ℕ) (u : MorS n (suc n)) (us : is-sectionS u) (u₁ : ∂₁S u ≡ UUStrS i (∂₀S u)) → ObS (suc n)
ElStrS i = //-elim-PiP2 (ElStrS-// i) (λ r us us' → PathOver-Prop→Cst (ElStrS-eq _ _ r us us'))


ElStr=S-// : (i : ℕ) (u : DMor n (suc n)) (us : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ UUStrS i (∂₀S (proj u))) → ftS (ElStrS i (proj u) us u₁) ≡ ∂₀S (proj u)
ElStr=S-// i (dmor (Γ , dΓ) ((_ , u) , (_ , du)) (δ , v) (dδ , dv~)) us u₁ = refl

ElStr=S : (i : ℕ) (u : MorS n (suc n)) (us : is-sectionS u) (u₁ : ∂₁S u ≡ UUStrS i (∂₀S u)) → ftS (ElStrS i u us u₁) ≡ ∂₀S u
ElStr=S i = //-elimP (ElStr=S-// i)

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


SigStrS-// : (X : DCtx (suc (suc n))) → ObS (suc n)
SigStrS-// (((Γ , A) , B), ((dΓ , dA) , dB)) = proj ((Γ , sig A B) , (dΓ , Sig dA dB))


SigStrS-eq : {Γ Γ' : DCtx (suc (suc n))} → ⊢ ctx Γ == ctx Γ' → SigStrS-// Γ ≡ SigStrS-// Γ'
SigStrS-eq {Γ  = (((Γ  , A)  , B),  ((dΓ  , dA)  , dB))}
          {Γ' = (((Γ' , A') , B'), ((dΓ' , dA') , dB'))}
          ((dΓ= , dA , dA' , dA= , dA=') , (dB , dB' , dB= , dB='))
          = eq (dΓ= ,, SigCong dA dA= dB=)

SigStrS : (B : ObS (suc (suc n))) → ObS (suc n)
SigStrS = //-rec SigStrS-// SigStrS-eq

SigStr=S-// : (Γ : DCtx (suc (suc n))) → ftS (SigStrS-// Γ) ≡ ftS (ftS (proj Γ))
SigStr=S-// (((Γ  , A)  , B),  ((dΓ  , dA)  , dB)) = refl

SigStr=S : (B : ObS (suc (suc n))) → ftS (SigStrS B) ≡ ftS (ftS B)
SigStr=S = //-elimP SigStr=S-//


NatStrS-// : (Γ : DCtx n) → ObS (suc n)
NatStrS-// (Γ , dΓ) = proj ((Γ , nat) , (dΓ , Nat))

NatStrS-eq : {Γ Γ' : DCtx n} → ⊢ ctx Γ == ctx Γ' → NatStrS-// Γ ≡ NatStrS-// Γ'
NatStrS-eq dΓ= = eq (dΓ= ,, NatCong)

NatStrS : (X : ObS n) → ObS (suc n)
NatStrS = //-rec NatStrS-// (λ dΓ= → eq (dΓ= ,, NatCong))

NatStr=S-// : (Γ : DCtx n) → ftS (NatStrS-// Γ) ≡ (proj Γ)
NatStr=S-// (Γ , dΓ) = refl

NatStr=S : (X : ObS n) → ftS (NatStrS X) ≡ X
NatStr=S = //-elimP NatStr=S-//


IdStrS-// : (Γ : DCtx (suc n)) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ (proj Γ)) (b : DMor n (suc n)) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ (proj Γ)) → ObS (suc n)
IdStrS-// ((Γ , A) , (dΓ , dA)) a aₛ a₁ b bₛ b₁ = proj ((Γ , id A (Tm a) (Tm b)) , dΓ , (Id dA (DMor-dTm a aₛ a₁) (DMor-dTm b bₛ b₁)))

IdStrS-eq : (Γ Γ' : DCtx (suc n)) (rΓ : Γ ≃ Γ') (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ proj Γ) (a'₁ : ∂₁S (proj a') ≡ proj Γ') (b b' : DMor n (suc n)) (rb : b ≃ b') (bₛ : is-sectionS (proj b)) (b'ₛ : is-sectionS (proj b')) (b₁ : ∂₁S (proj b) ≡ proj Γ) (b'₁ : ∂₁S (proj b') ≡ proj Γ') → IdStrS-// Γ a aₛ a₁ b bₛ b₁ ≡ IdStrS-// Γ' a' a'ₛ a'₁ b' b'ₛ b'₁
IdStrS-eq ((Γ , A) , (dΓ , dA)) ((Γ' , A') , (dΓ' , dA')) rA@(dΓ= , _ , _ , dA= , _) a a' ra aₛ a'ₛ a₁ a'₁ b b' rb bₛ b'ₛ b₁ b'₁ = eq (dΓ= ,, IdCong dA= (DMor-dTm= rA _ _ ra aₛ a'ₛ a₁ a'₁) (DMor-dTm= rA _ _ rb bₛ b'ₛ b₁ b'₁))

IdStrS : (A : ObS (suc n)) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ A) (b : MorS n (suc n)) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ A) → ObS (suc n)
IdStrS = //-elim-PiS
         (λ A → //-elim-PiP2 (λ a aₛ a₁ → //-elim-PiP2 (λ b bₛ b₁ → IdStrS-// A a aₛ a₁ b bₛ b₁)
         (λ rb bₛ b'ₛ → PathOver-Prop→Cst (λ b₁ b'₁ → IdStrS-eq A A (ref A) a a (ref a) aₛ aₛ a₁ a₁ _ _ rb bₛ b'ₛ b₁ b'₁ )))
         (λ ra aₛ a'ₛ → PathOver-Prop→Cst λ a₁ a'₁ → funext (//-elimP (λ b → funextP (λ bₛ → funextP (λ b₁ → IdStrS-eq A A (ref A) _ _ ra aₛ a'ₛ a₁ a'₁ b b (ref b) bₛ bₛ b₁ b₁))))))
         (λ rA → //-elimP (λ a → PathOver-CstPropPi (λ aₛ → PathOver-Prop→ (λ a₁ a₁' → PathOver-CstPi (//-elimP λ b → PathOver-CstPropPi (λ bₛ → PathOver-Prop→Cst (λ b₁ b₁' → IdStrS-eq _ _ rA a a (ref a) aₛ aₛ a₁ a₁' b b (ref b) bₛ bₛ b₁ b₁')))))))

IdStr=S-// : (A : DCtx (suc n)) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) (b : DMor n (suc n)) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ proj A) → ftS (IdStrS (proj A) (proj a) aₛ a₁ (proj b) bₛ b₁) ≡ ftS (proj A)
IdStr=S-// ((Γ , A) , (dΓ , dA)) a aₛ a₁ b bₛ b₁ = refl

IdStr=S : (A : ObS (suc n)) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ A) (b : MorS n (suc n)) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ A) → ftS (IdStrS A a aₛ a₁ b bₛ b₁) ≡ ftS A
IdStr=S = //-elimP (λ A → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → IdStr=S-// A a aₛ a₁ b bₛ b₁)))


--Term formers

uuStrS-// : (i : ℕ) (Γ : DCtx n) → MorS n (suc n)
uuStrS-// i (Γ , dΓ) = proj (dmor (Γ , dΓ) (UUStrS-//-u (suc i) (Γ , dΓ)) ((idMor _ , uu i)) (idMor+ dΓ UUUU))

uuStrS-eq : (i : ℕ) (Γ Γ' : DCtx n) (rΓ : Γ ≃ Γ') → uuStrS-// i Γ ≡ uuStrS-// i Γ'
uuStrS-eq i (Γ , dΓ) (Γ' , dΓ') dΓ= = eq ((dΓ= , (dΓ= ,, UUCong)) , (idMor+= dΓ UUUUCong))

uuStrS : (i : ℕ) (X : ObS n) → MorS n (suc n)
uuStrS i = //-rec (λ X → uuStrS-// i X) (λ {a} {b} r → uuStrS-eq i a b r)


uuStrₛS-// : (i : ℕ) (Γ : DCtx n) → is-sectionS (uuStrS i (proj Γ))
uuStrₛS-// i (Γ , dΓ) = eq (((CtxRefl dΓ) , (CtxRefl dΓ)) , (congMorEq refl refl ((! (weakenMorInsert _ _ _ ∙ [idMor]Mor _))) refl (MorRefl (idMorDerivable dΓ))))

uuStrₛS : (i : ℕ) (X : ObS n) → is-sectionS (uuStrS i X)
uuStrₛS i = //-elimP λ X → uuStrₛS-// i X


uuStr₁S-// : (i : ℕ) (Γ : DCtx n) → ∂₁S (uuStrS i (proj Γ)) ≡ UUStrS (suc i) (proj Γ)
uuStr₁S-// i (Γ , dΓ) = refl

uuStr₁S : (i : ℕ) (X : ObS n) → ∂₁S (uuStrS i X) ≡ UUStrS (suc i) X
uuStr₁S i = //-elimP (λ X → uuStr₁S-// i X)


piStrS-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (b : DMor (suc n) (suc (suc n))) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) → MorS n (suc n)
piStrS-// i a aₛ a₁ b bₛ b₁ = proj
            (dmor (lhs a)
                  ((ctx (lhs a) , uu i) , (der (lhs a) , UU))
                  ((idMor _) , (pi i (Tm a) (Tm b)))
                  (idMor+ (der (lhs a))
                          (PiUU (DMor-dTm a aₛ a₁) (DMor-dTm b bₛ b₁))))

piStrS-eq : (i : ℕ) (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (a'₁ : ∂₁S (proj a') ≡ UUStrS i (∂₀S (proj a'))) (b b' : DMor (suc n) (suc (suc n))) (rb : b ≃ b') (bₛ : is-sectionS (proj b)) (b'ₛ : is-sectionS (proj b')) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) (b'₁ : ∂₁S (proj b') ≡ UUStrS i (ElStrS i (proj a') a'ₛ a'₁))→ piStrS-// i a aₛ a₁ b bₛ b₁ ≡ piStrS-// i a' a'ₛ a'₁ b' b'ₛ b'₁
piStrS-eq i a a' ra@((da₀=a'₀ , _) , _) aₛ a'ₛ a₁ a'₁ b b' rb bₛ b'ₛ b₁ b'₁ =
            eq ((da₀=a'₀ , (da₀=a'₀ ,, UUCong)) ,
                (idMor+= (der (lhs a))
                         (PiUUCong (DMor-dTm a aₛ a₁)
                                   (DMor-dTm= (da₀=a'₀ ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁)
                                   (DMor-dTm= ((da₀=a'₀ ,, ElCong (DMor-dTm= (da₀=a'₀ ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁)) ,, UUCong) b b' rb bₛ b'ₛ b₁ b'₁))))


piStrS : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (b : MorS (suc n) (suc (suc n))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁)) → MorS n (suc n)
piStrS i = //-elim-PiP3 (λ a aₛ a₁ → //-elim-PiP2 (λ b bₛ b₁ → piStrS-// i a aₛ a₁ b bₛ b₁)
                        (λ {b} {b'} rb bₛ b'ₛ → PathOver-Prop→Cst (λ b₁ b'₁ → piStrS-eq i a a (ref a) aₛ aₛ a₁ a₁ b b' rb bₛ b'ₛ b₁ b'₁ )))
                        (λ {a} {a'} ra aₛ a'ₛ → PathOver-PropPi (λ a₁ a'₁ → PathOver-CstPi (//-elimP (λ b → PathOver-Prop→ (λ bₛ bₛ' → PathOver-Prop→Cst (λ b₁ b₁' → piStrS-eq i a a' ra aₛ a'ₛ a₁ a'₁ b b (ref b) bₛ bₛ' b₁ b₁')))))) 

piStrₛS-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a))
      (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a)))
      (b : DMor (suc n) (suc (suc n))) (bₛ : is-sectionS (proj b))
      (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) →
      is-sectionS (piStrS i (proj a) aₛ a₁ (proj b) bₛ b₁)
piStrₛS-// i a aₛ a₁ b bₛ b₁ = eq (((CtxRefl (der (lhs a))) , (CtxRefl (der (lhs a)))) , (congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor _)) refl (MorRefl (idMorDerivable (der (lhs a))))))

piStrₛS : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (b : MorS (suc n) (suc (suc n))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁)) → is-sectionS (piStrS i a aₛ a₁ b bₛ b₁)
piStrₛS i = //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → piStrₛS-// i a aₛ a₁ b bₛ b₁))

piStr₁S-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (b : DMor (suc n) (suc (suc n))) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) → ∂₁S (piStrS i (proj a) aₛ a₁ (proj b) bₛ b₁) ≡ UUStrS i (∂₀S (proj a))
piStr₁S-// i a aₛ a₁ b bₛ b₁ = refl

piStr₁S : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (b : MorS (suc n) (suc (suc n))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁)) → ∂₁S (piStrS i a aₛ a₁ b bₛ b₁) ≡ UUStrS i (∂₀S a)
piStr₁S i = //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → piStr₁S-// i a aₛ a₁ b bₛ b₁))


lamStrS-// : (B : DCtx (suc (suc n))) (u : DMor (suc n) (suc (suc n))) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) → MorS n (suc n)
lamStrS-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u uₛ u₁ =
  proj (dmor (Γ , dΓ) ((Γ , pi A B), (dΓ , Pi dA dB)) (idMor _ , lam A B (Tm u)) (idMor+ dΓ (Lam dA dB (DMor-dTm u uₛ u₁))))

lamStrS-eq : {B B' : DCtx (suc (suc n))} (rB : B ≃ B') {u u' : DMor (suc n) (suc (suc n))} (u~u' : u ≃ u') (uₛ : is-sectionS (proj u)) (u'ₛ : is-sectionS (proj u')) (u₁ : ∂₁S (proj u) ≡ proj B) (u'₁ : ∂₁S (proj u') ≡ proj B') → lamStrS-// B u uₛ u₁ ≡ lamStrS-// B' u' u'ₛ u'₁
lamStrS-eq {B = (((Γ , A) , B) , ((dΓ , dA) , dB))} {B' = (((Γ' , A') , B') , ((dΓ' , dA') , dB'))} rB@((dΓ= , _ , _ , dA= , _) , _ , _ , dB= , _) u~u' uₛ u'ₛ u₁ u'₁ = eq ((dΓ= , (dΓ= ,, PiCong dA dA= dB=)) , idMor+= dΓ (LamCong dA dA= dB= (DMor-dTm= rB _ _ u~u' uₛ u'ₛ u₁ u'₁))) 

lamStrS : (B : ObS (suc (suc n))) (u : MorS (suc n) (suc (suc n))) (us : is-sectionS u) (u₁ : ∂₁S u ≡ B) → MorS n (suc n)
lamStrS = //-elim-PiS (λ B → //-elim-PiP2 (λ u uₛ u₁ → lamStrS-// B u uₛ u₁) (λ ru uₛ u'ₛ → PathOver-Prop→Cst (λ u₁ u'₁ → lamStrS-eq (ref B) ru uₛ u'ₛ u₁ u'₁))) (λ rB → //-elimP (λ u → PathOver-CstPropPi λ uₛ → PathOver-Prop→Cst (λ u₁ u₁' → lamStrS-eq rB (ref u) uₛ uₛ u₁ u₁')))


lamStrₛS-// : (B : DCtx (suc (suc n))) (u : DMor (suc n) (suc (suc n))) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) → is-sectionS (lamStrS-// B u uₛ u₁)
lamStrₛS-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u uₛ u₁ = eq ((CtxRefl dΓ , CtxRefl dΓ) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor _)) refl (MorRefl (idMorDerivable dΓ)))

lamStrₛS : (B : ObS (suc (suc n))) (u : MorS (suc n) (suc (suc n))) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ B) → is-sectionS (lamStrS B u uₛ u₁)
lamStrₛS = //-elimP (λ B → //-elimP (λ u uₛ u₁ → lamStrₛS-// B u uₛ u₁))


lamStr₁S-// : (B : DCtx (suc (suc n))) (u : DMor (suc n) (suc (suc n))) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) → ∂₁S (lamStrS-// B u uₛ u₁) ≡ PiStrS (proj B)
lamStr₁S-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u us u₁ = refl

lamStr₁S : (B : ObS (suc (suc n))) (u : MorS (suc n) (suc (suc n))) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ B) → ∂₁S (lamStrS B u uₛ u₁) ≡ PiStrS B
lamStr₁S = //-elimP (λ B → (//-elimP (λ u uₛ u₁ → lamStr₁S-// B u uₛ u₁)))


appStrS-// : (B : DCtx (suc (suc n))) (f : DMor n (suc n)) (fs : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor n (suc n)) (as : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) → MorS n (suc n)
appStrS-// (((Γ , A) , B), ((dΓ , dA) , dB)) f fₛ f₁ a aₛ a₁ = 
  proj (dmor
       (Γ , dΓ)
       ((Γ , substTy B (Tm a)) ,  (dΓ , SubstTy dB (idMor+ dΓ (DMor-dTm a aₛ a₁))))
       (idMor _ , app A B (Tm f) (Tm a)) (idMor+ dΓ (App dA dB (DMor-dTm f fₛ f₁) (DMor-dTm a aₛ a₁)))
       )
 
appStr-eq : (B B' : DCtx (suc (suc n))) (rB : B ≃ B') (f f' : DMor n (suc n)) (rf : f ≃ f') (fₛ : is-sectionS (proj f)) (f'ₛ : is-sectionS (proj f')) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (f₁' : ∂₁S (proj f') ≡ PiStrS (proj B')) (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (a'₁ : ∂₁S (proj a') ≡ ftS (proj B')) → appStrS-// B f fₛ f₁ a aₛ a₁ ≡ appStrS-// B' f' f'ₛ f₁' a' a'ₛ a'₁
appStr-eq (((Γ , A) , B), ((dΓ , dA) , dB)) 
          (((Γ+ , A+) , B+), ((dΓ+ , dA+) , dB+))
          rB@((dΓ= , _ , _ , dA= , _) , _ , _ , dB= , _)
          f f' rf fₛ f'ₛ f₁ f'₁ a a' ra  aₛ a'ₛ a₁ a'₁ =
                                eq ((dΓ= , (dΓ= ,, SubstTyMorEq2 dΓ (dΓ , dA) dB= (idMor+= dΓ (DMor-dTm= (fst rB) a a' ra aₛ a'ₛ a₁ a'₁)))) ,
                                    (idMor+= dΓ (AppCong dA dA= dB= (DMor-dTm= (dΓ= ,, PiCong dA dA= dB=) f f' rf fₛ f'ₛ f₁ f'₁) (DMor-dTm= (dΓ= ,, dA=) a a' ra aₛ a'ₛ a₁ a'₁))))

appStrS : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fs : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) → MorS n (suc n)
appStrS =
  //-elim-PiS (λ B → //-elim-PiP2 (λ f fs f₁ → //-elim-PiP2 (appStrS-// B f fs f₁)
    (λ ra as as' → PathOver-Prop→Cst (λ a₁ a₁' → appStr-eq B B (ref B) f f (ref f) fs fs f₁ f₁ _ _ ra as as' a₁ a₁')))
    (λ rf fs fs' → PathOver-Prop→Cst (λ f₁ f₁' → funext (//-elimP (λ a → funextP (λ as → funextP (λ a₁ → appStr-eq B B (ref B) _ _ rf fs fs' f₁ f₁' a a (ref a) as as a₁ a₁)))))))
    (λ rB → //-elimP λ f → PathOver-CstPropPi (λ fs → PathOver-Prop→ (λ f₁ f₁' → PathOver-CstPi (//-elimP (λ a → PathOver-CstPropPi (λ as → PathOver-Prop→Cst (λ a₁ a₁' → appStr-eq _ _ rB f f (ref f) fs fs f₁ f₁' a a (ref a) as as a₁ a₁')))))))

appStrₛS-// : (B : DCtx (suc (suc n))) (f : DMor n (suc n)) (fs : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor n (suc n)) (as : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) → is-sectionS (appStrS (proj B) (proj f) fs f₁ (proj a) as a₁)
appStrₛS-// (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γf' , Af) , (dΓf' , dAf)) (δf , f) (dδf , df~)) fs f₁ aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) as a₁
  = eq ((CtxRefl dΓ , CtxRefl dΓ) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ idMor[]Mor _)) refl (MorRefl (idMorDerivable dΓ)))

appStrₛS : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fs : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) → is-sectionS (appStrS B f fs f₁ a as a₁)
appStrₛS = //-elimP (λ B → //-elimP (λ f fs f₁ → //-elimP (appStrₛS-// B f fs f₁)))

appStr₁S-// : (B : DCtx (suc (suc n))) (f : DMor n (suc n)) (fs : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) → ∂₁S (appStrS (proj B) (proj f) fs f₁ (proj a) aₛ a₁) ≡ starS (proj a) (proj B) a₁
appStr₁S-// (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γf' , Af) , (dΓf' , dAf)) (δf , f) (dδf , df~)) fs f₁ aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) aₛ a₁
  = let (dΓ= , _ , _ , daTy= , _) = reflect a₁
        dΓ=' = CtxTran (CtxSymm dΓ=) (sectionS-eq-ctx {dA = dAa} {dδ = dδa} {du = da~} aₛ)        
 in eq (dΓ=' ,, SubstTyMorEq dB (idMor+ dΓ (DMor-dTm aa aₛ a₁)) (ConvMorEq (MorSymm dΓa dΓa' (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} aₛ)) (CtxSymm dΓ=') dΓ= , TmRefl (congTm (! ([idMor]Ty A)) refl (DMor-dTm aa aₛ a₁))))

appStr₁S : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fs : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) → ∂₁S (appStrS B f fs f₁ a as a₁) ≡ starS a B a₁
appStr₁S = //-elimP (λ B → //-elimP (λ f fs f₁ → //-elimP (appStr₁S-// B f fs f₁)))


sigStrS-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (b : DMor (suc n) (suc (suc n))) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) → MorS n (suc n)
sigStrS-// i a aₛ a₁ b bₛ b₁ =  proj
            (dmor (lhs a)
                  ((ctx (lhs a) , uu i) , (der (lhs a) , UU))
                  ((idMor _) , (sig i (Tm a) (Tm b)))
                  (idMor+ (der (lhs a))
                          (SigUU (DMor-dTm a aₛ a₁) (DMor-dTm b bₛ b₁))))

sigStrS-eq : (i : ℕ) (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (a'₁ : ∂₁S (proj a') ≡ UUStrS i (∂₀S (proj a'))) (b b' : DMor (suc n) (suc (suc n))) (rb : b ≃ b') (bₛ : is-sectionS (proj b)) (b'ₛ : is-sectionS (proj b')) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) (b'₁ : ∂₁S (proj b') ≡ UUStrS i (ElStrS i (proj a') a'ₛ a'₁)) → sigStrS-// i a aₛ a₁ b bₛ b₁ ≡ sigStrS-// i a' a'ₛ a'₁ b' b'ₛ b'₁
sigStrS-eq i a a' ra@((da₀=a'₀ , _) , _) aₛ a'ₛ a₁ a'₁ b b' rb bₛ b'ₛ b₁ b'₁ =
           eq ((da₀=a'₀ , (da₀=a'₀ ,, UUCong)) , (idMor+= (der (lhs a))
                                                          (SigUUCong (DMor-dTm a aₛ a₁)
                                                                     (DMor-dTm= (da₀=a'₀ ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁)
                                                                     (DMor-dTm= ((da₀=a'₀ ,, ElCong (DMor-dTm= (da₀=a'₀ ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁)) ,, UUCong) b b' rb bₛ b'ₛ b₁ b'₁))))

sigStrS : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (b : MorS (suc n) (suc (suc n))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁)) → MorS n (suc n)
sigStrS i = //-elim-PiP3 (λ a aₛ a₁ → //-elim-PiP2 (λ b bₛ b₁ → sigStrS-// i a aₛ a₁ b bₛ b₁)
                         (λ {b} {b'} rb bₛ b'ₛ → PathOver-Prop→Cst (λ b₁ b'₁ → sigStrS-eq i a a (ref a) aₛ aₛ a₁ a₁ b b' rb bₛ b'ₛ b₁ b'₁ )))
                         (λ {a} {a'} ra aₛ a'ₛ → PathOver-PropPi (λ a₁ a'₁ → PathOver-CstPi (//-elimP (λ b → PathOver-Prop→ (λ bₛ b'ₛ → PathOver-Prop→Cst (λ b₁ b'₁ → sigStrS-eq i a a' ra aₛ a'ₛ a₁ a'₁ b b (ref b) bₛ b'ₛ b₁ b'₁)) ))))

sigStrₛS-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a))
      (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a)))
      (b : DMor (suc n) (suc (suc n))) (bₛ : is-sectionS (proj b))
      (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) →
      is-sectionS (sigStrS i (proj a) aₛ a₁ (proj b) bₛ b₁)
sigStrₛS-// i a aₛ a₁ b bₛ b₁ = eq (((CtxRefl (der (lhs a))) , (CtxRefl (der (lhs a)))) , (congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor _)) refl (MorRefl (idMorDerivable (der (lhs a))))))

sigStrₛS : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (b : MorS (suc n) (suc (suc n))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁)) → is-sectionS (sigStrS i a aₛ a₁ b bₛ b₁)
sigStrₛS i = //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → sigStrₛS-// i a aₛ a₁ b bₛ b₁))

sigStr₁S-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (b : DMor (suc n) (suc (suc n))) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) → ∂₁S (sigStrS i (proj a) aₛ a₁ (proj b) bₛ b₁) ≡ UUStrS i (∂₀S (proj a))
sigStr₁S-// i a aₛ a₁ b bₛ b₁ = refl

sigStr₁S : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (b : MorS (suc n) (suc (suc n))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁)) → ∂₁S (sigStrS i a aₛ a₁ b bₛ b₁) ≡ UUStrS i (∂₀S a)
sigStr₁S i = //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → sigStr₁S-// i a aₛ a₁ b bₛ b₁))


pairStrS-// : (B : DCtx (suc (suc n))) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (b : DMor n (suc n)) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj B) a₁) → MorS n (suc n)
pairStrS-// BB@(((Γ , A) , B) , ((dΓ , dA) , dB)) a@(dmor _ ((Γa' , Aa) , (_ ,  dAa)) (_ , _) (dδa , da)) aₛ a₁ b bₛ b₁ =
         proj (dmor (Γ , dΓ)
                    ((Γ , sig A B) , (dΓ , Sig dA dB)) ((idMor _) , (pair A B (Tm a) (Tm b)))
                    (idMor+ dΓ (Pair dA dB (DMor-dTm a aₛ a₁) (DMor-dTm+ BB a aₛ a₁ b bₛ b₁)))) 

       

pairStrS-eq : (B B' : DCtx (suc (suc n))) (rB : B ≃ B') (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (a'₁ : ∂₁S (proj a') ≡ ftS (proj B')) (b b' : DMor n (suc n)) (rb : b ≃ b') (bₛ : is-sectionS (proj b)) (b'ₛ : is-sectionS (proj b')) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj B) a₁) (b'₁ : ∂₁S (proj b') ≡ starS (proj a') (proj B') a'₁) → pairStrS-// B a aₛ a₁ b bₛ b₁ ≡ pairStrS-// B' a' a'ₛ a'₁ b' b'ₛ b'₁
pairStrS-eq BB@(((Γ , A) , B) , ((dΓ , dA) , dB))
            BB'@(((Γ' , A') , B') , ((dΓ' , dA') , dB')) rB@(rA@(dΓ= , _ , _ , dA= , _) , _ , _ , dB= , _)
            a@(dmor _ ((Γa' , Aa) , (_ ,  dAa)) (_ , _) (dδa , da))
            a'@(dmor _ ((Γa'' , Aa') , (_ ,  dAa')) (_ , _) (dδa' , da')) ra aₛ a'ₛ a₁ a'₁ b b' rb bₛ b'ₛ b₁ b'₁ = 
                              eq ((dΓ= , (dΓ= ,, SigCong dA dA= dB=)) ,
                                 idMor+= dΓ
                                 (PairCong dA dA= dB= (DMor-dTm= rA a a' ra aₛ a'ₛ a₁ a'₁) (DMor-dTm+= BB BB' rB a a' ra aₛ a'ₛ a₁ a'₁ b b' rb bₛ b'ₛ b₁ b'₁)))


pairStrS : (B : ObS (suc (suc n))) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) (b : MorS n (suc n)) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ starS a B a₁) → MorS n (suc n)
pairStrS = //-elim-PiS (λ B → //-elim-PiP3 (λ a aₛ a₁ → //-elim-PiP2 (λ b bₛ b₁ → pairStrS-// B a aₛ a₁ b bₛ b₁)
                       (λ {b} {b'} rb bₛ b'ₛ → PathOver-Prop→Cst (λ b₁ b'₁ → pairStrS-eq B B (ref B) a a (ref a) aₛ aₛ a₁ a₁ b b' rb bₛ b'ₛ b₁ b'₁)))
                       (λ {a} {a'} ra aₛ a'ₛ → PathOver-PropPi (λ a₁ a'₁ → PathOver-CstPi (//-elimP (λ b → PathOver-CstPropPi (λ bₛ → PathOver-Prop→Cst (λ b₁ b₁' → pairStrS-eq B B (ref B) a a' ra aₛ a'ₛ a₁ a'₁ b b (ref b) bₛ bₛ b₁ b₁')))))))
                       (λ {B} {B'} rB → //-elimP (λ a → PathOver-CstPropPi (λ aₛ → PathOver-PropPi (λ a₁ a₁' → PathOver-CstPi (//-elimP (λ b → PathOver-CstPropPi (λ bₛ → PathOver-Prop→Cst (λ b₁ b₁' → pairStrS-eq B B' rB a a (ref a) aₛ aₛ a₁ a₁' b b (ref b) bₛ bₛ b₁ b₁'))))))))


pairStrₛS-// : (B : DCtx (suc (suc n))) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (b : DMor n (suc n)) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj B) a₁) → is-sectionS (pairStrS (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁)
pairStrₛS-// (((Γ , A) , B) , ((dΓ , dA) , dB)) a@(dmor _ ((_ , _) , (_ , _)) (_ , _) (_ , _)) aₛ a₁ b bₛ b₁ = eq ((CtxRefl dΓ , CtxRefl dΓ) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable dΓ)))

pairStrₛS : (B : ObS (suc (suc n))) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) (b : MorS n (suc n)) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ starS a B a₁) → is-sectionS (pairStrS B a aₛ a₁ b bₛ b₁)
pairStrₛS = //-elimP (λ B → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → pairStrₛS-// B a aₛ a₁ b bₛ b₁)))

pairStr₁S-// : (B : DCtx (suc (suc n))) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (b : DMor n (suc n)) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj B) a₁) → ∂₁S (pairStrS (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁) ≡ SigStrS (proj B)
pairStr₁S-// (((Γ , A) , B) , ((dΓ , dA) , dB)) a@(dmor _ ((_ , _) , (_ , _)) (_ , _) (_ , _)) aₛ a₁ b bₛ b₁ = refl

pairStr₁S : (B : ObS (suc (suc n))) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) (b : MorS n (suc n)) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ starS a B a₁) → ∂₁S (pairStrS B a aₛ a₁ b bₛ b₁) ≡ SigStrS B
pairStr₁S = //-elimP (λ B → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → pairStr₁S-// B a aₛ a₁ b bₛ b₁)))


pr1StrS-// : (B : DCtx (suc (suc n))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) → MorS n (suc n)
pr1StrS-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u uₛ u₁ = proj (dmor (Γ , dΓ) ((Γ , A) , (dΓ , dA)) ((idMor _) , (pr1 A B (Tm u))) (idMor+ dΓ (Pr1 dA dB (DMor-dTm u uₛ u₁))))

pr1StrS-eq : (B B' : DCtx (suc (suc n))) (rB : B ≃ B') (u u' : DMor n (suc n)) (ru : u ≃ u') (uₛ : is-sectionS (proj u)) (u'ₛ : is-sectionS (proj u')) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) (u'₁ : ∂₁S (proj u') ≡ SigStrS (proj B')) → pr1StrS-// B u uₛ u₁ ≡ pr1StrS-// B' u' u'ₛ u'₁
pr1StrS-eq (((Γ , A) , B) , ((dΓ , dA) , dB)) (((Γ' , A') , B') , ((dΓ' , dA') , dB'))  rB@((dΓ= , _ , _ , dA= , _) , _ , _ , dB= , _) u u' ru uₛ u'ₛ u₁ u'₁ = eq ((dΓ= , (dΓ= ,, dA=)) , idMor+= dΓ (Pr1Cong dA dA= dB= (DMor-dTm= (dΓ= ,, SigCong dA dA= dB=) u u' ru uₛ u'ₛ u₁ u'₁)))


pr1StrS : (B : ObS (suc (suc n))) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B) → MorS n (suc n)
pr1StrS = //-elim-PiS (λ B → //-elim-PiP2 (λ u uₛ u₁ → pr1StrS-// B u uₛ u₁)
                      (λ {u} {u'} ru uₛ u'ₛ → PathOver-Prop→Cst (λ u₁ u'₁ → pr1StrS-eq B B (ref B) u u' ru uₛ u'ₛ u₁ u'₁)))
                      (λ {B} {B'} rB → //-elimP (λ u → PathOver-CstPropPi (λ uₛ → PathOver-Prop→Cst (λ u₁ u₁' → pr1StrS-eq B B' rB u u (ref u) uₛ uₛ u₁ u₁'))))


pr1StrₛS-// : (B : DCtx (suc (suc n))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) → is-sectionS (pr1StrS (proj B) (proj u) uₛ u₁)
pr1StrₛS-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u uₛ u₁ = eq ((CtxRefl dΓ , CtxRefl dΓ) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable dΓ)))


pr1StrₛS : (B : ObS (suc (suc n))) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B) → is-sectionS (pr1StrS B u uₛ u₁)
pr1StrₛS = //-elimP (λ B → //-elimP (λ u uₛ u₁ → pr1StrₛS-// B u uₛ u₁))


pr1Str₁S-// : (B : DCtx (suc (suc n))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) → ∂₁S (pr1StrS (proj B) (proj u) uₛ u₁) ≡ ftS (proj B)
pr1Str₁S-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u uₛ u₁ = refl

pr1Str₁S : (B : ObS (suc (suc n))) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B) → ∂₁S (pr1StrS B u uₛ u₁) ≡ ftS B
pr1Str₁S = //-elimP (λ B → //-elimP (λ u uₛ u₁ → pr1Str₁S-// B u uₛ u₁))


pr2StrS-// : (B : DCtx (suc (suc n))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) → MorS n (suc n)
pr2StrS-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u uₛ u₁ = proj (dmor (Γ , dΓ) ((Γ , substTy B (pr1 A B (Tm u))) , (dΓ , SubstTy dB (idMor+ dΓ (Pr1 dA dB (DMor-dTm u uₛ u₁) )))) ((idMor _) , (pr2 A B (Tm u))) (idMor+ dΓ (Pr2 dA dB (DMor-dTm u uₛ u₁))))

pr2StrS-eq : (B B' : DCtx (suc (suc n))) (rB : B ≃ B') (u u' : DMor n (suc n)) (ru : u ≃ u') (uₛ : is-sectionS (proj u)) (u'ₛ : is-sectionS (proj u')) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) (u'₁ : ∂₁S (proj u') ≡ SigStrS (proj B')) → pr2StrS-// B u uₛ u₁ ≡ pr2StrS-// B' u' u'ₛ u'₁
pr2StrS-eq (((Γ , A) , B) , ((dΓ , dA) , dB)) (((Γ' , A') , B') , ((dΓ' , dA') , dB'))  rB@((dΓ= , _ , _ , dA= , _) , _ , _ , dB= , _) u u' ru uₛ u'ₛ u₁ u'₁ = eq ((dΓ= , (dΓ= ,, SubstTyFullEq {Δ = (Γ , A)} (ConvTy dB' (CtxSymm dΓ= ,, ConvTyEq (TySymm dA=) dΓ=)) (idMor+ dΓ (Pr1 dA dB (DMor-dTm u uₛ u₁))) dB= (idMor+= dΓ (Pr1Cong dA dA= dB= (DMor-dTm= (dΓ= ,, SigCong dA dA= dB=) u u' ru uₛ u'ₛ u₁ u'₁))))) , idMor+= dΓ (Pr2Cong dA dA= dB= (DMor-dTm= (dΓ= ,, SigCong dA dA= dB=) u u' ru uₛ u'ₛ u₁ u'₁)))


pr2StrS : (B : ObS (suc (suc n))) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B) → MorS n (suc n)
pr2StrS = //-elim-PiS (λ B → //-elim-PiP2 (λ u uₛ u₁ → pr2StrS-// B u uₛ u₁)
                      (λ {u} {u'} ru uₛ u'ₛ → PathOver-Prop→Cst (λ u₁ u'₁ → pr2StrS-eq B B (ref B) u u' ru uₛ u'ₛ u₁ u'₁)))
                      (λ {B} {B'} rB → //-elimP (λ u → PathOver-CstPropPi (λ uₛ → PathOver-Prop→Cst (λ u₁ u₁' → pr2StrS-eq B B' rB u u (ref u) uₛ uₛ u₁ u₁'))))


pr2StrₛS-// : (B : DCtx (suc (suc n))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) → is-sectionS (pr2StrS (proj B) (proj u) uₛ u₁)
pr2StrₛS-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u uₛ u₁ = eq ((CtxRefl dΓ , CtxRefl dΓ) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable dΓ)))


pr2StrₛS : (B : ObS (suc (suc n))) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B) → is-sectionS (pr2StrS B u uₛ u₁)
pr2StrₛS = //-elimP (λ B → //-elimP (λ u uₛ u₁ → pr2StrₛS-// B u uₛ u₁))


pr2Str₁S-// : (B : DCtx (suc (suc n))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) → ∂₁S (pr2StrS (proj B) (proj u) uₛ u₁) ≡ starS (pr1StrS (proj B) (proj u) uₛ u₁) (proj B) (pr1Str₁S (proj B) (proj u) uₛ u₁)
pr2Str₁S-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u uₛ u₁ = refl

pr2Str₁S : (B : ObS (suc (suc n))) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B) → ∂₁S (pr2StrS B u uₛ u₁) ≡ starS (pr1StrS B u uₛ u₁) B (pr1Str₁S B u uₛ u₁)
pr2Str₁S = //-elimP (λ B → //-elimP (λ u uₛ u₁ → pr2Str₁S-// B u uₛ u₁))


natStrS-// : (i : ℕ) (X : DCtx n) → MorS n (suc n)
natStrS-// i X = proj (dmor X ((ctx X , uu i) , (der X , UU)) (idMor _ , nat i) (idMor+ (der X) NatUU))

natStrS-eq : (i : ℕ) (X X' : DCtx n) (rX : X ≃ X') → natStrS-// i X ≡ natStrS-// i X'
natStrS-eq i X X' rX = eq ((rX , (rX ,, UUCong)) , (idMor+= (der X) NatUUCong))

natStrS : (i : ℕ) (X : ObS n) → MorS n (suc n)
natStrS i = //-rec (λ X → natStrS-// i X) (λ {X} {X'} rX → natStrS-eq i X X' rX)

natStrₛS-// : (i : ℕ) (X : DCtx n) → is-sectionS (natStrS i (proj X))
natStrₛS-// i X = eq ((CtxRefl (der X) , CtxRefl (der X)) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable (der X))))

natStrₛS : (i : ℕ) (X : ObS n) → is-sectionS (natStrS i X)
natStrₛS i = //-elimP (λ X → natStrₛS-// i X)


natStr₁S-// : (i : ℕ) (X : DCtx n) → ∂₁S (natStrS i (proj X)) ≡ UUStrS i (proj X)
natStr₁S-// i X = refl

natStr₁S : (i : ℕ) (X : ObS n) → ∂₁S (natStrS i X) ≡ UUStrS i X
natStr₁S i = //-elimP  (λ X → natStr₁S-// i X)


zeroStrS-// : (X : DCtx n) → MorS n (suc n)
zeroStrS-// X = proj (dmor X ((ctx X , nat) , (der X , Nat)) (idMor _ , zero) (idMor+ (der X) Zero))

zeroStrS-eq : (X X' : DCtx n) (rX : X ≃ X') → zeroStrS-// X ≡ zeroStrS-// X'
zeroStrS-eq X X' rX = eq ((rX , (rX ,, NatCong)) , (idMor+= (der X) ZeroCong))

zeroStrS : (X : ObS n) → MorS n (suc n)
zeroStrS = //-rec (λ X → zeroStrS-// X) λ {X} {X'} rX → zeroStrS-eq X X' rX

zeroStrₛS-// : (X : DCtx n) → is-sectionS (zeroStrS (proj X))
zeroStrₛS-// X = eq ((CtxRefl (der X) , CtxRefl (der X)) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable (der X))))

zeroStrₛS : (X : ObS n) → is-sectionS (zeroStrS X)
zeroStrₛS = //-elimP (λ X → zeroStrₛS-// X)


zeroStr₁S-// : (X : DCtx n) → ∂₁S (zeroStrS (proj X)) ≡ NatStrS (proj X)
zeroStr₁S-// X = refl

zeroStr₁S : (X : ObS n) → ∂₁S (zeroStrS X) ≡ NatStrS X
zeroStr₁S = //-elimP  (λ X → zeroStr₁S-// X)


sucStrS-// : (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (∂₀S (proj u))) → MorS n (suc n)
sucStrS-// u uₛ u₁ = proj (dmor (lhs u) ((ctx (lhs u) , nat) , (der (lhs u) , Nat)) (idMor _ , (suc (Tm u))) (idMor+ (der (lhs u)) (Suc (DMor-dTm u uₛ u₁))))

sucStrS-eq : (u u' : DMor n (suc n)) (ru : u ≃ u') (uₛ : is-sectionS (proj u)) (u'ₛ : is-sectionS (proj u')) (u₁ : ∂₁S (proj u) ≡ NatStrS (∂₀S (proj u))) (u'₁ : ∂₁S (proj u') ≡ NatStrS (∂₀S (proj u'))) → sucStrS-// u uₛ u₁ ≡ sucStrS-// u' u'ₛ u'₁
sucStrS-eq u u' ru@((lhs= , rhs=) , mor=) uₛ u'ₛ u₁ u'₁ = eq ((lhs= , (lhs= ,, NatCong)) , idMor+= (der (lhs u)) (SucCong (DMor-dTm= (lhs= ,, NatCong) u u' ru uₛ u'ₛ u₁ u'₁)))

sucStrS : (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ NatStrS (∂₀S u)) → MorS n (suc n)
sucStrS = //-elim-PiP2 (λ u uₛ u₁ → sucStrS-// u uₛ u₁) (λ {u} {u'} ru uₛ u'ₛ → PathOver-Prop→Cst (λ u₁ u'₁ → sucStrS-eq u u' ru uₛ u'ₛ u₁ u'₁)) 

sucStrₛS-// : (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (∂₀S (proj u))) → is-sectionS (sucStrS (proj u) uₛ u₁)
sucStrₛS-// u uₛ u₁ = eq ((CtxRefl (der (lhs u)) , CtxRefl (der (lhs u))) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable (der (lhs u)))))

sucStrₛS : (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ NatStrS (∂₀S u)) → is-sectionS (sucStrS u uₛ u₁)
sucStrₛS = //-elimP (λ u uₛ u₁ → sucStrₛS-// u uₛ u₁)

sucStr₁S-// : (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (∂₀S (proj u))) → ∂₁S (sucStrS (proj u) uₛ u₁) ≡ NatStrS (∂₀S (proj u))
sucStr₁S-// u uₛ u₁ = refl

sucStr₁S : (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ NatStrS (∂₀S u)) → ∂₁S (sucStrS u uₛ u₁) ≡ NatStrS (∂₀S u)
sucStr₁S = //-elimP (λ u uₛ u₁ → sucStr₁S-// u uₛ u₁)


idStrS-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj a) aₛ a₁)  (v : DMor n (suc n)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj a) aₛ a₁) → MorS n (suc n)
idStrS-// i a aₛ a₁ u uₛ u₁ v vₛ v₁ = proj (dmor (lhs a) ((ctx (lhs a) , uu i) , (der (lhs a) , UU)) (idMor _ , id i (Tm a) (Tm u) (Tm v)) (idMor+ (der (lhs a)) (IdUU (DMor-dTm a aₛ a₁) (DMor-dTm u uₛ u₁) (DMor-dTm v vₛ v₁))))


idStrS-eq : (i : ℕ) (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (a'₁ : ∂₁S (proj a') ≡ UUStrS i (∂₀S (proj a'))) (u u' : DMor n (suc n)) (ru : u ≃ u') (uₛ : is-sectionS (proj u)) (u'ₛ : is-sectionS (proj u')) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj a) aₛ a₁)  (u'₁ : ∂₁S (proj u') ≡ ElStrS i (proj a') a'ₛ a'₁) (v v' : DMor n (suc n)) (rv : v ≃ v') (vₛ : is-sectionS (proj v)) (v'ₛ : is-sectionS (proj v')) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj a) aₛ a₁) (v'₁ : ∂₁S (proj v') ≡ ElStrS i (proj a') a'ₛ a'₁) → idStrS-// i a aₛ a₁ u uₛ u₁ v vₛ v₁ ≡ idStrS-// i a' a'ₛ a'₁ u' u'ₛ u'₁ v' v'ₛ v'₁
idStrS-eq i a a' ra@((lhs= , rhs=) , mor=) aₛ a'ₛ a₁ a'₁ u u' ru uₛ u'ₛ u₁ u'₁ v v' rv vₛ v'ₛ v₁ v'₁ = eq ((lhs= , (lhs= ,, UUCong)) , idMor+= (der (lhs a)) (IdUUCong (DMor-dTm= (lhs= ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁) (DMor-dTm= (lhs= ,, ElCong (DMor-dTm= (lhs= ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁)) u u' ru uₛ u'ₛ u₁ u'₁) (DMor-dTm= (lhs= ,, ElCong (DMor-dTm= (lhs= ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁)) v v' rv vₛ v'ₛ v₁ v'₁)))


idStrS : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ ElStrS i a aₛ a₁)  (v : MorS n (suc n)) (vₛ : is-sectionS v) (v₁ : ∂₁S v ≡ ElStrS i a aₛ a₁) → MorS n (suc n)
idStrS i = //-elim-PiP3 (λ a aₛ a₁ → //-elim-PiP2 (λ u uₛ u₁ → //-elim-PiP2 (λ v vₛ v₁ → idStrS-// i a aₛ a₁ u uₛ u₁ v vₛ v₁) (λ {v} {v'} rv vₛ v'ₛ → PathOver-Prop→Cst (λ v₁ v'₁ → idStrS-eq i a a (ref a) aₛ aₛ a₁ a₁ u u (ref u) uₛ uₛ u₁ u₁ v v' rv vₛ v'ₛ v₁ v'₁)))
                        (λ {u} {u'} ru uₛ u'ₛ → PathOver-Prop→Cst (λ u₁ u'₁ → funext (//-elimP (λ v → funextP (λ vₛ → funextP (λ v₁ → idStrS-eq i a a (ref a) aₛ aₛ a₁ a₁ u u' ru uₛ u'ₛ u₁ u'₁ v v (ref v) vₛ vₛ v₁ v₁)))))))
                        (λ {a} {a'} ra aₛ a'ₛ → PathOver-PropPi (λ a₁ a'₁ → PathOver-CstPi (//-elimP (λ u → PathOver-CstPropPi (λ uₛ → PathOver-Prop→ (λ u₁ u₁' → PathOver-CstPi (//-elimP (λ v → PathOver-CstPropPi (λ vₛ → PathOver-Prop→Cst (λ v₁ v₁' → idStrS-eq i a a' ra aₛ a'ₛ a₁ a'₁ u u (ref u) uₛ uₛ u₁ u₁' v v (ref v) vₛ vₛ v₁ v₁'))))))))))


idStrₛS-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj a) aₛ a₁)  (v : DMor n (suc n)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj a) aₛ a₁) → is-sectionS (idStrS i (proj a) aₛ a₁ (proj u) uₛ u₁ (proj v) vₛ v₁)
idStrₛS-// i a aₛ a₁ u uₛ u₁ v vₛ v₁ = eq ((CtxRefl (der (lhs a)) , CtxRefl (der (lhs a))) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable (der (lhs a)))))

idStrₛS : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ ElStrS i a aₛ a₁)  (v : MorS n (suc n)) (vₛ : is-sectionS v) (v₁ : ∂₁S v ≡ ElStrS i a aₛ a₁) → is-sectionS (idStrS i a aₛ a₁ u uₛ u₁ v vₛ v₁)
idStrₛS i = //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → idStrₛS-// i a aₛ a₁ u uₛ u₁ v vₛ v₁)))

idStr₁S-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj a) aₛ a₁)  (v : DMor n (suc n)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj a) aₛ a₁) → ∂₁S (idStrS i (proj a) aₛ a₁ (proj u) uₛ u₁ (proj v) vₛ v₁) ≡ UUStrS i (∂₀S (proj a))
idStr₁S-// i a aₛ a₁ u uₛ u₁ v vₛ v₁ = refl

idStr₁S : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ ElStrS i a aₛ a₁)  (v : MorS n (suc n)) (vₛ : is-sectionS v) (v₁ : ∂₁S v ≡ ElStrS i a aₛ a₁) → ∂₁S (idStrS i a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ UUStrS i (∂₀S a)
idStr₁S i = //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → idStr₁S-// i a aₛ a₁ u uₛ u₁ v vₛ v₁)))

reflStrS-// : (A : DCtx (suc n)) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ (proj A)) → MorS n (suc n)
reflStrS-// ((Γ , A) , (dΓ , dA)) a aₛ a₁ = proj (dmor (Γ , dΓ) ((Γ , id A (Tm a) (Tm a)) , (dΓ , Id dA (DMor-dTm a aₛ a₁) (DMor-dTm a aₛ a₁))) (idMor _ , refl A (Tm a)) (idMor+ dΓ (Refl dA (DMor-dTm a aₛ a₁))))

reflStrS-eq : (A A' : DCtx (suc n)) (rA : A ≃ A') (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ (proj A)) (a'₁ : ∂₁S (proj a') ≡ (proj A')) → reflStrS-// A a aₛ a₁ ≡ reflStrS-// A' a' a'ₛ a'₁
reflStrS-eq ((Γ , A) , (dΓ , dA)) ((Γ' , A') , (dΓ' , dA')) rA@(dΓ= , _ , _ , dA= , _) a a' ra aₛ a'ₛ a₁ a'₁ = eq ((dΓ= , (dΓ= ,, IdCong dA= (DMor-dTm= (dΓ= ,, dA=) a a' ra aₛ a'ₛ a₁ a'₁) (DMor-dTm= (dΓ= ,, dA=) a a' ra aₛ a'ₛ a₁ a'₁))) , idMor+= dΓ (ReflCong dA= (DMor-dTm= (dΓ= ,, dA=) a a' ra aₛ a'ₛ a₁ a'₁)))

reflStrS  : (A : ObS (suc n)) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ A) → MorS n (suc n)
reflStrS = //-elim-PiS (λ A → //-elim-PiP2 (λ a aₛ a₁ → reflStrS-// A a aₛ a₁) λ {a} {a'} ra aₛ a'ₛ → PathOver-Prop→Cst (λ a₁ a'₁ → reflStrS-eq A A (ref A) a a' ra aₛ a'ₛ a₁ a'₁)) (λ {A} {A'} rA → //-elimP (λ a → PathOver-CstPropPi (λ aₛ → PathOver-Prop→Cst (λ a₁ a₁' → reflStrS-eq A A' rA a a (ref a) aₛ aₛ a₁ a₁'))))

reflStrₛS-// : (A : DCtx (suc n)) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ (proj A)) → is-sectionS (reflStrS (proj A) (proj a) aₛ a₁)
reflStrₛS-// ((Γ , A) , (dΓ , dA)) a aₛ a₁ = eq ((CtxRefl dΓ , CtxRefl dΓ) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable dΓ)))

reflStrₛS :  (A : ObS (suc n)) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ A) → is-sectionS (reflStrS A a aₛ a₁)
reflStrₛS = //-elimP (λ A → (//-elimP (λ a aₛ a₁ → reflStrₛS-// A a aₛ a₁)))


reflStr₁S-// : (A : DCtx (suc n)) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ (proj A)) → ∂₁S (reflStrS (proj A) (proj a) aₛ a₁) ≡ IdStrS (proj A) (proj a) aₛ a₁ (proj a) aₛ a₁
reflStr₁S-// ((Γ , A) , (dΓ , dA)) a aₛ a₁ = refl

reflStr₁S :  (A : ObS (suc n)) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ A) → ∂₁S (reflStrS A a aₛ a₁) ≡ IdStrS A a aₛ a₁ a aₛ a₁
reflStr₁S = //-elimP (λ A → (//-elimP (λ a aₛ a₁ → reflStr₁S-// A a aₛ a₁)))




--Naturality


ssₛS : (f : MorS m (suc n)) → is-sectionS (ssS f)
ssₛS f = ap2-irr compS (ap ppS (ss₁S f)) refl ∙ (ss-ppS f) ∙ ap (idS _) (! (ss₀S f))

starTmS : (g : MorS n m) (u : MorS m (suc m)) (u₀ : ∂₀S u ≡ ∂₁S g) → MorS n (suc n)
starTmS g u u₀ = ssS (compS u g (! u₀))

ss₁'S : {f : MorS m (suc n)} {X : ObS (suc n)} (p : ∂₁S f ≡ X) → ∂₁S (ssS f) ≡ starS (compS (ppS X) f (p ∙ ! (pp₀S X))) X (comp₁S (ppS X) f (p ∙ ! (pp₀S X)) ∙ pp₁S X)
ss₁'S {f = f} refl = ss₁S f

starTm₁S : (g : MorS n m) (u : MorS m (suc m)) (uₛ : is-sectionS u) (u₀ : ∂₀S u ≡ ∂₁S g) {X : ObS (suc m)} (p : ∂₁S u ≡ X) → ∂₁S (starTmS g u u₀) ≡ starS g X (! u₀ ∙ is-section₀S {u = u} uₛ p)
starTm₁S g u uₛ u₀ p = ss₁'S (comp₁S u g (! u₀)) ∙ ap2-irr starS (! (assocS (ppS (∂₁S u)) u g (! u₀) (! (pp₀S (∂₁S u)))) ∙ ap2-irr compS (uₛ ∙ ap (idS _) u₀) refl ∙ id-rightS g) p

starTm₀S : (g : MorS n m) (u : MorS m (suc m)) (u₀ : ∂₀S u ≡ ∂₁S g) → ∂₀S (starTmS g u u₀) ≡ ∂₀S g
starTm₀S g u u₀ = ss₀S (compS u g (! u₀)) ∙ comp₀S u g (! u₀)

star+S : (g : MorS n m) (A : ObS (suc (suc m))) (A= : ftS (ftS A) ≡ ∂₁S g) → ObS (suc (suc n))
star+S g A A= = starS (qqS g (ftS A) (! A=)) A (qq₁S g (ftS A) (! A=))


UUStrNatS-// : {i : ℕ} (g : DMor n m) (X : DCtx m) (p : proj X ≡ ∂₁S (proj g)) → starS (proj g) (UUStrS i (proj X)) (! p ∙ ! (UUStr=S i (proj X))) ≡ UUStrS i (∂₀S (proj g))
UUStrNatS-// (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (_ , _) p = refl

UUStrNatS : {i : ℕ} (g : MorS n m) (X : ObS m) (p : X ≡ ∂₁S g) → starS g (UUStrS i X) (! p ∙ ! (UUStr=S i X)) ≡ UUStrS i (∂₀S g)
UUStrNatS = //-elimP (λ g → //-elimP (UUStrNatS-// g))


ElStrNatS-// : {i : ℕ} (g : DMor n m) (v : DMor m (suc m)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ UUStrS i (∂₀S (proj v))) (p : ∂₀S (proj v) ≡ ∂₁S (proj g))
  → starS (proj g) (ElStrS i (proj v) vₛ v₁) (! (ElStr=S i (proj v) vₛ v₁ ∙ p)) ≡ ElStrS i (starTmS (proj g) (proj v) p) (ssₛS (compS (proj v) (proj g) (! p))) (starTm₁S (proj g) (proj v) vₛ p v₁ ∙ UUStrNatS (proj g) (∂₀S (proj v)) p ∙ ap (UUStrS i) (! (starTm₀S (proj g) (proj v) p)))
ElStrNatS-// (dmor (Θ , dΘ) (Γ' , dΓ') θ dθ) (dmor (Γ , dΓ) ((Δ , B) , (dΔ , dB)) (δ , v) (dδ ,  dv)) vₛ v₁ p = refl


ElStrNatS : {i : ℕ} (g : MorS n m) (v : MorS m (suc m)) (vₛ : is-sectionS v) (v₁ : ∂₁S v ≡ UUStrS i (∂₀S v)) (p : ∂₀S v ≡ ∂₁S g)
  → starS g (ElStrS i v vₛ v₁) (! (ElStr=S i v vₛ v₁ ∙ p)) ≡ ElStrS i (starTmS g v p) (ssₛS (compS v g (! p))) (starTm₁S g v vₛ p v₁ ∙ UUStrNatS g (∂₀S v) p ∙ ap (UUStrS i) (! (starTm₀S g v p)))
ElStrNatS = //-elimP λ g → //-elimP (λ v → ElStrNatS-// g v)


PiStrNatS-// : (g : DMor n m) (B : DCtx (suc (suc m))) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g)) → starS (proj g) (PiStrS (proj B)) (! (PiStr=S (proj B) ∙ p)) ≡ PiStrS (star+S (proj g) (proj B) p)
PiStrNatS-// (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (((_ , A) , B), ((_ , dA) , dB)) p = refl

PiStrNatS : (g : MorS n m) (B : ObS (suc (suc m))) (p : ftS (ftS B) ≡ ∂₁S g) → starS g (PiStrS B) (! (PiStr=S B ∙ p)) ≡ PiStrS (star+S g B p)
PiStrNatS = //-elimP (λ g → //-elimP (PiStrNatS-// g))


SigStrNatS-// : (g : DMor n m) (B : DCtx (suc (suc m))) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g)) → starS (proj g) (SigStrS (proj B)) (! (SigStr=S (proj B) ∙ p)) ≡ SigStrS (star+S (proj g) (proj B) p)
SigStrNatS-// (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (((_ , A) , B), ((_ , dA) , dB)) p = refl

SigStrNatS : (g : MorS n m) (B : ObS (suc (suc m))) (p : ftS (ftS B) ≡ ∂₁S g) → starS g (SigStrS B) (! (SigStr=S B ∙ p)) ≡ SigStrS (star+S g B p)
SigStrNatS = //-elimP (λ g → //-elimP (SigStrNatS-// g))


NatStrNatS-// : (g : DMor n m) (X : DCtx m) (p : proj X ≡ ∂₁S (proj g)) → starS (proj g) (NatStrS (proj X)) (! (NatStr=S (proj X) ∙ p)) ≡ NatStrS (∂₀S (proj g))
NatStrNatS-// g (Γ , dΓ) p = refl

NatStrNatS : (g : MorS n m) (X : ObS m) (p : X ≡ ∂₁S g) → starS g (NatStrS X) (! (NatStr=S X ∙ p)) ≡ NatStrS (∂₀S g)
NatStrNatS = //-elimP (λ g → //-elimP (NatStrNatS-// g))


IdStrNatS-// : (g : DMor n m) (A : DCtx (suc m)) (u : DMor m (suc m)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ (proj A)) (v : DMor m (suc m)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ (proj A)) (p : ftS (proj A) ≡ ∂₁S (proj g))
  → starS (proj g) (IdStrS (proj A) (proj u) uₛ u₁ (proj v) vₛ v₁) (! (IdStr=S (proj A) (proj u) uₛ u₁ (proj v) vₛ v₁ ∙ p))
    ≡ IdStrS (starS (proj g) (proj A) (! p))
      (starTmS (proj g) (proj u) (is-section₀S {u = (proj u)} uₛ u₁ ∙ p)) (ssₛS (compS (proj u) (proj g) (! (is-section₀S {u = (proj u)} uₛ u₁ ∙ p))))
      (starTm₁S (proj g) (proj u) uₛ (is-section₀S {u = (proj u)} uₛ u₁ ∙ p) u₁)
      (starTmS (proj g) (proj v) (is-section₀S {u = (proj v)} vₛ v₁ ∙ p)) (ssₛS (compS (proj v) (proj g) (! (is-section₀S {u = (proj v)} vₛ v₁ ∙ p))))
      (starTm₁S (proj g) (proj v) vₛ (is-section₀S {u = (proj v)} vₛ v₁ ∙ p) v₁)
IdStrNatS-// g ((Γ , A) , (dΓ , dA)) u uₛ u₁ v vₛ v₁ p =
  {!we need to change the definition of ssS-//-u so that Tm (ssS-//-u f) reduces without needing f to reduce, and then we need to use something like  Tm (mor u [ mor g ]Mor) ≡ Tm u [ mor g ]Tm!}

IdStrNatS : (g : MorS n m) (A : ObS (suc m)) (u : MorS m (suc m)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ A) (v : MorS m (suc m)) (vₛ : is-sectionS v) (v₁ : ∂₁S v ≡ A) (p : ftS A ≡ ∂₁S g)
  → starS g (IdStrS A u uₛ u₁ v vₛ v₁) (! (IdStr=S A u uₛ u₁ v vₛ v₁ ∙ p))
    ≡ IdStrS (starS g A (! p))
      (starTmS g u (is-section₀S {u = u} uₛ u₁ ∙ p)) (ssₛS (compS u g (! (is-section₀S {u = u} uₛ u₁ ∙ p))))
      (starTm₁S g u uₛ (is-section₀S {u = u} uₛ u₁ ∙ p) u₁)
      (starTmS g v (is-section₀S {u = v} vₛ v₁ ∙ p)) (ssₛS (compS v g (! (is-section₀S {u = v} vₛ v₁ ∙ p))))
      (starTm₁S g v vₛ (is-section₀S {u = v} vₛ v₁ ∙ p) v₁)
IdStrNatS = //-elimP (λ g → //-elimP (λ A → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → IdStrNatS-// g A u uₛ u₁ v vₛ v₁))))

-- lamStr₀S : (u : MorS (suc n) (suc (suc n))) (us : is-sectionS u) → ∂₀S (lamStrS u us) ≡ ftS (∂₀S u)
-- lamStr₀S u us = is-section₀S (lamStrₛS u us) ∙ ap ftS (lamStr₁S u us) ∙ PiStr=S (∂₁S u) ∙ ap ftS (! (is-section₀S us))




-- CtxSubstRefl : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} {A : TyExpr m} → (⊢ Γ) → (Γ ⊢ δ ∷> Δ) → Derivable (Δ ⊢ A) → ⊢ (Γ , A [ δ ]Ty) == (Γ , A [ δ ]Ty)
-- CtxSubstRefl dΓ dδ dA = (CtxRefl dΓ ,, TyRefl (SubstTy dA dδ))

-- WeakSubstTmEq : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} {A : TyExpr m} {B : TyExpr (suc m)} {u v : TmExpr (suc m)} → (⊢ Γ) → Derivable (Δ ⊢ A) →  Derivable ((Δ , A) ⊢ u == v :> B) → (Γ ⊢ δ ∷> Δ) → Derivable ((Γ , A [ δ ]Ty) ⊢ u [ (weakenMor δ , var last) ]Tm == v [ (weakenMor δ , var last) ]Tm :> B [ (weakenMor δ , var last)  ]Ty)
-- WeakSubstTmEq {δ = δ} {A = A} dΓ dA du=v dδ = ConvTmEq (SubstTmEq du=v ((WeakMor (A [ δ ]Ty) dδ) , weakenDerLast dA dδ)) (CtxSubstRefl dΓ dδ dA)


-- lamStrNatS-// : (g : DMor n m) (u : DMor (suc m) (suc (suc m))) (us : is-sectionS (proj u)) (p : ftS (∂₀S (proj u)) ≡ ∂₁S (proj g))
--               →  ssS (compS (lamStrS (proj u) us) (proj g) (! (lamStr₀S (proj u) us ∙ p))) ≡ lamStrS (ssS (compS (proj u) (qqS (proj g) (∂₀S (proj u)) (! p)) (qq₁S (proj g) (∂₀S (proj u)) (! p )))) (ssₛS (compS (proj u) (qqS (proj g) (∂₀S (proj u)) (! p)) (qq₁S (proj g) (∂₀S (proj u)) (! p ))))
-- lamStrNatS-// (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (dmor ((Δ' , A) , (dΔ' , dA)) (((Δ'' , A') , B) , ((dΔ'' , dA') , dB)) ((θ , a) , u) ((dθ , da) , du)) us p =
--               let dΔ'=Δ = reflect p
--                   ((Δ'refl , (dΔ''=Δ' , _ , _ , _ , dΔ'A'=A)) , (dθ=wid , da=lastA')) = reflect us

--                   wwθ=θ : weakenMor (weakenMor (idMor _)) [ (θ , a) , u ]Mor ≡ θ
--                   wwθ=θ = (weakenMorInsert (weakenMor (idMor _)) (θ , a ) u) ∙ (weakenMorInsert (idMor _) θ a) ∙ (idMor[]Mor θ)
                  
--                   dδΔ' : Γ ⊢ δ ∷> Δ'
--                   dδΔ' = ConvMor dδ (CtxRefl dΓ) (CtxSymm (dΔ'=Δ))

--                   dA'Δ' : Derivable (Δ' ⊢ A')
--                   dA'Δ' = ConvTy dA' dΔ''=Δ'

--                   dBΔ' : Derivable ((Δ' , A) ⊢ B)
--                   dBΔ' = ConvTy dB (dΔ''=Δ' ,, (ConvTyEq dΔ'A'=A (CtxSymm dΔ''=Δ')))

--                   dθΔ' : (Δ' , A) ⊢ θ ∷> Δ'
--                   dθΔ' = ConvMor dθ Δ'refl dΔ''=Δ'
                  
--                   dθ=widΔ' : (Δ' , A) ⊢ θ == weakenMor (idMor _) ∷> Δ'
--                   dθ=widΔ' = ConvMorEq (congMorEq refl refl wwθ=θ refl dθ=wid) Δ'refl dΔ''=Δ'

--                   wwθ : (Δ' , A) ⊢ weakenMor' last (weakenMor' last (idMor _)) [ (θ , a) , u ]Mor ∷> Δ'
--                   wwθ = congMor refl refl (! wwθ=θ) dθΔ'

--                   da=lastA : Derivable ((Δ' , A) ⊢ a == var last :> A [ weakenMor (idMor _) ]Ty )
--                   da=lastA = ConvEq (SubstTy dA'Δ' wwθ) da=lastA' (SubstTyFullEq dA wwθ dΔ'A'=A (congMorEq refl refl (! wwθ=θ) refl dθ=widΔ'))
                  
--                   dBθa : Derivable ((Δ' , A) ⊢ B [ θ , a ]Ty == B)
--                   dBθa = TySymm (congTyEq ([idMor]Ty B) refl (SubstTyMorEq dBΔ' ((WeakMor _ (idMorDerivable dΔ')) , (ConvTm (weakenDerLast dA (idMorDerivable dΔ')) (CtxRefl dΔ' ,, TySymm (congTyRefl dA (! ([idMor]Ty A)))))) (MorSymm (dΔ' , dA) dΔ' dθ=widΔ' , TmSymm (da=lastA))))
                  
--               in
--               ! (eq ((CtxRefl dΓ , (CtxRefl dΓ ,, congTyEq (ap (pi (A [ δ ]Ty)) ([]Ty-assoc _ (θ , a) B)) (ap (λ z → pi (A' [ z ]Ty)  (B [ weakenMor z , var last ]Ty)) (! (idMor[]Mor δ))) (SubstTyEq (PiCong dA (TySymm dΔ'A'=A) dBθa) dδΔ'))) , (MorRefl (idMorDerivable dΓ)) , congTmEqTy (! ([idMor]Ty _ ∙ ap (pi (A [ δ ]Ty)) (! ([]Ty-assoc _ (θ , a) B)))) (congTmEqTm (ap (λ z → lam (A [ δ ]Ty) z _) ([]Ty-assoc _ (θ , a) B)) refl (SubstTmEq (LamCong dA (TySymm dΔ'A'=A) dBθa (TmRefl du)) dδΔ'))))



-- lamStrNatS : (g : MorS n m) (u : MorS (suc m) (suc (suc m))) (us : is-sectionS u) (p : ftS (∂₀S u) ≡ ∂₁S g)
--            → ssS (compS (lamStrS u us) g (! (lamStr₀S u us ∙ p))) ≡ lamStrS (ssS (compS u (qqS g (∂₀S u) (! p)) (qq₁S g (∂₀S u) (! p )))) (ssₛS (compS u (qqS g (∂₀S u) (! p)) (qq₁S g (∂₀S u) (! p ))))
-- lamStrNatS = //-elimP (λ g → //-elimP (λ u → lamStrNatS-// g u))


-- appStr₀S : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fs : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) → ∂₀S (appStrS B f fs f₁ a as a₁) ≡ ftS (ftS B)
-- appStr₀S B f fs f₁ a as a₁ = is-section₀S (appStrₛS B f fs f₁ a as a₁) ∙ ap ftS (appStr₁S B f fs f₁ a as a₁) ∙ (ft-starS a B a₁) ∙ is-section₀S as ∙ ap ftS a₁

-- appStrNatS-// : (g : DMor n m) (B : DCtx (suc (suc m))) (f : DMor m (suc m)) (fs : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor m (suc m)) (as : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))  → ssS (compS (appStrS (proj B) (proj f) fs f₁ (proj a) as a₁) (proj g) (! (appStr₀S (proj B) (proj f) fs f₁ (proj a) as a₁ ∙ p))) ≡ appStrS (starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p))) (ssS (compS (proj f) (proj g) (! (is-section₀S {u = proj f} fs ∙ ap ftS f₁ ∙ (PiStr=S (proj B)) ∙ p)))) (ssₛS (compS (proj f) (proj g) (! (is-section₀S {u = proj f} fs ∙ ap ftS f₁ ∙ (PiStr=S (proj B)) ∙ p)))) (ss-comp-section₁S (proj g) (proj f) fs (! (is-section₀S {u = proj f} fs ∙ ap ftS f₁ ∙ (PiStr=S (proj B)) ∙ p)) ∙  ap2-irr starS {a = (proj g)} refl f₁ {b = ! (is-section₀S {u = proj f} fs ∙ ap ftS f₁ ∙ PiStr=S (proj B) ∙ p) ∙ is-section₀S {u = proj f} fs} ∙ (PiStrNatS (proj g) (proj B) p)) (ssS (compS (proj a) (proj g) (! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p)))) (ssₛS (compS (proj a) (proj g) (! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p)))) (ss-comp-section₁S (proj g) (proj a) as (! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p)) ∙ ! (ft-starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p)) ∙ qq₀S (proj g) (ftS (proj B)) (! p) ∙ ap2-irr starS {a = (proj g)} refl (! a₁) {b = ! p} {b' = ! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p) ∙ is-section₀S {u = proj a} as}))
-- appStrNatS-// gg@(dmor (Δ , dΔ) (Γg , dΓg) δg dδg) (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γf' , piABf) , (dΓf' , dpiABf)) (δf , f) (dδf , df~)) fs f₁ aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) as a₁ p =
--                             let ((_ , dΓf'=Γf) , dδf=id) = reflect fs
--                                 (dΓf'=Γ , _ , _ , dΓf'piABf=piAB , dΓpiABf=piAB) = reflect f₁
--                                 ((_ , dΓa'=Γa) , dδa=id) = reflect as
--                                 (dΓa'=Γ , _ , _ , dΓ'Aa=A , dΓAa=A) = reflect a₁
--                                 dΓ=Γg = reflect p

--                                 dδaΓ : Γa ⊢ δa ∷> Γ
--                                 dδaΓ = ConvMor dδa (CtxRefl dΓa) dΓa'=Γ

--                                 dδa=idΓ : Γa ⊢ δa == idMor _ ∷> Γ
--                                 dδa=idΓ = ConvMorEq (congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor δa) refl dδa=id) (CtxRefl dΓa) dΓa'=Γ
--                                 dδf=idΓf' : Γf' ⊢ δf == idMor _ ∷> Γf'
--                                 dδf=idΓf' = ConvMorEq (congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor δf) refl dδf=id) (CtxSymm dΓf'=Γf) (CtxRefl dΓf')

--                                 da[] : Derivable (Γ ⊢ a :> A [ idMor _ ]Ty)
--                                 da[] = ConvTm2 da~ (CtxTran (CtxSymm dΓa'=Γa) dΓa'=Γ) (SubstTyFullEq dA dδaΓ dΓAa=A dδa=idΓ)

--                                 dδgΓ : Δ ⊢ δg ∷> Γ
--                                 dδgΓ = ConvMor dδg (CtxRefl dΔ) (CtxSymm dΓ=Γg)
--                                 dAΓg : Derivable (Γg ⊢ A)
--                                 dAΓg = ConvTy dA dΓ=Γg
--                                 dBΓg : Derivable ((Γg , A) ⊢ B)
--                                 dBΓg = ConvTy dB (dΓ=Γg ,, (TyRefl dA))
--                                 dfΓg : Derivable (Γg ⊢ f :> pi A B)
--                                 dfΓg = ConvTm2 df~ (CtxTran (CtxSymm dΓf'=Γf) (CtxTran dΓf'=Γ dΓ=Γg)) (ConvTyEq (congTyEq refl ([idMor]Ty (pi A B)) (SubstTyFullEq (Pi (ConvTy dA (CtxSymm dΓf'=Γ)) (ConvTy dB (CtxSymm dΓf'=Γ ,, TyRefl dA))) (ConvMor dδf (CtxSymm dΓf'=Γf) (CtxRefl dΓf')) dΓf'piABf=piAB dδf=idΓf')) dΓf'=Γf)
--                                 daΓg : Derivable (Γg ⊢ a :> A)
--                                 daΓg = ConvTm2 da[] dΓ=Γg (TySymm (congTyRefl dA (! ([idMor]Ty A))))
--                             in
--                             eq ((CtxRefl dΔ , (CtxRefl dΔ ,, congTyRefl (SubstTy (SubstTy dB ((idMorDerivable dΓ) , da[])) (SubstMor (idMorDerivable dΓ) (ConvMor dδg (CtxRefl dΔ) (CtxSymm dΓ=Γg)))) ([]Ty-assoc _ _ B ∙ ! ([]Ty-assoc _ _ B ∙ ap (_[_]Ty B) (ap (λ z → (z , a [ δg ]Tm)) {b = idMor _ [ idMor _ [ δg ]Mor ]Mor} (weakenMorInsert _ _ (a [ δg ]Tm) ∙ [idMor]Mor δg ∙ ! (idMor[]Mor _ ∙ idMor[]Mor δg)) ∙ ap (λ z → (_ , z)) (ap (_[_]Tm a) (! (idMor[]Mor δg)))))))) , ((MorRefl (idMorDerivable dΔ)) , TmRefl (Conv (SubstTy (SubstTy dB ((idMorDerivable dΓ) , da[])) dδgΓ) (SubstTm (App {f = f} {a = a} dAΓg dBΓg dfΓg daΓg) dδg) (congTyRefl (SubstTy (SubstTy dB ((idMorDerivable dΓ) , da[])) dδgΓ) (! ([idMor]Ty _ ∙ ap (_[_]Ty _) (idMor[]Mor δg)))))))


-- appStrNatS : (g : MorS n m) (B : ObS (suc (suc m))) (f : MorS m (suc m)) (fs : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS m (suc m)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) (p : ftS (ftS B) ≡ ∂₁S g)              → ssS (compS (appStrS B f fs f₁ a as a₁) g (! (appStr₀S B f fs f₁ a as a₁ ∙ p))) ≡ appStrS (starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p))) (ssS (compS f g (! (is-section₀S fs ∙ ap ftS f₁ ∙ (PiStr=S B) ∙ p)))) (ssₛS (compS f g (! (is-section₀S fs ∙ ap ftS f₁ ∙ (PiStr=S B) ∙ p)))) (ss-comp-section₁S g f fs (! (is-section₀S fs ∙ ap ftS f₁ ∙ (PiStr=S B) ∙ p)) ∙ ap2-irr starS {a = g} refl f₁  ∙ (PiStrNatS g B p)) (ssS (compS a g (! (is-section₀S as ∙ ap ftS a₁ ∙ p)))) (ssₛS (compS a g (! (is-section₀S as ∙ ap ftS a₁ ∙ p)))) (ss-comp-section₁S g a as (! (is-section₀S as ∙ ap ftS a₁ ∙ p)) ∙ ! (ft-starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p)) ∙ qq₀S g (ftS B) (! p) ∙ ap2-irr starS {a = g} refl (! a₁)))
-- appStrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ f fs f₁ → //-elimP (λ a as a₁ → appStrNatS-// g B f fs f₁ a as a₁))))


-- betaStrS-// : (u : DMor (suc n) (suc (suc n))) (us : is-sectionS (proj u)) (a : DMor n (suc n)) (as : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (∂₁S (proj u)))
--             → appStrS (∂₁S (proj u)) (lamStrS (proj u) us) (lamStrₛS (proj u) us) (lamStr₁S (proj u) us) (proj a) as a₁ ≡ ssS (compS (proj u) (proj a) (a₁ ∙ ! (is-section₀S {u = proj u} us)))
-- betaStrS-// uu@(dmor ((Γ , A) , (dΓ , dA)) (((Γ' , A') , B) , ((dΓ' , dA') , dB)) ((δ , v) , u) ((dδ , dv) , du)) us
--             aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) as a₁
--             =
--   let (dΓ= , _ , _ , dA= , dA=') = reflect (is-section₀S {u = proj uu} us)

--       a₀ : ∂₀S (proj aa) ≡ proj (Γ , dΓ)
--       a₀ = is-section₀S {u = proj aa} as ∙ ap ftS a₁ ∙ ! (eq dΓ=)

--       (dΓa'= , _ , _ , daTy= , _) = reflect a₁

--       dΓ'= = CtxTran (CtxSymm dΓ=) (reflect (! a₀))

--       da : Derivable (Γ' ⊢ a :> A')
--       da = ConvTm2 da~ (CtxSymm dΓ'=) (congTyEq refl ([idMor]Ty A') (SubstTyMorEq2 dΓa dΓa' daTy= (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} as)))

--       da[] : Derivable (Γ' ⊢ a :> A' [ idMor _ ]Ty)
--       da[] = ConvTm2 da~ (CtxSymm dΓ'=) (SubstTyMorEq2 dΓa dΓa' daTy= (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} as))

--       dδv= = sectionS-eq {dA = dB} {dδ = dδ , dv} {du = du} us

--       eq1 : Γ' ⊢ (idMor _) [ δa , a ]Mor == (δ , v) [ δa , a ]Mor ∷> (Γ' , A')
--       eq1 = SubstMorEq (MorSymm (dΓ , dA) (dΓ' , dA') (sectionS-eq {dA = dB} {dδ = dδ , dv} {du = du} us)) (ConvMor {Δ = Γa' , Aa} (dδa , da~) (CtxSymm dΓ'=) (CtxTran dΓa'= (CtxSymm dΓ=) ,, TyTran (ConvTy dA' (CtxSymm dΓa'=)) daTy= (TySymm (ConvTyEq dA=' (CtxSymm dΓa'=)))))

--       eq2 : Γ' ⊢ idMor _ , a == (idMor _) [ δa , a ]Mor ∷> (Γ' , A')
--       eq2 = congMorEq refl refl refl (! (idMor[]Mor (δa , a))) ((ConvMorEq
--                                                                    (MorSymm dΓa dΓa' (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} as)) (CtxSymm dΓ'=)
--                                                                    dΓa'=) , (TmRefl da[]))

--       du' : Derivable ((Γ' , A') ⊢ u :> B)
--       du' = ConvTm2 du (dΓ= ,, dA=) (congTyEq refl ([idMor]Ty B) (SubstTyMorEq dB (dδ , dv) dδv=))

--       du[]= : Derivable (Γ' ⊢ u [ idMor _ , a ]Tm == u [ δa , a ]Tm :> B [ idMor _ , a ]Ty)
--       du[]= = SubstTmMorEq du' (idMorDerivable dΓ' , da[]) ((MorSymm dΓ' dΓ' (ConvMorEq (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} as) (CtxSymm dΓ'=) dΓa'=)) , (TmRefl da[]))
--    in
--    eq ((dΓ'= , (dΓ'= ,, SubstTyMorEq dB (idMorDerivable dΓ' , da[]) (MorTran dΓ' (dΓ' , dA') eq2 eq1))) , MorRefl (idMorDerivable dΓ') , congTmEqTy (! ([idMor]Ty _)) (TmTran (TmEqTm1 dΓ' du[]=) (BetaPi dA' dB du' da) du[]=))

-- -- betaStrS' : (u : MorS (suc n) (suc (suc n))) (us : is-sectionS u) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS (∂₁S u))
-- --             → appStrS (∂₁S u) (lamStrS u us) (lamStrₛS u us) (lamStr₁S u us) a as a₁ ≡ ssS (compS u a (a₁ ∙ ! (is-section₀S us)))
-- -- betaStrS' = //-elimP (λ u us → //-elimP (betaStrS-// u us))

-- -- betaStrS : (B : ObS (suc (suc n))) (u : MorS (suc n) (suc (suc n))) (us : is-sectionS u) (u₁ : ∂₁S u ≡ B) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS (∂₁S u))
-- --             → appStrS B (lamStrS u us) (lamStrₛS u us) (lamStr₁S u us ∙ ap PiStrS u₁) a as (a₁ ∙ ap ftS u₁) ≡ ssS (compS u a (a₁ ∙ ! (is-section₀S us)))
-- -- betaStrS B u us refl = betaStrS' u us


strSynCCat : StructuredCCat

ccat strSynCCat = synCCat

UUStr strSynCCat = UUStrS
UUStr= strSynCCat = UUStr=S _ _
ElStr strSynCCat = ElStrS
ElStr= strSynCCat {v = v} = ElStr=S _ v _ _
PiStr strSynCCat = PiStrS
PiStr= strSynCCat {B = B} = PiStr=S B
SigStr strSynCCat = SigStrS
SigStr= strSynCCat {B = B} = SigStr=S B
NatStr strSynCCat = NatStrS
NatStr= strSynCCat = NatStr=S _
IdStr strSynCCat = IdStrS
IdStr= strSynCCat {A = A} {a = a} {b = b} = IdStr=S A a _ _ b _ _

uuStr strSynCCat = uuStrS
uuStrₛ strSynCCat {X = X} = uuStrₛS _ X
uuStr₁ strSynCCat {X = X} = uuStr₁S _ X 

piStr strSynCCat = piStrS
piStrₛ strSynCCat {a = a} {b = b} = piStrₛS _ a _ _ b _ _
piStr₁ strSynCCat {a = a} {b = b} = piStr₁S _ a _ _ b _ _
lamStr strSynCCat = lamStrS
lamStrₛ strSynCCat {B = B} {u = u} = lamStrₛS B u _ _
lamStr₁ strSynCCat {B = B} {u = u} = lamStr₁S B u _ _
appStr strSynCCat = appStrS
appStrₛ strSynCCat {B = B} {f = f} {a = a} = appStrₛS B f _ _ a _ _
appStr₁ strSynCCat {B = B} {f = f} {a = a} = appStr₁S B f _ _ a _ _

sigStr strSynCCat = sigStrS
sigStrₛ strSynCCat {a = a} {b = b} = sigStrₛS _ a _ _ b _ _
sigStr₁ strSynCCat {a = a} {b = b} = sigStr₁S _ a _ _ b _ _
pairStr strSynCCat = pairStrS
pairStrₛ strSynCCat {B = B} {a = a} {b = b} = pairStrₛS B a _ _ b _ _ 
pairStr₁ strSynCCat {B = B} {a = a} {b = b} = pairStr₁S B a _ _ b _ _
pr1Str strSynCCat = pr1StrS
pr1Strₛ strSynCCat {B = B} {u = u} = pr1StrₛS B u _ _ 
pr1Str₁ strSynCCat {B = B} {u = u} = pr1Str₁S B u _ _ 
pr2Str strSynCCat = pr2StrS
pr2Strₛ strSynCCat {B = B} {u = u} = pr2StrₛS B u _ _
pr2Str₁ strSynCCat {B = B} {u = u} = pr2Str₁S B u _ _

natStr strSynCCat = natStrS
natStrₛ strSynCCat {X = X} = natStrₛS _ X
natStr₁ strSynCCat {X = X} = natStr₁S _ X
zeroStr strSynCCat = zeroStrS
zeroStrₛ strSynCCat {X = X} = zeroStrₛS X
zeroStr₁ strSynCCat {X = X} = zeroStr₁S X
sucStr strSynCCat = sucStrS
sucStrₛ strSynCCat {u = u} = sucStrₛS u _ _
sucStr₁ strSynCCat {u = u} = sucStr₁S u _ _

idStr strSynCCat = idStrS
idStrₛ strSynCCat {a = a} {u = u} {v = v} = idStrₛS _ a _ _ u _ _ v _ _ 
idStr₁ strSynCCat {a = a} {u = u} {v = v} = idStr₁S _ a _ _ u _ _ v _ _
reflStr strSynCCat = reflStrS
reflStrₛ strSynCCat {A = A} {a = a} = reflStrₛS A a _ _
reflStr₁ strSynCCat {A = A} {a = a} = reflStr₁S A a _ _

UUStrNat strSynCCat g {X = X} p = UUStrNatS g X p
ElStrNat strSynCCat g {v} {vₛ} p = ElStrNatS g v _ _ p
PiStrNat strSynCCat g {B = B} p = PiStrNatS g B p
SigStrNat strSynCCat g {B = B} p = SigStrNatS g B p
NatStrNat strSynCCat g {X = X} p = NatStrNatS g X p
IdStrNat strSynCCat g {A = A} {a = u} {b = v} p = IdStrNatS g A u _ _ v _ _ p

uuStrNat strSynCCat g p = {!!}

piStrNat strSynCCat g p = {!!}
lamStrNat strSynCCat g {u} {us} p = {!lamStrNatS g u us p!}
appStrNat strSynCCat g {B} {f} {fₛ} {f₁} {a} {aₛ} {a₁} p = {!appStrNatS g B f fₛ f₁ a aₛ a₁ p!}

sigStrNat strSynCCat g p = {!!}
pairStrNat strSynCCat g p = {!!}
pr1StrNat strSynCCat g p = {!!}
pr2StrNat strSynCCat g p = {!!}

natStrNat strSynCCat g p = {!!}
zeroStrNat strSynCCat g p = {!!}
sucStrNat strSynCCat g p = {!!}

idStrNat strSynCCat g p = {!!}
reflStrNat strSynCCat g p = {!!}

betaPiStr strSynCCat {B = B} {u = u} {uₛ = uₛ} {u₁ = u₁} {a = a} {aₛ = aₛ} {a₁ = a₁} = {!betaPiStrS B u uₛ u₁ a aₛ a₁!}
betaSig1Str strSynCCat = {!!}
betaSig2Str strSynCCat = {!!}
eluuStr strSynCCat = {!!}
elpiStr strSynCCat = {!!}
elsigStr strSynCCat = {!!}
elnatStr strSynCCat = {!!}
elidStr strSynCCat = {!!}
