{-# OPTIONS --rewriting --prop --without-K #-}

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
  ObEquiv : {n : ℕ} → EquivRel (DCtx n)
  EquivRel._≃_ ObEquiv (Γ , _) (Γ' , _) = ⊢ Γ == Γ'
  EquivRel.ref ObEquiv (Γ , dΓ) = CtxRefl dΓ
  EquivRel.sym ObEquiv p = CtxSymm p
  EquivRel.tra ObEquiv p q = CtxTran p q

  MorEquiv : {n m : ℕ} → EquivRel (DMor n m)
  EquivRel._≃_ MorEquiv (dmor (Γ , _) (Δ , _) δ _) (dmor (Γ' , _) (Δ' , _) δ' _) = ((⊢ Γ == Γ') × (⊢ Δ == Δ')) × (Γ ⊢ δ == δ' ∷> Δ)
  EquivRel.ref MorEquiv (dmor (_ , dΓ) (_ , dΔ) _ dδ) = (CtxRefl dΓ , CtxRefl dΔ) , (MorRefl dδ)
  EquivRel.sym MorEquiv ((Γ= , Δ=), δ=) = (CtxSymm Γ= , CtxSymm Δ=) , ConvMorEq (MorSymm δ=) Γ= Δ=
  EquivRel.tra MorEquiv ((Γ= , Δ=), δ=) ((Γ'= , Δ'=), δ'=) = (CtxTran Γ= Γ'= , CtxTran Δ= Δ'=) , (MorTran δ= (ConvMorEq δ'= (CtxSymm Γ=) (CtxSymm Δ=)))


idMor+ : {Γ : Ctx n} {A : TyExpr n} {a : TmExpr n} → ⊢ Γ → Derivable (Γ ⊢ a :> A) → Γ ⊢ (idMor n , a) ∷> (Γ , A)
idMor+ dΓ da = (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl da , DerTmTy dΓ da)

idMor+= : {Γ : Ctx n} {A : TyExpr n} {a a' : TmExpr n} → ⊢ Γ → Derivable (Γ ⊢ a == a' :> A) → Γ ⊢ (idMor n , a) == (idMor n , a') ∷> (Γ , A)
idMor+= dΓ da= = (MorRefl (idMorDerivable dΓ) ,∷ congTmEqTy (! ([idMor]Ty _)) da= , DerTmTy dΓ (TmEqTm1 dΓ da=))

idMor+=' : {Γ : Ctx n} {A : TyExpr n} {a a' : TmExpr n} → ⊢ Γ → Derivable (Γ ⊢ a == a' :> A) → Γ ⊢ (idMor n , a') == (idMor n , a) ∷> (Γ , A)
idMor+=' dΓ da= = MorSymm {Δ = _ , _} {δ = _ , _} {δ' = _ , _} (idMor+= dΓ da=)

ctx-end : Ctx (suc n) → TyExpr n
ctx-end (_ , A) = A

ty2 : (Γ : DCtx (suc n)) → TyExpr n
ty2 Γ = ctx-end (ctx Γ)

ctx-init : Ctx (suc n) → Ctx n
ctx-init (Γ , _) = Γ

ctx2 : (Γ : DCtx (suc n)) → Ctx n
ctx2 Γ = ctx-init (ctx Γ)

derctx2 : (Γ : DCtx (suc n)) → ⊢ ctx2 Γ
derctx2 ((_ , _) , (dΓ , _)) = dΓ

ty2der : (A : DCtx (suc n)) → Derivable (ctx2 A ⊢ ty2 A)
ty2der ((ΓA , A) , (dΓA , dA)) = dA

mor-init : Mor m (suc n) → Mor m n
mor-init (δ , _) = δ

mor-init-der : {Γ : Ctx m} {Δ : Ctx (suc n)} {δ : Mor m (suc n)} → Γ ⊢ δ ∷> Δ → Γ ⊢ mor-init δ ∷> ctx-init Δ
mor-init-der {Δ = Δ , B} {δ , u} (dδ , du) = dδ

mor-end : Mor m (suc n) → TmExpr m
mor-end (_ , u) = u

mor-end-der : {Γ : Ctx m} {Δ : Ctx (suc n)} {δ : Mor m (suc n)} → Γ ⊢ δ ∷> Δ → Derivable (Γ ⊢ mor-end δ :> (ctx-end Δ [ mor-init δ ]Ty))
mor-end-der {Δ = Δ , B} {δ , u} (dδ , du , _) = du

{- The syntactic contextual category -}

ObS : ℕ → Set
ObS n = DCtx n // ObEquiv

MorS : ℕ → ℕ → Set
MorS n m = DMor n m // MorEquiv

∂₀S : {n m : ℕ} → MorS n m → ObS n
∂₀S = //-rec (λ δ → proj (lhs δ)) (λ r → eq (fst (fst r)))

∂₁S : {n m : ℕ} → MorS n m → ObS m
∂₁S = //-rec (λ δ → proj (rhs δ)) (λ r → eq (snd (fst r)))

idS : (n : ℕ) → ObS n → MorS n n
idS n = //-rec (λ Γ → proj (dmor Γ Γ (idMor n) (idMorDerivable (der Γ)))) (λ {r → eq ((r , r) , MorRefl (idMorDerivable (CtxEqCtx1 r)))})

id₀S : (n : ℕ) (X : ObS n) → ∂₀S (idS n X) ≡ X
id₀S n = //-elimP (λ Γ → refl)

id₁S : (n : ℕ) (X : ObS n) → ∂₁S (idS n X) ≡ X
id₁S n = //-elimP (λ Γ → refl)

compS-//-u : (g : DMor m k) (f : DMor n m) (_ : ∂₁S (proj f) ≡ ∂₀S (proj g)) → DMor n k
compS-//-u (dmor Δ Θ θ dθ) (dmor Γ Δ' δ dδ) p = dmor Γ Θ (θ [ δ ]Mor) (SubstMor dθ (ConvMor dδ (CtxRefl (der Γ)) (reflect p)))

compS-// : (g : DMor m k) (f : DMor n m) (_ : ∂₁S (proj f) ≡ ∂₀S (proj g)) → MorS n k
compS-// g f p = proj (compS-//-u g f p)

compS-eq : (g g' : DMor m k) (r : g ≃ g') (f f' : DMor n m) (r' : f ≃ f') (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj f') ≡ ∂₀S (proj g')) → compS-// g f p ≡ compS-// g' f' q
compS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ') ((dΓ= , dΔ=) , dδ=) (dmor (Γ'' , dΓ'') (Δ'' , dΔ'') δ'' dδ'') (dmor (Γ''' , dΓ''') (Δ''' , dΔ''') δ''' dδ''') ((dΓ''= , dΔ''=) ,  dδ''=) p q =
  eq ((dΓ''= , dΔ=) , SubstMorFullEq (ConvMor dδ' (CtxSymm (CtxTran (reflect p) dΓ=)) (CtxSymm dΔ=)) (ConvMorEq dδ= (CtxSymm (CtxTran (reflect p) (CtxRefl dΓ))) (CtxRefl dΔ)) dδ'' dδ''=)


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

ftS-//-u : {n : ℕ} → DCtx (suc n) → DCtx n
ftS-//-u Γ = (ctx2 Γ , derctx2 Γ)

ftS-// : {n : ℕ} → DCtx (suc n) → ObS n
ftS-// Γ = proj (ftS-//-u Γ)

ftS-eq : {Γ Γ' : DCtx (suc n)} → ⊢ ctx Γ == ctx Γ' → ftS-// Γ ≡ ftS-// Γ'
ftS-eq {Γ = (_ , _) , _} {(_ , _) , _} r = eq (fst r)

ftS : {n : ℕ} → ObS (suc n) → ObS n
ftS = //-rec ftS-// (λ {Γ} {Γ'} rΓ → ftS-eq {Γ = Γ} {Γ' = Γ'} rΓ)

ppS-// : (X : DCtx (suc n)) → MorS (suc n) n
ppS-// {n = n} Γd@((Γ , A), (dΓ , dA)) = proj (dmor Γd (Γ , dΓ) (weakenMor (idMor n)) (WeakMor A (idMorDerivable dΓ) dA))

ppS-eq : {X X' : DCtx (suc n)} (_ : X ≃ X') → ppS-// X ≡ ppS-// X'
ppS-eq {X = (Γ , A), (dΓ , dA)} {(Γ' , A'), (dΓ' , dA')} (dΓ= , dA=) = eq (((dΓ= , dA=) , dΓ=) , (MorRefl (WeakMor A (idMorDerivable dΓ) dA)))

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
ptmorS = //-rec (λ Γ → proj (dmor Γ (◇ , tt) ◇ (der Γ , tt))) (λ {a} r → eq ((r , tt) , der a ,tt))

ptmor₀S : (X : ObS n) → ∂₀S (ptmorS X) ≡ X
ptmor₀S = //-elimP (λ Γ → refl)

ptmor₁S : (X : ObS n) → ∂₁S (ptmorS X) ≡ ptS
ptmor₁S = //-elimP (λ Γ → refl)

ptmor-uniqueS-// : (X : DCtx n) (f : DMor n 0) (p : ∂₀S (proj f) ≡ proj X) (q : ∂₁S (proj f) ≡ ptS) → proj f ≡ ptmorS (proj X)
ptmor-uniqueS-// X (dmor Γ (◇ , tt) ◇ (dΓ , tt)) p q = eq ((reflect p , tt) , dΓ ,tt)

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

starS-//-uc : (f : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj f) ≡ ftS (proj X)) → Ctx (suc m)
starS-//-uc f B p = (Γ , ty2 B [ δ ]Ty)  where
  Γ = ctx (lhs f)
  δ = mor f

starS-//-ud : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → ⊢ starS-//-uc f X p
starS-//-ud (dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) ((Δ , B) , (dΔ , dB)) p = (dΓ , (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p))))

starS-//-u : (f : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj f) ≡ ftS (proj X)) → DCtx (suc m)
starS-//-u f X p = (starS-//-uc f X p , starS-//-ud f X p)

starS-// : (f : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj f) ≡ ftS (proj X)) → ObS (suc m)
starS-// f X p = proj (starS-//-u f X p)

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
                         (λ {a} {b} r → starS-eq f f (ref f) a b r))
          (λ {a} {b} r → //-elimP-PiP (λ X → starS-eq a b r X X (ref X)))

qqS-// : (f : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj f) ≡ ftS (proj X)) → MorS (suc m) (suc n)
qqS-// f X p = proj (dmor (starS-//-u f X p) X (weakenMor (mor f) , var last) (qqS-//-der f X p)) where

  qqS-//-der : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → ctx (starS-//-u f X p) ⊢ (weakenMor (mor f) , var last) ∷> ctx X
  qqS-//-der f@(dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) X@((Δ , A) , (dΔ , dA)) p = (WeakMor _ (ConvMor dδ (CtxRefl dΓ) (reflect p)) (SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflect p))) , aux , dA)  where

    aux : Derivable ((Γ , (A [ δ ]Ty)) ⊢ var last :> (A [ weakenMor δ ]Ty))
    aux = congTm (weaken[]Ty A δ last) refl (VarLast (SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflect p)))) 


qqS-eq : (f g : DMor m n) (r : f ≃ g) (Γ Δ : DCtx (suc n)) (r' : Γ ≃ Δ) (p : ∂₁S (proj f) ≡ ftS (proj Γ)) (q : ∂₁S (proj g) ≡ ftS (proj Δ)) → qqS-// f Γ p ≡ qqS-// g Δ q
qqS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ') ((dΓ= , dΔ=) , dδ=) ((Γ'' , A) , (dΓ'' , dA)) ((Δ'' , B) , (dΔ'' , dB)) (dΓ''= , dA , dB , dA= , dA=') p q = eq (((( dΓ= , SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflect p)) , SubstTy dB (ConvMor dδ' (CtxRefl dΓ') (reflect q)) , SubstTyFullEq dB (ConvMor dδ (CtxRefl dΓ) (CtxTran dΔ= (reflect q))) (ConvTyEq dA= dΓ''=) (ConvMorEq dδ= (CtxRefl dΓ) (CtxTran dΔ= (reflect q))) , SubstTyFullEq dB (ConvMor dδ dΓ= (CtxTran dΔ= (reflect q))) (ConvTyEq dA= dΓ''=) (ConvMorEq dδ= dΓ= (CtxTran dΔ= (reflect q))) ) , ( dΓ''= , dA , dB , dA= , dA=')) , (WeakMorEq _ (ConvMorEq dδ= (CtxRefl dΓ) (reflect p)) (SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflect p))) ,∷ congTmRefl (weakenDerLast dA (ConvMor dδ (CtxRefl dΓ) (reflect p))) refl , dA)))

qqS : (f : MorS m n) (X : ObS (suc n)) (_ : ∂₁S f ≡ ftS X) → MorS (suc m) (suc n)
qqS {n = n} {m = m} =
  //-elim-PiS
    (λ f → //-elim-PiP (qqS-// f)
                       (λ r → qqS-eq f f (ref f) _ _ r))
    (λ {f} {f'} r → //-elimP-PiP (λ X → qqS-eq f f' r X X (ref X)))


qq₀S-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → ∂₀S (qqS (proj f) (proj X) p) ≡ starS (proj f) (proj X) p
qq₀S-// f X@((Δ , A) , (dΔ , dA)) p = refl

qq₀S : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → ∂₀S (qqS f X p) ≡ starS f X p
qq₀S = //-elimP (λ f → //-elimP (qq₀S-// f))

qq₁S-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → ∂₁S (qqS (proj f) (proj X) p) ≡ proj X
qq₁S-// f X@((Δ , A) , (dΔ , dA)) p = refl

qq₁S : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → ∂₁S (qqS f X p) ≡ X
qq₁S = //-elimP (λ f → //-elimP (qq₁S-// f))

ssS-//-u : (f : DMor m (suc n)) → DMor m (suc m)
ssS-//-u (dmor Γd Δd δu dδu) = dmor Γd ((ctx Γd , ty2 Δd [ mor-init δu ]Ty) , (der Γd , SubstTy (ty2der Δd) (mor-init-der dδu))) (idMor _ , mor-end δu) (idMor+ (der Γd) (mor-end-der dδu))

ssS-// : (f : DMor m (suc n)) → MorS m (suc m)
ssS-// f = proj (ssS-//-u f)

ssS-eq : {f f' : DMor m (suc n)} (_ : f ≃ f') → ssS-// f ≡ ssS-// f'
ssS-eq {m = m} {f@(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du))} {f'@(dmor (Γ' , dΓ') ((Δ' , B'), (dΔ' , dB')) (δ' , u') (dδ' , du'))} p@((dΓ= , (dΔ= , dB , dB' , dB= , dB=')) , (dδ= ,∷ du= , _))
  = eq {a = ssS-//-u f} {b = ssS-//-u f'} ((dΓ= , (dΓ= , SubstTy dB dδ , SubstTy dB' dδ' ,  SubstTyFullEq (ConvTy dB' (CtxSymm dΔ=)) dδ dB= dδ= , SubstTyFullEq (ConvTy dB' (CtxSymm dΔ=)) (ConvMor dδ dΓ= (CtxRefl dΔ)) dB= (ConvMorEq dδ= dΓ= (CtxRefl dΔ)))) , (idMor+= dΓ du=))

ssS : (f : MorS m (suc n)) → MorS m (suc m)
ssS {n = n} = //-rec ssS-// (λ {f} {f'} r → ssS-eq {f = f} {f' = f'} r)

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
pp-qqS-// (dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) ((Δ , B), (dΔ , dB)) p = eq (((CtxRefl dΓ , SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)) , SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)) , TyRefl (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p))) , TyRefl (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)))) , CtxSymm (reflect p)) , MorSymm (congMorRefl ( ! (weaken[]Mor δ (idMor _) last) ∙ ap (λ z → weakenMor z) ([idMor]Mor δ) ∙ ! ([weakenMor]Mor δ (idMor _) ∙ ap (λ z → weakenMor z) (idMor[]Mor δ))) (SubstMor (ConvMor dδ (CtxRefl dΓ) (reflect p)) (WeakMor _ (idMorDerivable dΓ) (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)))))))

pp-qqS : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → compS (ppS X) (qqS f X p) (qq₁S f X p ∙ ! (pp₀S X)) ≡ compS f (ppS (starS f X p)) (pp₁S (starS f X p) ∙ ft-starS f X p)
pp-qqS = //-elimP (λ f → //-elimP (pp-qqS-// f))

star-idS : {n : ℕ} (X : ObS (suc n)) → starS (idS n (ftS X)) X (id₁S n (ftS X)) ≡ X
star-idS = //-elimP (λ {((Γ , A), (dΓ , dA)) → ap-irr (λ x z → proj ((Γ , x) , z)) ([idMor]Ty A)})

qq-idS : (X : ObS (suc n)) → qqS (idS n (ftS X)) X (id₁S n (ftS X)) ≡ idS (suc n) X
qq-idS {n = n} = //-elimP (λ {((Γ , A), (dΓ , dA)) → ap-irr2 (λ x z t → (proj (dmor ((Γ , x) , (dΓ , z)) ((Γ , A), (dΓ , dA)) (weakenMor' last (idMor n) , var last) t))) ([idMor]Ty A) {b = SubstTy dA (idMorDerivable dΓ)} {b' = dA} {c = (WeakMor (A [ idMor _ ]Ty) (idMorDerivable dΓ) (SubstTy dA (idMorDerivable dΓ))) , (congTm (weaken[]Ty A (idMor n) last) refl (VarLast (congTy (! ([idMor]Ty _)) dA))) , dA} {c' = (WeakMor A (idMorDerivable dΓ) dA , congTm (ap weakenTy (! ([idMor]Ty A)) ∙ weaken[]Ty A (idMor n) last) refl (VarLast dA) , dA)}})

star-compS-// : (g : DMor m k) (f : DMor n m) (X : DCtx (suc k)) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj g) ≡ ftS (proj X)) → starS (compS (proj g) (proj f) p) (proj X) (comp₁S (proj g) (proj f) p ∙ q) ≡ starS (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q))
star-compS-// (dmor Δd@(Δ , dΔ) Θd θ dθ) (dmor Γd@(Γ , dΓ) Δd'@(Δ' , dΔ') δ dδ) ((Γ' , A), (dΓ' , dA)) p q =  ap-irr (λ x z → proj ((Γ , x), z)) (! ([]Ty-assoc δ θ A))

star-compS : (g : MorS m k) (f : MorS n m) (X : ObS (suc k)) (p : ∂₁S f ≡ ∂₀S g) (q : ∂₁S g ≡ ftS X) → starS (compS g f p) X (comp₁S g f p ∙ q) ≡ starS f (starS g X q) (p ∙ ! (ft-starS g X q))
star-compS = //-elimP (λ g → //-elimP (λ f → //-elimP (star-compS-// g f)))


qq-compS-// : (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (X : DCtx (suc k)) (q : ∂₁S (proj g) ≡ ftS (proj X)) → qqS (compS (proj g) (proj f) p) (proj X) (comp₁S (proj g) (proj f) p ∙ q) ≡ compS (qqS (proj g) (proj X) q) (qqS (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q))) (qq₁S (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q)) ∙ ! (qq₀S (proj g) (proj X) q))
qq-compS-// (dmor Δd@(Δ , dΔ) Θd θ dθ) (dmor Γd@(Γ , dΓ) Δd'@(Δ' , dΔ') δ dδ) p ((Γ' , A), (dΓ' , dA)) q = eq (((CtxRefl dΓ ,, congTyRefl (SubstTy dA (SubstMor (ConvMor dθ (CtxSymm (reflect p)) (reflect q)) dδ)) (! ([]Ty-assoc δ θ A))) , (CtxRefl dΓ' ,, TyRefl dA)) , (congMorRefl (weaken[]Mor _ _ _ ∙ ! (weakenMorInsert _ _ _)) (WeakMor _ (SubstMor (ConvMor dθ (CtxSymm (reflect p)) (reflect q)) dδ) (SubstTy dA (SubstMor (ConvMor dθ (CtxSymm (reflect p)) (reflect q)) dδ))) ,∷ TmRefl (weakenDerLast dA (SubstMor (ConvMor dθ (CtxSymm (reflect p)) (reflect q)) dδ)) , dA))

qq-compS : (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) (X : ObS (suc k)) (q : ∂₁S g ≡ ftS X) → qqS (compS g f p) X (comp₁S g f p ∙ q) ≡ compS (qqS g X q) (qqS f (starS g X q) (p ∙ ! (ft-starS g X q))) (qq₁S f (starS g X q) (p ∙ ! (ft-starS g X q)) ∙ ! (qq₀S g X q))
qq-compS = //-elimP (λ g → //-elimP (λ f p → //-elimP λ X → qq-compS-// g f p X))


ss-ppS-// : {m n : ℕ} (f : DMor m (suc n)) → compS (ppS (starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f))))) (ssS (proj f)) (ss₁S (proj f) ∙ ! (pp₀S (starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))))) ≡ idS m (∂₀S (proj f))
ss-ppS-// (dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = eq (((CtxRefl dΓ) , (CtxRefl dΓ)) , MorSymm (congMorRefl (! (weakenMorInsert (idMor _) (idMor _) u ∙ idMor[]Mor (idMor _))) (idMorDerivable dΓ)))

ss-ppS : {m n : ℕ} (f : MorS m (suc n)) → compS (ppS (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f)))) (ssS f) (ss₁S f ∙ ! (pp₀S (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))))) ≡ idS m (∂₀S f)
ss-ppS {m} {n} = //-elimP (ss-ppS-// {m} {n})

ss-qqS-// : {m n : ℕ} (f : DMor m (suc n)) → (proj f) ≡ compS (qqS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))) (ssS (proj f)) (ss₁S (proj f) ∙ ! (qq₀S (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))))
ss-qqS-// (dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du , _)) = eq ((CtxRefl dΓ , CtxRefl dΔ , dB , dB , (TyRefl dB) , (TyRefl dB)) , (congMorRefl (! (weakenMorInsert _ (idMor _) u ∙ [idMor]Mor _ ∙ weakenMorInsert _ δ u ∙ idMor[]Mor δ)) dδ) ,∷ TmRefl du , dB)

ss-qqS : {m n : ℕ} (f : MorS m (suc n)) → f ≡ compS (qqS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))) (ssS f) (ss₁S f ∙ ! (qq₀S (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))))
ss-qqS = //-elimP ss-qqS-//

ss-compS-// : {m n k : ℕ} (U : DCtx (suc k)) (g : DMor n k) (f : DMor m (suc n)) (g₁ : ∂₁S (proj g) ≡ ftS (proj U)) (f₁ : ∂₁S (proj f) ≡ starS (proj g) (proj U) g₁) {-g₀ : ∂₀ g ≡ ft (∂₁ f)-} → ssS (proj f) ≡ ssS (compS (qqS (proj g) (proj U) g₁) (proj f) (! (qq₀S (proj g) (proj U) g₁ ∙ ! f₁)))
ss-compS-// U@((Θ' , C), (dΘ' , dC)) g@(dmor (Δ' , dΔ') (Θ , dΘ) θ dθ) f@(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du , _)) g₁ f₁ =  eq (((CtxRefl dΓ) , CtxRefl dΓ , SubstTy dB dδ , TyEqTy1 dΓ (SubstTyMorEq dC (ConvMor (congMor refl refl (! (weakenMorInsert θ δ u)) (SubstMor dθ (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁))))) (CtxRefl dΓ) (reflect g₁)) (congMorRefl (weakenMorInsert θ δ u) (ConvMor (congMor refl refl (! (weakenMorInsert θ δ u)) (SubstMor dθ (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁))))) (CtxRefl dΓ) (reflect g₁)))) , TyTran (SubstTy (SubstTy (ConvTy dC (CtxSymm (reflect g₁))) dθ) (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁)))) (SubstTyEq (fst (snd (snd (snd (reflect f₁))))) dδ ) (congTyRefl (SubstTy (SubstTy dC (ConvMor dθ (CtxRefl dΔ') (reflect g₁))) (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁)))) ([]Ty-assoc δ θ C ∙ ap (λ z → C [ z ]Ty) (! (weakenMorInsert θ δ u)))) , TyTran (SubstTy (SubstTy (ConvTy dC (CtxSymm (reflect g₁))) dθ) (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁)))) (SubstTyEq (fst (snd (snd (snd (reflect f₁))))) dδ ) (congTyRefl (SubstTy (SubstTy dC (ConvMor dθ (CtxRefl dΔ') (reflect g₁))) (ConvMor dδ (CtxRefl dΓ) (fst (reflect f₁)))) ([]Ty-assoc δ θ C ∙ ap (λ z → C [ z ]Ty) (! (weakenMorInsert θ δ u))))) , congMorRefl refl (idMorDerivable dΓ) ,∷ congTmRefl (congTm (! ([idMor]Ty (B [ δ ]Ty))) refl du) refl , SubstTy dB dδ)

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

module S = M synCCat
open StructuredCCat

is-sectionS : (u : MorS n (suc n)) → Prop
is-sectionS u = compS (ppS (∂₁S u)) u (! (pp₀S (∂₁S u))) ≡ idS _ (∂₀S u)

sectionS-eq : {Γ Δ : Ctx n} {dΓ : ⊢ Γ} {A : TyExpr n} {dΔ : ⊢ Δ} {dA : Derivable (Δ ⊢ A)} {δ : Mor n n} {dδ : Γ ⊢ δ ∷> Δ} {u : TmExpr n} {du : Derivable (Γ ⊢ u :> A [ δ ]Ty)}
            → is-sectionS (proj (dmor (Γ , dΓ) ((Δ , A), (dΔ , dA)) (δ , u) (dδ , du , dA)))
            → Γ ⊢ δ == idMor n ∷> Δ
sectionS-eq us with reflect us
... | ((_ , dΔ=) , dδ=) = congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor _) refl dδ=

sectionS-eq-ctx : {Γ Δ : Ctx n} {dΓ : ⊢ Γ} {A : TyExpr n} {dΔ : ⊢ Δ} {dA : Derivable (Δ ⊢ A)} {δ : Mor n n} {dδ : Γ ⊢ δ ∷> Δ} {u : TmExpr n} {du : Derivable (Γ ⊢ u :> A [ δ ]Ty)}
            → is-sectionS (proj (dmor (Γ , dΓ) ((Δ , A), (dΔ , dA)) (δ , u) (dδ , du , dA)))
            → ⊢ Δ == Γ
sectionS-eq-ctx us with reflect us
... | ((_ , dΔ=) , dδ=) = dΔ=

is-section₀S : {u : MorS n (suc n)} (us : is-sectionS u) → ∂₀S u ≡ ftS (∂₁S u)
is-section₀S {u = u} us = ! (id₁S _ (∂₀S u)) ∙ ap ∂₁S (! us) ∙ comp₁S (ppS (∂₁S u)) u (! (pp₀S _)) ∙ pp₁S (∂₁S u)


record DTy {n : ℕ} (Γ : DCtx n) : Set where
  constructor _,ft_
  field
    Ty-Ctx   : DCtx (suc n)
    Ty-ft    : ftS (proj Ty-Ctx) ≡ proj Γ
open DTy public

toS : {Γ : DCtx n} → DTy Γ → S.Ty (proj Γ)
toS (A ,ft A=) = (proj A M.,ft A=)

record DTm {n : ℕ} (Γ : DCtx n) (A : DTy Γ) : Set where
  field
    Tm-Mor : DMor n (suc n)
    Tmₛ    : is-sectionS (proj Tm-Mor)
    Tm₁    : ∂₁S (proj Tm-Mor) ≡ S.Ty-Ctx (toS A)
  Tm₀ :  ∂₀S (proj Tm-Mor) ≡ proj Γ
  Tm₀ = is-section₀S {u = proj Tm-Mor} Tmₛ ∙ ap ftS Tm₁ ∙ Ty-ft A
open DTm public

toSTm : {Γ : DCtx n} {A : DTy Γ} (u : DTm Γ A) → S.Tm (proj Γ) (toS A)
S.Tm-Mor (toSTm u) = proj (Tm-Mor u)
S.Tmₛ (toSTm u) = Tmₛ u
S.Tm₁ (toSTm u) = Tm₁ u


ty : {Γ : DCtx n} (A : DTy Γ) → TyExpr n
ty {Γ = (Γ , dΓ)} A = ty2 (Ty-Ctx A)

tyder : {Γ : DCtx n} (A : DTy Γ) → Derivable (ctx Γ ⊢ ty A)
tyder {Γ = (Γ , dΓ)} (((ΓA , A) , (dΓA , dA)) ,ft p) = ConvTy dA (reflect p)

tyder2 : {Γ : DCtx n} (A : DTy Γ) (B : DTy (Ty-Ctx A)) → Derivable ((ctx Γ , ty A) ⊢ ty B)
tyder2 (((ΓA , A) , (dΓA , dA)) ,ft p) (((ΓB , B) , (dΓB , dB)) ,ft q) = ConvTy (ConvTy dB (reflect q)) (reflect p ,, TyRefl dA)

tm2 : {Γ : DCtx n} {A : DTy Γ} (u : DMor n (suc n)) → TmExpr n
tm2 δ = mor-end (mor δ)

tm : {Γ : DCtx n} {A : DTy Γ} (u : DTm Γ A) → TmExpr n
tm {Γ = Γ} {A} u = tm2 {Γ = Γ} {A} (Tm-Mor u)

ttt : (Γ : DCtx n) (A : DTy Γ) → ⊢ ctx (Ty-Ctx A) == (ctx Γ , ty A)
ttt (Γ , dΓ) (((Γ' , A) , (dΓ' , dA)) ,ft p) = (reflect p ,, TyRefl dA)

morLemma : {Γ : DCtx n} {A : DTy Γ} (a : DTm Γ A) → ctx Γ ⊢ mor (Tm-Mor a) == (idMor n , tm a) ∷> (ctx Γ , ty A)
morLemma {Γ = Γ} {A = A'} aa@record { Tm-Mor = dmor (Δ , dΔ) ((Δ' , A) , (dΔ' , dA)) (δ , a) (dδ , da , _)  ; Tmₛ = aₛ ; Tm₁ = a₁ }
  = ConvMorEq {δ = δ , a} {δ' = idMor _ , a} (sectionS-eq {dA = dA} {dδ = dδ} {du = da} aₛ ,∷ TmRefl da , dA) (reflect (Tm₀ aa)) (CtxTran (reflect a₁) (ttt Γ A'))

tmder : {Γ : DCtx n} {A : DTy Γ} (u : DTm Γ A) → Derivable (ctx Γ ⊢ tm u :> ty A)
tmder {A = ((ΓA , A) , (dΓA , dA)) ,ft p} uu@(record { Tm-Mor = (dmor (Γ , dΓ) ((Γ' , A') , (dΓ' , dA')) (δ , u) (dδ , du , _)) ; Tmₛ = uₛ ; Tm₁ = u₁ }) =
  congTm ([idMor]Ty A) refl (ConvTm2 du (reflect (Tm₀ uu)) (SubstTyMorEq2 (fst (snd (snd (snd (reflect u₁))))) (congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor _) refl (snd (reflect uₛ)))))

tmder2 : {Γ : DCtx n} (A : DTy Γ) {B : DTy (Ty-Ctx A)} (u : DTm (Ty-Ctx A) B) → Derivable ((ctx Γ , ty A) ⊢ tm u :> ty B)
tmder2 {Γ = Γ} A u = ConvTm (tmder u) (ttt Γ A)

PathOver-DTy : {Γ : DCtx n} {P : (A : ObS (suc n)) (A-ft : ftS A ≡ proj Γ) → Set}
               {a a' : ObS (suc n)} {p : a ≡R a'} {u : (A-ft : ftS a ≡ proj Γ) → P a A-ft} {u' : (A-ft : ftS a' ≡ proj Γ) → P a' A-ft}
               → ({y : ftS a ≡ proj Γ} {y' : ftS a' ≡ proj Γ} → PathOver (λ ab → P (S.Ty-Ctx ab) (S.Ty-ft ab)) (S.Ty=R p) (u y) (u' y'))
               → PathOver (λ A → (A-ft : ftS A ≡ proj Γ) → P A A-ft) p u u'
PathOver-DTy {p = reflR} f = PathOver-refl-to (funextP (λ y → PathOver-refl-from f))

PathOver-DTm : {Γ : DCtx n} {A : DTy Γ} {P : (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ S.Ty-Ctx (toS A)) → Set}
               {u u' : MorS n (suc n)} {p : u ≡R u'} {k : (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ S.Ty-Ctx (toS A)) → P u uₛ u₁} {k' : (uₛ : is-sectionS u') (u₁ : ∂₁S u' ≡ S.Ty-Ctx (toS A)) → P u' uₛ u₁}
               → ({uₛ : is-sectionS u} {u'ₛ : is-sectionS u'} {u₁ : ∂₁S u ≡ S.Ty-Ctx (toS A)} {u'₁ : ∂₁S u' ≡ S.Ty-Ctx (toS A)} → PathOver (λ (abc : S.Tm (proj Γ) (toS A)) → P (S.Tm-Mor abc) (S.Tmₛ abc) (S.Tm₁ abc)) (S.Tm=R p) (k uₛ u₁) (k' u'ₛ u'₁))
               → PathOver (λ u → (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ S.Ty-Ctx (toS A)) → P u uₛ u₁) p k k'
PathOver-DTm {p = reflR} f = PathOver-refl-to (funextP (λ uₛ → funextP (λ u₁ → PathOver-refl-from f)))

PathOver-STy : {X : Set} {f : X → ObS n} {B : (x : X) (A : S.Ty (f x)) → Set}
               {x x' : X} {p : x ≡R x'}
               {u : (A : S.Ty (f x)) → B x A} {v : (A' : S.Ty (f x')) → B x' A'}
               → ((A : S.Ty (f x)) {q : f x ≡ f x'} → PathOver (λ ab → B (fst ab) (S.Ty-Ctx A S.,ft snd ab)) (pair≡P p) (u A) (v (S.Ty-Ctx A S.,ft (S.Ty-ft A ∙ q))))
               → PathOver (λ z → (A : S.Ty (f z)) → B z A) p u v
PathOver-STy {p = reflR} h = PathOver-refl-to (funext (λ x → PathOver-refl-from (h x {q = refl})))

PathOver-STm : {X : Set} {f : X → ObS n} {g : (x : X) → S.Ty (f x)} {B : (x : X) (A : S.Tm (f x) (g x)) → Set}
               {x x' : X} {p : x ≡R x'}
               {a : (A : S.Tm (f x) (g x)) → B x A} {b : (A' : S.Tm (f x') (g x')) → B x' A'}
               → ((u : S.Tm (f x) (g x)) {q : S.Ty-Ctx (g x) ≡ S.Ty-Ctx (g x')} → PathOver (λ ab → B (fst ab) (record { Tm-Mor = S.Tm-Mor u ; Tmₛ = S.Tmₛ u ; Tm₁ = S.Tm₁ u ∙ snd ab })) (pair≡P p {b = refl} {b' = q}) (a u) (b (record { Tm-Mor = S.Tm-Mor u ; Tmₛ = S.Tmₛ u ; Tm₁ = S.Tm₁ u ∙ q })))
               → PathOver (λ z → (A : S.Tm (f z) (g z)) → B z A) p a b
PathOver-STm {p = reflR} h = PathOver-refl-to (funext (λ x → PathOver-refl-from (h x)))

//-elim-Ty : {Γ : DCtx n}
             {P : S.Ty (proj Γ) → Set}
           → (proj* : (A : DTy Γ) → P (toS A))
           → (eq* : {A A' : DTy Γ} (A= : Ty-Ctx A ≃ Ty-Ctx A') → PathOver P (S.Ty=R (eqR A=)) (proj* A) (proj* A'))
           → (A : S.Ty (proj Γ)) → P A
//-elim-Ty {Γ = Γ} {P} proj* eq* (A S.,ft A-ft) = //-elim-Ty-aux A A-ft  where

  //-elim-Ty-aux : (A : ObS (suc _)) (A-ft : ftS A ≡ proj Γ) → P (A S.,ft A-ft)
  //-elim-Ty-aux = //-elim (λ A' A-ft' → proj* (A' ,ft A-ft')) (λ A= → PathOver-DTy (eq* A=))

//-elimP-Ty : {Γ : DCtx n}
              {P : S.Ty (proj Γ) → Prop}
            → (proj* : (A : DTy Γ) → P (toS A))
            → (A : S.Ty (proj Γ)) → P A
//-elimP-Ty {Γ = Γ} {P} proj* (A S.,ft A-ft) = //-elimP-Ty-aux A A-ft  where

  //-elimP-Ty-aux : (A : ObS (suc _)) (A-ft : ftS A ≡ proj Γ) → P (A S.,ft A-ft)
  //-elimP-Ty-aux = //-elimP (λ A' A-ft' → proj* (A' ,ft A-ft'))

//-elim-Tm : {Γ : DCtx n}
             {A : DTy Γ}
             {P : S.Tm (proj Γ) (toS A) → Set}
           → (proj* : (u : DTm Γ A) → P (toSTm u))
           → (eq* : {u u' : DTm Γ A} (u= : Tm-Mor u ≃ Tm-Mor u') → PathOver P (S.Tm=R (eqR u=)) (proj* u) (proj* u'))
           → (u : S.Tm (proj Γ) (toS A)) → P u
//-elim-Tm {Γ = Γ} {A = A} {P = P} proj* eq* record { Tm-Mor = u ; Tmₛ = uₛ ; Tm₁ = u₁ } = //-elim-Tm-aux u uₛ u₁  where

  //-elim-Tm-aux : (u : MorS _ (suc _)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ S.Ty-Ctx (toS A)) → P (record {Tm-Mor = u ; Tmₛ = uₛ ; Tm₁ = u₁})
  //-elim-Tm-aux = //-elim (λ u uₛ u₁ → proj* (record { Tm-Mor = u ; Tmₛ = uₛ ; Tm₁ = u₁ })) (λ u= → PathOver-DTm (eq* u=))

//-elimP-Tm : {Γ : DCtx n}
              {A : DTy Γ}
              {P : S.Tm (proj Γ) (toS A) → Prop}
            → (proj* : (u : DTm Γ A) → P (toSTm u))
            → (u : S.Tm (proj Γ) (toS A)) → P u
//-elimP-Tm {Γ = Γ} {A} {P} proj* u = //-elimP-Tm-aux (S.Tm-Mor u) (S.Tmₛ u) (S.Tm₁ u)  where

  //-elimP-Tm-aux : (u : MorS _ (suc _)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ S.Ty-Ctx (toS A)) → P (record {Tm-Mor = u ; Tmₛ = uₛ ; Tm₁ = u₁})
  //-elimP-Tm-aux = //-elimP (λ u uₛ u₁ → proj* (record { Tm-Mor = u ; Tmₛ = uₛ ; Tm₁ = u₁ }))

//-elimP-CtxMor : {Δ : DCtx m} {Γ : DCtx n}
                  {P : S.CtxMor (proj Γ) (proj Δ) → Prop}
                → (proj* : (u : DMor n m) (u₀ : proj (lhs u) ≡ proj Γ) (u₁ : proj (rhs u) ≡ proj Δ) → P (proj u S.,Mor u₀ , u₁))
                → (g : S.CtxMor (proj Γ) (proj Δ)) → P g
//-elimP-CtxMor {Δ = Δ} {Γ = Γ} {P} proj* (u S.,Mor u₀ , u₁) = aux u u₀ u₁ where

  aux : (u : MorS _ _) (u₀ : ∂₀S u ≡ proj Γ) (u₁ : ∂₁S u ≡ proj Δ) → P (u S.,Mor u₀ , u₁)
  aux = //-elimP proj*

toS= : {X : Set} {x x' : X} {f : X → ObS n} {p : x ≡R x'} {A : S.Ty (f x)} {B : S.Ty (f x')} → S.Ty-Ctx A ≡ S.Ty-Ctx B  → PathOver (λ z → S.Ty (f z)) p A B
toS= {p = reflR} refl = reflo

toSTm= : {X : Set} {x x' : X} {f : X → ObS n} {g : (x : X) → S.Ty (f x)} {p : x ≡R x'} {u : S.Tm (f x) (g x)} {v : S.Tm (f x') (g x')} → S.Tm-Mor u ≡ S.Tm-Mor v  → PathOver (λ z → S.Tm (f z) (g z)) p u v
toSTm= {p = reflR} refl = reflo

DCtxRefl : (Γ : DCtx n) → ⊢ ctx Γ == ctx Γ
DCtxRefl (Γ , dΓ) = CtxRefl dΓ

DTyRefl : {Γ : DCtx n} (A : DTy Γ) → Derivable (ctx Γ ⊢ ty A == ty A)
DTyRefl A = TyRefl (tyder A)

DTyRefl2 : {Γ : DCtx n} (A : DTy Γ) (B : DTy (Ty-Ctx A)) → Derivable ((ctx Γ , ty A) ⊢ ty B == ty B)
DTyRefl2 A B = TyRefl (tyder2 A B)

DTmRefl : {Γ : DCtx n} {A : DTy Γ} (u : DTm Γ A) → Derivable (ctx Γ ⊢ tm u == tm u :> ty A)
DTmRefl u = TmRefl (tmder u)

DTmRefl2 : {Γ : DCtx n} (A : DTy Γ) {B : DTy (Ty-Ctx A)} (u : DTm (Ty-Ctx A) B) → Derivable ((ctx Γ , ty A) ⊢ tm u == tm u :> ty B)
DTmRefl2 A u = ConvTmEq (DTmRefl u) (ttt _ A)

ctx-Ty-Ctx : {Γ : DCtx n} (A : DTy Γ) → ⊢ ctx (Ty-Ctx A) == (ctx Γ , ty2 (Ty-Ctx A))
ctx-Ty-Ctx (((ΓA , A) , (dΓA , dA)) ,ft A=) = reflect A= ,, TyRefl dA

lemma : {Γ : DCtx n} (A A' : DTy Γ) (A= : Ty-Ctx A ≃ Ty-Ctx A')
       → Derivable (ctx Γ ⊢ ty A == ty A')
lemma (((ΓA , A) , (dΓA , dA)) ,ft A-ft) (((ΓA' , A') , (dΓA' , dA')) ,ft A'-ft) (ΓA= , _ , _ , A= , _) = ConvTyEq A= (reflect A-ft)

lemma2 : {Γ : DCtx n} (A : DTy Γ) (B B' : DTy (Ty-Ctx A))
        → Ty-Ctx B ≃ Ty-Ctx B'
        → Derivable ((ctx Γ , ty A) ⊢ ty B == ty B')
lemma2 {Γ = Γ} A (((ΓB , B) , (dΓB , dB)) ,ft B-ft) (((ΓB' , B') , (dΓB' , dB')) ,ft B'-ft) (ΓB= , _ , _ , B= , _) = ConvTyEq B= (reflect {b = (ctx Γ , ty2 (Ty-Ctx A)) , (der Γ , tyder A)} (B-ft ∙ eq (ctx-Ty-Ctx A)))

lemmaTm : {Γ : DCtx n} {A : DTy Γ} (u u' : DTm Γ A)
          → Tm-Mor u ≃ Tm-Mor u'
          → Derivable (ctx Γ ⊢ tm u == tm u' :> ty A)
lemmaTm {A = ((ΓA , A) , (dΓA , dA)) ,ft p} u@record { Tm-Mor = dmor (_ , dΓ) ((Γu , Au) , (dΓu , dAu)) (_ , _) _ ; Tmₛ = uₛ ; Tm₁ = u₁ } u'@record { Tm-Mor = dmor _ (_ , _) (_ , _) _ ; Tmₛ = _ ; Tm₁ = _ } (_ , (_ ,∷ u= , _))
  = ConvTmEq2 u= (reflect (Tm₀ u)) (congTyEq refl ([idMor]Ty A) (SubstTyMorEq2 (fst (snd (snd (snd (reflect u₁))))) (congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor _) refl (snd (reflect uₛ)))))

lemmaTm2 : {Γ : DCtx n} (A : DTy Γ) {B : DTy (Ty-Ctx A)} (u u' : DTm (Ty-Ctx A) B)
          → Tm-Mor u ≃ Tm-Mor u'
          → Derivable ((ctx Γ , ty A) ⊢ tm u == tm u' :> ty B)
lemmaTm2 A u u' ru
  = ConvTmEq (lemmaTm u u' ru) (ttt _ A)

toDTm : {Γ : DCtx n} {A : DTy Γ} {A' : TyExpr n} (u : TmExpr n) (du : Derivable (ctx Γ ⊢ u :> A')) → Derivable (ctx Γ ⊢ A' == ty A) → DTm Γ A
Tm-Mor (toDTm {Γ = Γ} {A} u du p) = dmor Γ ((ctx Γ , ty A) , (der Γ , tyder A)) (idMor _ , u) (idMor+ (der Γ) (Conv (TyEqTy1 (der Γ) p) du p))
Tmₛ (toDTm {Γ = Γ} {A} u du p) = eq ((DCtxRefl Γ , DCtxRefl Γ) , MorSymm (congMorRefl (! (weakenMorInsert _ _ _ ∙ idMor[]Mor _)) (idMorDerivable (der Γ))))
Tm₁ (toDTm {Γ = Γ} {A} u du p) = eq (CtxSymm (ttt Γ A))

repackageTy : {Γ Γ' : DCtx n} → DTy Γ → proj Γ ≡ proj Γ' → DTy Γ'
Ty-Ctx (repackageTy A p) = Ty-Ctx A
Ty-ft (repackageTy A p) = Ty-ft A ∙ p

repackageTm : {Γ Γ' : DCtx n} {A : DTy Γ} {A' : DTy Γ'} → DTm Γ A → S.Ty-Ctx (toS A) ≡ S.Ty-Ctx (toS A') → DTm Γ' A'
Tm-Mor (repackageTm u p) = Tm-Mor u
Tmₛ (repackageTm u p) = Tmₛ u
Tm₁ (repackageTm u p) = Tm₁ u ∙ p

substDTy : {Γ : DCtx n} {A : DTy Γ} (B : DTy (Ty-Ctx A)) (u : DTm Γ A) → DTy Γ
substDTy {Γ = Γ} B u = ((ctx (lhs (Tm-Mor u)) , (ty B) [ mor (Tm-Mor u) ]Ty) , (der (lhs (Tm-Mor u)) , SubstTy (tyder B) (ConvMor (morDer (Tm-Mor u)) (DCtxRefl (lhs (Tm-Mor u))) (reflect (Tm₁ u))))) ,ft (Tm₀ u)

substDTy-red : {Γ : DCtx n} {A : DTy Γ} (B : DTy (Ty-Ctx A)) (u : DTm Γ A) → Derivable (ctx Γ ⊢ substTy (ty B) (tm u) == ty (substDTy B u))
substDTy-red {Γ = Γ} {A = A@(((_ , _) , (_ , dA)) ,ft _)} B uu@record { Tm-Mor = dmor (Δ , dΔ) ((Γ' , X) , (dΓ' , dX)) (δ , u) (dδ , du , _) ; Tmₛ = uₛ ; Tm₁ = u₁ }
  = TySymm (SubstTyMorEq (tyder2 A B) (ConvMor dδ (reflect (Tm₀ uu)) (CtxTran (fst (reflect u₁)) (reflect (Ty-ft A))) , ConvTm2 du (reflect (Tm₀ uu)) (SubstTyEq (fst (snd (snd (snd (reflect u₁))))) dδ) , ConvTy dA (reflect (Ty-ft A))) ((ConvMorEq (sectionS-eq {dA = dX} {dδ = dδ} {du = du} uₛ) (reflect (Tm₀ uu)) (CtxTran (fst (reflect u₁)) (reflect (Ty-ft A)))) ,∷ TmRefl (ConvTm2 du (reflect (Tm₀ uu)) (SubstTyEq (fst (snd (snd (snd (reflect u₁))))) dδ)) , ConvTy dA (reflect (Ty-ft A))))



PiStrS-//  : (Γ : DCtx n) (A : DTy Γ) (B : DTy (Ty-Ctx A)) → DTy Γ
PiStrS-// (Γ , dΓ) A B = ((Γ , pi (ty A) (ty B)) , (dΓ , Pi (tyder A) (tyder2 A B))) ,ft refl

PiStrS-eq : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' →
            {A A' : TyExpr n} → Derivable (Γ ⊢ A == A') →
            {B B' : TyExpr (suc n)} → Derivable ((Γ , A) ⊢ B == B')
            → ⊢ (Γ , pi A B) == (Γ' , pi A' B')
PiStrS-eq dΓ= dA= dB= = (dΓ= ,, PiCong (TyEqTy1 (CtxEqCtx1 dΓ=) dA=) dA= dB=)

PiStrS : (Γ : ObS n) (A : S.Ty Γ) (B : S.Ty (S.Ty-Ctx A)) → S.Ty Γ
PiStrS = //-elim (λ Γ → //-elim-Ty (λ A → //-elim-Ty (λ B  → toS  (PiStrS-// Γ A B))
                                                     (λ {B} {B'} B= → toS= (eq (PiStrS-eq (DCtxRefl Γ) (DTyRefl A) (lemma2 A B B' B=)))))
                                   (λ {A} {A'} A= → PathOver-STy (//-elimP-Ty (λ B → toS= (eq (PiStrS-eq (DCtxRefl Γ) (lemma A A' A=) (DTyRefl2 A B)))))))
                 (λ Γ= → PathOver-STy (//-elimP-Ty (λ A → PathOver-STy (//-elimP-Ty (λ B → toS= (eq (PiStrS-eq Γ= (DTyRefl A) (DTyRefl2 A B))))))))


appStrS-//  : (Γ : DCtx n) (A : DTy Γ) (B : DTy (Ty-Ctx A)) (f : DTm Γ (PiStrS-// Γ A B)) (a : DTm Γ A) → DTm Γ (substDTy B a)
appStrS-// (Γ , dΓ) A B f a = toDTm (app (ty A) (ty B) (tm f) (tm a)) (App (tyder A) (tyder2 A B) (tmder f) (tmder a)) (substDTy-red B a)

appStrS-eq : (Γ Γ' : DCtx n) → ⊢ ctx Γ == ctx Γ'
           → (A : DTy Γ) (A' : DTy Γ') → Derivable (ctx Γ ⊢ ty A == ty A')
           → (B : DTy (Ty-Ctx A)) (B' : DTy (Ty-Ctx A')) → Derivable ((ctx Γ , ty A) ⊢ ty B == ty B')
           → (f : DTm Γ (PiStrS-// Γ A B)) (f' : DTm Γ' (PiStrS-// Γ' A' B')) → Derivable (ctx Γ ⊢ tm f == tm f' :> pi (ty A) (ty B))
           → (a : DTm Γ A) (a' : DTm Γ' A') → Derivable (ctx Γ ⊢ tm a == tm a' :> ty A)
           → _≡_ {A = MorS n (suc n)} (proj (Tm-Mor (appStrS-// Γ A B f a))) (proj (Tm-Mor (appStrS-// Γ' A' B' f' a')))
appStrS-eq Γ _ Γ= A _ A= B _ B= _ _ f= a a' a= = eq ((Γ= , (Γ= ,, SubstTyMorEq2 B= (MorTran (morLemma a) (MorTran (idMor+= (der Γ) a=) (MorSymm (ConvMorEq (morLemma a') (CtxSymm Γ=) (CtxSymm (Γ= ,, A=))))))))
           , (idMor+= (der Γ) (ConvTmEq2 (AppCong (tyder A) A= B= f= a=) (DCtxRefl Γ) (SubstTyMorEq (tyder2 A B) (idMor+ (der Γ) (tmder a)) (MorSymm (morLemma a))))))

appStrS-5 : (Γ : DCtx n) (A : DTy Γ) (B : DTy (Ty-Ctx A)) (f : DTm Γ (PiStrS-// Γ A B)) (a : DTm Γ A) → S.Tm (proj Γ) (S.substTy (toS B) (toSTm a))
appStrS-5 Γ A B f a = toSTm (appStrS-// Γ A B f a)

appStrS-5= : (Γ : DCtx n) (A : DTy Γ) (B : DTy (Ty-Ctx A)) (f : DTm Γ (PiStrS-// Γ A B)) (a a' : DTm Γ A) (ra : Tm-Mor a ≃ Tm-Mor a')
           → PathOver (λ (z : S.Tm (proj Γ) (toS A)) → S.Tm (proj Γ) (S.substTy (toS B) z)) {a = toSTm a} {a' = toSTm a'} (S.Tm=R (eqR ra)) (appStrS-5 Γ A B f a) (appStrS-5 Γ A B f a')
appStrS-5= Γ A B f a a' ra = toSTm= (appStrS-eq Γ Γ (DCtxRefl Γ) A A (DTyRefl A) B B (DTyRefl2 A B) f f (DTmRefl f) a a' (lemmaTm a a' ra))

appStrS-4 : (Γ : DCtx n) (A : DTy Γ) (B : DTy (Ty-Ctx A)) (f : DTm Γ (PiStrS-// Γ A B)) (a : S.Tm (proj Γ) (toS A)) → S.Tm (proj Γ) (S.substTy (toS B) a)
appStrS-4 Γ A B f = //-elim-Tm (appStrS-5 Γ A B f) (λ {a} {a'} ra → appStrS-5= Γ A B f a a' ra)

appStrS-4= : (Γ : DCtx n) (A : DTy Γ) (B : DTy (Ty-Ctx A)) (f f' : DTm Γ (PiStrS-// Γ A B)) (rf : Tm-Mor f ≃ Tm-Mor f') → PathOver (λ f → (a : S.Tm (proj Γ) (toS A)) → S.Tm (proj Γ) (S.substTy (toS B) a)) {a = toSTm f} {a' = toSTm f'} (S.Tm=R (eqR rf)) (appStrS-4 Γ A B f) (appStrS-4 Γ A B f')
appStrS-4= Γ A B f f' rf = PathOver-STm (//-elimP-Tm (λ a → toSTm= (appStrS-eq Γ Γ (DCtxRefl Γ) A A (DTyRefl A) B B (DTyRefl2 A B) f f' (lemmaTm f f' rf) a a (DTmRefl a))))

appStrS-3 : (Γ : DCtx n) (A : DTy Γ) (B : DTy (Ty-Ctx A)) (f : S.Tm (proj Γ) (PiStrS (proj Γ) (toS A) (toS B))) (a : S.Tm (proj Γ) (toS A)) → S.Tm (proj Γ) (S.substTy (toS B) a)
appStrS-3 Γ A B = //-elim-Tm (appStrS-4 Γ A B) (λ {f} {f'} rf → appStrS-4= Γ A B f f' rf)

appStrS-3= : (Γ : DCtx n) (A : DTy Γ) (B B' : DTy (Ty-Ctx A)) (rB : Ty-Ctx B ≃ Ty-Ctx B') → PathOver (λ B → (f : S.Tm (proj Γ) (PiStrS (proj Γ) (toS A) B)) (a : S.Tm (proj Γ) (toS A)) → S.Tm (proj Γ) (S.substTy B a)) {a = toS B} {a' = toS B'} (S.Ty=R (eqR rB)) (appStrS-3 Γ A B) (appStrS-3 Γ A B')
appStrS-3= Γ A B B' rB = PathOver-STm (//-elimP-Tm (λ f {fq} → PathOver-STm (//-elimP-Tm (λ a → toSTm= (appStrS-eq Γ Γ (DCtxRefl Γ) A A (DTyRefl A) B B' (lemma2 A B B' rB) f (repackageTm f fq) (DTmRefl f) a a (DTmRefl a))))))

appStrS-2 : (Γ : DCtx n) (A : DTy Γ) (B : S.Ty (S.Ty-Ctx (toS A))) (f : S.Tm (proj Γ) (PiStrS (proj Γ) (toS A) B)) (a : S.Tm (proj Γ) (toS A)) → S.Tm (proj Γ) (S.substTy B a)
appStrS-2 Γ A = //-elim-Ty (appStrS-3 Γ A) (λ {B} {B'} rB → appStrS-3= Γ A B B' rB)

appStrS-2= : (Γ : DCtx n) (A A' : DTy Γ) (rA : Ty-Ctx A ≃ Ty-Ctx A') → PathOver (λ A → (B : S.Ty (S.Ty-Ctx A)) (f : S.Tm (proj Γ) (PiStrS (proj Γ) A B)) (a : S.Tm (proj Γ) A) → S.Tm (proj Γ) (S.substTy B a)) {a = toS A} {a' = toS A'} (S.Ty=R (eqR rA)) (appStrS-2 Γ A) (appStrS-2 Γ A')
appStrS-2= Γ A A' rA = PathOver-STy (//-elimP-Ty (λ B {Bq} → PathOver-STm (//-elimP-Tm (λ f {fq} → PathOver-STm (//-elimP-Tm (λ a {aq} →
                           toSTm= (appStrS-eq Γ Γ (DCtxRefl Γ) A A' (lemma A A' rA) B (repackageTy B Bq) (DTyRefl2 A B) f (repackageTm f fq) (DTmRefl f) a (repackageTm a aq) (DTmRefl a))))))))

appStrS-1 : (Γ : DCtx n) (A : S.Ty (proj Γ)) (B : S.Ty (S.Ty-Ctx A)) (f : S.Tm (proj Γ) (PiStrS (proj Γ) A B)) (a : S.Tm (proj Γ) A) → S.Tm (proj Γ) (S.substTy B a)
appStrS-1 Γ = //-elim-Ty (appStrS-2 Γ) (λ {A} {A'} rA → appStrS-2= Γ A A' rA)

appStrS-1= : (Γ Γ' : DCtx n) (rΓ : Γ ≃ Γ') → PathOver (λ Γ → (A : S.Ty Γ) (B : S.Ty (S.Ty-Ctx A)) (f : S.Tm Γ (PiStrS Γ A B)) (a : S.Tm Γ A) → S.Tm Γ (S.substTy B a)) {a = proj Γ} {a' = proj Γ'} (eqR rΓ) (appStrS-1 Γ) (appStrS-1 Γ')
appStrS-1= Γ Γ' rΓ = PathOver-STy (//-elimP-Ty (λ A {Aq} → PathOver-STy (//-elimP-Ty (λ B {Bq} → PathOver-STm (//-elimP-Tm (λ f {fq} → PathOver-STm (//-elimP-Tm (λ a {aq} →
                       toSTm= (appStrS-eq Γ Γ' rΓ A (repackageTy A Aq) (DTyRefl A) B B (DTyRefl2 A B) f (repackageTm f fq) (DTmRefl f) a (repackageTm a aq) (DTmRefl a))))))))))

appStrS : (Γ : ObS n) (A : S.Ty Γ) (B : S.Ty (S.Ty-Ctx A)) (f : S.Tm Γ (PiStrS Γ A B)) (a : S.Tm Γ A) → S.Tm Γ (S.substTy B a)
appStrS = //-elim appStrS-1 (λ {Γ} {Γ'} rΓ → appStrS-1= Γ Γ' rΓ)



lamStrS-//  : (Γ : DCtx n) (A : DTy Γ) (B : DTy (Ty-Ctx A)) (u : DTm (Ty-Ctx A) B) → DTm Γ (PiStrS-// Γ A B)
lamStrS-// (Γ , dΓ) A B u = toDTm (lam (ty A) (ty B) (tm u)) (Lam (tyder A) (tyder2 A B) (tmder2 A u)) (TyRefl (Pi (tyder A) (tyder2 A B)))

lamStrS-eq : (Γ Γ' : DCtx n) → ⊢ ctx Γ == ctx Γ'
           → (A : DTy Γ) (A' : DTy Γ') → Derivable (ctx Γ ⊢ ty A == ty A')
           → (B : DTy (Ty-Ctx A)) (B' : DTy (Ty-Ctx A')) → Derivable ((ctx Γ , ty A) ⊢ ty B == ty B')
           → (u : DTm (Ty-Ctx A) B) (u' : DTm (Ty-Ctx A') B') → Derivable ((ctx Γ , ty A) ⊢ tm u == tm u' :> ty B)
           → _≡_ {A = MorS n (suc n)} (proj (Tm-Mor (lamStrS-// Γ A B u))) (proj (Tm-Mor (lamStrS-// Γ' A' B' u')))
lamStrS-eq Γ _ Γ= A _ A= _ _ B= _ _ u= = eq ((Γ= , (Γ= ,, PiCong (tyder A) A= B=)) , idMor+= (der Γ) (LamCong (tyder A) A= B= u=))

lamStrS-4 : (Γ : DCtx n) (A : DTy Γ) (B : DTy (Ty-Ctx A)) (u : DTm (Ty-Ctx A) B) → S.Tm (proj Γ) (PiStrS (proj Γ) (toS A) (toS B))
lamStrS-4 Γ A B u = toSTm (lamStrS-// Γ A B u)

lamStrS-4= : (Γ : DCtx n) (A : DTy Γ) (B : DTy (Ty-Ctx A)) (u u' : DTm (Ty-Ctx A) B) (ru : Tm-Mor u ≃ Tm-Mor u') → PathOver (λ u → S.Tm (proj Γ) (PiStrS (proj Γ) (toS A) (toS B))) {a = toSTm u} {a' = toSTm u'} (S.Tm=R (eqR ru)) (lamStrS-4 Γ A B u) (lamStrS-4 Γ A B u')
lamStrS-4= Γ A B u u' ru = toSTm= (lamStrS-eq Γ Γ (DCtxRefl Γ) A A (DTyRefl A) B B (DTyRefl2 A B) u u' (lemmaTm2 A u u' ru))

lamStrS-3 : (Γ : DCtx n) (A : DTy Γ) (B : DTy (Ty-Ctx A)) (u : S.Tm (S.Ty-Ctx (toS A)) (toS B)) → S.Tm (proj Γ) (PiStrS (proj Γ) (toS A) (toS B))
lamStrS-3 Γ A B = //-elim-Tm (lamStrS-4 Γ A B) (λ {u} {u'} ru → lamStrS-4= Γ A B u u' ru)

lamStrS-3= : (Γ : DCtx n) (A : DTy Γ) (B B' : DTy (Ty-Ctx A)) (rB : Ty-Ctx B ≃ Ty-Ctx B') → PathOver (λ B → (u : S.Tm (S.Ty-Ctx (toS A)) B) → S.Tm (proj Γ) (PiStrS (proj Γ) (toS A) B)) {a = toS B} {a' = toS B'} (S.Ty=R (eqR rB)) (lamStrS-3 Γ A B) (lamStrS-3 Γ A B')
lamStrS-3= Γ A B B' rB = PathOver-STm (//-elimP-Tm (λ u {uq} → toSTm= (lamStrS-eq Γ Γ (DCtxRefl Γ) A A (DTyRefl A) B B' (lemma2 A B B' rB) u (repackageTm u uq) (DTmRefl2 A u))))

lamStrS-2 : (Γ : DCtx n) (A : DTy Γ) (B : S.Ty (S.Ty-Ctx (toS A))) (u : S.Tm (S.Ty-Ctx (toS A)) B) → S.Tm (proj Γ) (PiStrS (proj Γ) (toS A) B)
lamStrS-2 Γ A = //-elim-Ty (lamStrS-3 Γ A) (λ {B} {B'} rB → lamStrS-3= Γ A B B' rB)

lamStrS-2= : (Γ : DCtx n) (A A' : DTy Γ) (rA : Ty-Ctx A ≃ Ty-Ctx A') → PathOver (λ A → (B : S.Ty (S.Ty-Ctx A)) (u : S.Tm (S.Ty-Ctx A) B) → S.Tm (proj Γ) (PiStrS (proj Γ) A B)) {a = toS A} {a' = toS A'} (S.Ty=R (eqR rA)) (lamStrS-2 Γ A) (lamStrS-2 Γ A')
lamStrS-2= Γ A A' rA = PathOver-STy (//-elimP-Ty (λ B {Bq} → PathOver-STm (//-elimP-Tm (λ u {uq} → toSTm= (lamStrS-eq Γ Γ (DCtxRefl Γ) A A' (lemma A A' rA) B (repackageTy B Bq) (DTyRefl2 A B) u (repackageTm u uq) (DTmRefl2 A u))))))

lamStrS-1 : (Γ : DCtx n) (A : S.Ty (proj Γ)) (B : S.Ty (S.Ty-Ctx A)) (u : S.Tm (S.Ty-Ctx A) B) → S.Tm (proj Γ) (PiStrS (proj Γ) A B)
lamStrS-1 Γ = //-elim-Ty (lamStrS-2 Γ) (λ {A} {A'} rA → lamStrS-2= Γ A A' rA)

lamStrS-1= : (Γ Γ' : DCtx n) (rΓ : Γ ≃ Γ') → PathOver (λ Γ → (A : S.Ty Γ) (B : S.Ty (S.Ty-Ctx A)) (u : S.Tm (S.Ty-Ctx A) B) → S.Tm Γ (PiStrS Γ A B)) {a = proj Γ} {a' = proj Γ'} (eqR rΓ) (lamStrS-1 Γ) (lamStrS-1 Γ')
lamStrS-1= Γ Γ' rΓ = PathOver-STy (//-elimP-Ty (λ A {Aq} → PathOver-STy (//-elimP-Ty (λ B {Bq} → PathOver-STm (//-elimP-Tm (λ u {uq} → toSTm= (lamStrS-eq Γ Γ' rΓ A (repackageTy A Aq) (DTyRefl A) B (repackageTy B Bq) (DTyRefl2 A B) u (repackageTm u uq) (DTmRefl2 A u))))))))

lamStrS : (Γ : ObS n) (A : S.Ty Γ) (B : S.Ty (S.Ty-Ctx A)) (u : S.Tm (S.Ty-Ctx A) B) → S.Tm Γ (PiStrS Γ A B)
lamStrS = //-elim lamStrS-1 (λ {Γ} {Γ'} rΓ → lamStrS-1= Γ Γ' rΓ)



UUStrS-// : (Γ : DCtx n) → DTy Γ
UUStrS-// (Γ , dΓ) = (((Γ , uu) , (dΓ , UU)) ,ft refl)

UUStrS-eq : {Γ Γ' : Ctx n} → ⊢ Γ == Γ'
            → ⊢ (Γ , uu) == (Γ' , uu)
UUStrS-eq dΓ= = dΓ= ,, UUCong

UUStrS : (Γ : ObS n) → S.Ty Γ
UUStrS = //-elim (λ Γ → toS (UUStrS-// Γ))
                 (λ Γ= → toS= (eq (UUStrS-eq Γ=)))


ElStrS-//  : (Γ : DCtx n) (v : DTm Γ (UUStrS-// Γ)) → DTy Γ
ElStrS-// (Γ , dΓ) v = ((Γ , el (tm v)) , (dΓ , El (tmder v))) ,ft refl

ElStrS-eq : {Γ Γ' : Ctx n} → ⊢ Γ == Γ'
          → {v v' : TmExpr n} → Derivable (Γ ⊢ v == v' :> uu)
          → {w : _} {w' : _}
          → _≡_ {A = ObS (suc n)} (proj ((Γ , el v) , w)) (proj ((Γ' , el v') , w'))
ElStrS-eq Γ= v= = eq (Γ= ,, ElCong v=)

ElStrS : (Γ : ObS n) (v : S.Tm Γ (UUStrS Γ)) → S.Ty Γ
ElStrS = //-elim (λ Γ → //-elim-Tm (λ v → toS (ElStrS-// Γ v))
                                   (λ {v} {v'} rv → toS= (ElStrS-eq (DCtxRefl Γ) (lemmaTm v v' rv ))))
                 (λ rΓ → PathOver-STm (//-elimP-Tm (λ v → toS= (ElStrS-eq rΓ (DTmRefl v)))))


PiStrNatS : (Δ : ObS m) (A : S.Ty Δ) (B : S.Ty (S.Ty-Ctx A)) (Γ : ObS n) (g : S.CtxMor Γ Δ) → PiStrS Γ (S.starTy g A) (S.starTy (S.qqCtxMor g A) B) ≡ S.starTy g (PiStrS Δ A B)
PiStrNatS = //-elimP (λ Δ → //-elimP-Ty (λ A → //-elimP-Ty (λ B → //-elimP (λ Γ → //-elimP-CtxMor (λ g g₀ g₁
              → S.Ty= (eq (CtxSymm (reflect g₀) ,, TyRefl (SubstTy (Pi (tyder A) (tyder2 A B)) (ConvMor (morDer g) (reflect g₀) (reflect g₁))))))))))

ap-lam : {A A' : TyExpr n} (A= : A ≡ A') {B B' : TyExpr (suc n)} (B= : B ≡ B') {u u' : TmExpr (suc n)} (u= : u ≡ u') → lam A B u ≡ lam A' B' u'
ap-lam refl refl refl = refl

mor-end-lemma : (θ : Mor m (suc k)) {δ : Mor n m} → mor-end θ [ δ ]Tm ≡ mor-end (θ [ δ ]Mor)
mor-end-lemma (θ , u) = refl

lamStrNatS : (Δ : ObS m) (A : S.Ty Δ) (B : S.Ty (S.Ty-Ctx A)) (u : S.Tm (S.Ty-Ctx A) B) (Γ : ObS n) (g : S.CtxMor Γ Δ)
           → lamStrS Γ (S.starTy g A) (S.starTy (S.qqCtxMor g A) B) (S.starTm (S.qqCtxMor g A) u) ≡ S.cong!Tm (PiStrNatS Δ A B Γ g) (S.starTm g (lamStrS Δ A B u))
lamStrNatS = //-elimP (λ Δ → //-elimP-Ty (λ A → //-elimP-Ty (λ B → //-elimP-Tm (λ u → //-elimP (λ Γ → //-elimP-CtxMor (λ g g₀ g₁
               → S.Tm= (eq ((CtxSymm (reflect g₀) , (CtxSymm (reflect g₀) ,, SubstTyMorEq (Pi (tyder A) (tyder2 A B)) (betterg g g₀ g₁) (congMorRefl (! (idMor[]Mor (mor g))) (betterg g g₀ g₁))))
                           , idMor+=' (der Γ) (congTmRefl (SubstTm {u = lam (ty A) (ty B) (tm u)} (Lam (tyder A) (tyder2 A B) (tmder2 A u)) (betterg g g₀ g₁)) (ap-lam refl refl (mor-end-lemma (mor (Tm-Mor u)))))))))))))  where

           betterg : {Γ : DCtx n} {Δ : DCtx m} (g : DMor n m) (g₀ : _≡_ {A = ObS n} (proj (lhs g)) (proj Γ)) (g₁ : _≡_ {A = ObS m} (proj (rhs g)) (proj Δ)) → ctx Γ ⊢ mor g ∷> ctx Δ
           betterg g g₀ g₁ = ConvMor (morDer g) (reflect g₀) (reflect g₁)

projMor : {Γ : DCtx n} {Δ : DCtx m} (g : DMor n m) (g₀ : _≡_ {A = ObS n} (proj (lhs g)) (proj Γ)) (g₁ : _≡_ {A = ObS m} (proj (rhs g)) (proj Δ)) → S.CtxMor (proj Γ) (proj Δ)
projMor g g₀ g₁ = (proj g M.,Mor g₀ , g₁)

appStrNatS-// : (Δ : DCtx m) (A : DTy Δ) (B : DTy (Ty-Ctx A)) (f : DTm Δ (PiStrS-// Δ A B)) (a : DTm Δ A) (Γ : DCtx n) (g : DMor n m) (g₀ : _≡_ {A = ObS n} (proj (lhs g)) (proj Γ)) (g₁ : _≡_ {A = ObS m} (proj (rhs g)) (proj Δ))
           → appStrS (proj Γ) (S.starTy (projMor g g₀ g₁) (toS A)) (S.starTy (S.qqCtxMor (projMor g g₀ g₁) (toS A)) (toS B)) (S.cong!Tm (PiStrNatS (proj Δ) (toS A) (toS B) (proj Γ) (projMor g g₀ g₁)) (S.starTm (projMor g g₀ g₁) {A = PiStrS (proj Δ) (toS A) (toS B)} (toSTm f))) (S.starTm (projMor g g₀ g₁) {A = toS A} (toSTm a)) ≡ S.cong!Tm (S.substTyqqCtx (toS A) (toS B) (toSTm a) (projMor g g₀ g₁)) (S.starTm (projMor g g₀ g₁) (appStrS (proj Δ) (toS A) (toS B) (toSTm f) (toSTm a)))
appStrNatS-// Δ A B f@record { Tm-Mor = dmor _ (_ , _) (_ , _) _ ; Tmₛ = fₛ ; Tm₁ = f₁ } a@record { Tm-Mor = dmor _ (_ , _) (_ , _) _ ; Tmₛ = aₛ ; Tm₁ = a₁ } Γ g g₀ g₁
  = S.Tm= (eq ((CtxSymm (reflect g₀) , (CtxSymm (reflect g₀) ,, {!!}))
              , MorRefl (idMor+ (der Γ) (congTm (! (substCommutes[]Ty _ _ _)) refl (SubstTm (App (tyder A) (tyder2 A B) (tmder f) (tmder a)) (ConvMor (morDer g) (reflect g₀) (reflect g₁)))))))

appStrNatS : (Δ : ObS m) (A : S.Ty Δ) (B : S.Ty (S.Ty-Ctx A)) (f : S.Tm Δ (PiStrS Δ A B)) (a : S.Tm Δ A) (Γ : ObS n) (g : S.CtxMor Γ Δ)
           → appStrS Γ (S.starTy g A) (S.starTy (S.qqCtxMor g A) B) (S.cong!Tm (PiStrNatS Δ A B Γ g) (S.starTm g f)) (S.starTm g a)
             ≡ S.cong!Tm (S.substTyqqCtx A B a g) (S.starTm g (appStrS Δ A B f a))
appStrNatS = //-elimP (λ Δ → //-elimP-Ty (λ A → //-elimP-Ty (λ B → //-elimP-Tm (λ f → //-elimP-Tm (λ a → //-elimP (λ Γ → //-elimP-CtxMor (λ g g₀ g₁
               → appStrNatS-// Δ A B f a Γ g g₀ g₁)))))))
               -- S.Tm= (eq ((CtxSymm (reflect g₀) , (CtxSymm (reflect g₀) ,, {!SubstTyMorEq ? (ConvMor (morDer g) (reflect g₀) (reflect g₁)) (congMorRefl (! (idMor[]Mor (mor g))) (ConvMor (morDer g) (reflect g₀) (reflect g₁)))!}))
               --             , {!!})))))))))

-- UUStrNatS : (Δ : ObS m) {-(i : ℕ)-} (Γ : ObS n) (g : S.CtxMor Γ Δ) → UUStrS {-i-} Γ ≡ S.starTy g (UUStrS {-i-} Δ)
-- UUStrNatS = //-elimP (λ Δ → //-elimP (λ Γ → //-elimP-CtxMor (λ g g₀ g₁ → S.Ty= (eq (CtxSymm (reflect g₀) ,, UUCong)))))

-- ElStrNatS : (Δ : ObS m) {-(i : ℕ)-} (v : S.Tm Δ (UUStrS Δ {-i-})) (Γ : ObS n) (g : S.CtxMor Γ Δ) → ElStrS Γ (S.cong!Tm (UUStrNatS Δ Γ g) (S.starTm g v)) ≡ S.starTy g (ElStrS Δ v)
-- ElStrNatS = //-elimP (λ Δ → //-elimP-Tm (λ v → //-elimP (λ Γ → //-elimP-CtxMor (λ g g₀ g₁ → S.Ty= (eq (CtxSymm (reflect g₀) ,, {!!}))))))

-- betaStrS : (Γ : ObS n) (A : S.Ty Γ) (B : S.Ty (S.Ty-Ctx A)) (u : S.Tm (S.Ty-Ctx A) B) (a : S.Tm Γ A) → appStrS Γ A B (lamStrS Γ A B u) a ≡ S.substTm u a
-- betaStrS = //-elimP (λ Γ → //-elimP-Ty (λ A → //-elimP-Ty (λ B → //-elimP-Tm (λ u → //-elimP-Tm (λ a
--              → S.Tm= (eq ((reflect (! (Tm₀ a)) , (reflect (! (Tm₀ a)) ,, {!!}))
--                          , idMor+= (der Γ) {!Beta!})))))))


-- -- strSynCCat : StructuredCCat

-- -- ccat strSynCCat = synCCat

-- -- PiStr strSynCCat = PiStrS
-- -- lamStr strSynCCat = lamStrS
-- -- appStr strSynCCat = appStrS
-- -- UUStr strSynCCat = UUStrS
-- -- ElStr strSynCCat = ElStrS

-- -- PiStrNat strSynCCat g = PiStrNatS _ _ _ _ g
-- -- lamStrNat strSynCCat g = lamStrNatS _ _ _ _ _ g
-- -- appStrNat strSynCCat g = appStrNatS _ _ _ _ _ _ g
-- -- UUStrNat strSynCCat g = UUStrNatS _ _ g
-- -- ElStrNat strSynCCat g = ElStrNatS _ _ _ g

-- -- betaStr strSynCCat = betaStrS _ _ _ _ _
