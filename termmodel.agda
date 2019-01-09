{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import typetheory
open import syntx
open import rules
open import contextualcat
open import quotients

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


DCtx= : {n : ℕ} → {Γ Γ' : Ctx n} → {w₁ : _} → {w₂ : _} → Γ ≡ Γ' → proj {R = ObEquiv} (Γ , w₁) ≡ proj (Γ' , w₂)
DCtx= CtxEq = ap-irr (λ x y → proj (x , y)) CtxEq


ap3-irr : {A C D E : Set} {F : A → Prop} {G : C → Prop} {B : A → C → E → Prop} (h : (a : A) (f : F a) (c : C) (g : G c) (e : E) (b : B a c e) → D) {a a' : A} (p : a ≡ a') {f : F a} {f' : F a'} {c c' : C} (q : c ≡ c') {g : G c} {g' : G c'} {e e' : E} (r : e ≡ e') {b : B a c e} {b' : B a' c' e'} → h a f c g e b ≡ h a' f' c' g' e' b'
ap3-irr f refl refl refl = refl

DMor= : {m n : ℕ} → {Γ Γ' : Ctx m} {w₁ : _} {w₂ : _} {Δ Δ' : Ctx n} {w₃ : _} {w₄ : _} {δ δ' : Mor m n} {w₅ : _} {w₆ : _} → Γ ≡ Γ' → Δ ≡ Δ' → δ ≡ δ' → proj {R = MorEquiv} (dmor (Γ , w₁) (Δ , w₃) δ w₅) ≡ proj (dmor (Γ' , w₂) (Δ' , w₄) δ' w₆)
DMor= {m} {n} lhsEq rhsEq morEq = ap3-irr (λ Γ p Δ q δ r → proj (dmor (Γ , p) (Δ , q) δ r)) lhsEq rhsEq morEq

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
ftS-// ((Γ , A), (dΓ , dA)) = (Γ , dΓ)

ftS-eq : {Γ Γ' : DCtx (suc n)} → ⊢ ctx Γ == ctx Γ' → proj {R = ObEquiv} (ftS-// Γ) ≡ proj (ftS-// Γ')
ftS-eq {Γ = (_ , _) , _} {(_ , _) , _} r = eq (fst r)

ftS : {n : ℕ} → ObS (suc n) → ObS n
ftS = //-rec (λ X → proj (ftS-// X)) ftS-eq

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
starS {m = m} {n = n} =
  //-elim-PiS (λ f → //-elim-PiP (starS-// f)
                         (λ r → starS-eq f f (ref f) _ _ r))
          (λ r → //-elimP-PiP (λ X → starS-eq _ _ r X X (ref X)))

qqS-// : (f : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj f) ≡ ftS (proj X)) → MorS (suc m) (suc n)
qqS-// f@(dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) X@((Δ , A) , (dΔ , dA)) p = proj (dmor (starS-//-u f X p) X (weakenMor δ , var last) ((WeakMor _ (ConvMor dδ (CtxRefl dΓ) (reflect p))) , weakenDerLast dA (ConvMor dδ (CtxRefl dΓ) (reflect p))))


qqS-eq : (f g : DMor m n) (r : f ≃ g) (Γ Δ : DCtx (suc n)) (r' : Γ ≃ Δ) (p : ∂₁S (proj f) ≡ ftS (proj Γ)) (q : ∂₁S (proj g) ≡ ftS (proj Δ)) → qqS-// f Γ p ≡ qqS-// g Δ q
qqS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ') ((dΓ= , dΔ=) , dδ=) ((Γ'' , A) , (dΓ'' , dA)) ((Δ'' , B) , (dΔ'' , dB)) (dΓ''= , dA , dB , dA= , dA=') p q = eq (((( dΓ= , SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflect p)) , SubstTy dB (ConvMor dδ' (CtxRefl dΓ') (reflect q)) , SubstTyFullEq dB (ConvMor dδ (CtxRefl dΓ) (CtxTran dΔ= (reflect q))) (ConvTyEq dA= dΓ''=) (ConvMorEq dδ= (CtxRefl dΓ) (CtxTran dΔ= (reflect q))) , SubstTyFullEq dB (ConvMor dδ dΓ= (CtxTran dΔ= (reflect q))) (ConvTyEq dA= dΓ''=) (ConvMorEq dδ= dΓ= (CtxTran dΔ= (reflect q))) ) , ( dΓ''= , dA , dB , dA= , dA=')) , ( WeakMorEq _ (ConvMorEq dδ= (CtxRefl dΓ) (reflect p)) , congTmRefl (weakenDerLast dA (ConvMor dδ (CtxRefl dΓ) (reflect p))) refl)))

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
ssS-//-u {m = m} f@(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = dmor (Γ , dΓ) ((Γ , B [ δ ]Ty) , (dΓ , SubstTy dB dδ)) (idMor _ , u) (idMor+ dΓ du)

ssS-// : (f : DMor m (suc n)) → MorS m (suc m)
ssS-// f = proj (ssS-//-u f)

ssS-eq : {f f' : DMor m (suc n)} (_ : f ≃ f') → ssS-// f ≡ ssS-// f'
ssS-eq {m = m} {f = f@(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du))} {f'@(dmor (Γ' , dΓ') ((Δ' , B'), (dΔ' , dB')) (δ' , u') (dδ' , du'))} p@((dΓ= , (dΔ= , dB , dB' , dB= , dB=')) , (dδ= , du=))
  = eq {a = ssS-//-u f} {b = ssS-//-u f'} ((dΓ= , (dΓ= ,, SubstTyMorEq2 dΓ dΔ dB= dδ= )) , idMor+= dΓ du=)

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
pp-qqS-// (dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) ((Δ , B), (dΔ , dB)) p = eq (((CtxRefl dΓ , SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)) , SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)) , TyRefl (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p))) , TyRefl (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)))) , CtxSymm (reflect p)) , MorSymm (dΓ , (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflect p)))) dΔ (congMorRefl ( ! (weaken[]Mor δ (idMor _) last) ∙ ap weakenMor ([idMor]Mor δ) ∙ ! ([weakenMor]Mor δ (idMor _) ∙ ap weakenMor (idMor[]Mor δ))) (SubstMor (ConvMor dδ (CtxRefl dΓ) (reflect p)) (WeakMor _ (idMorDerivable dΓ)))))

pp-qqS : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → compS (ppS X) (qqS f X p) (qq₁S f X p ∙ ! (pp₀S X)) ≡ compS f (ppS (starS f X p)) (pp₁S (starS f X p) ∙ ft-starS f X p)
pp-qqS = //-elimP (λ f → //-elimP (pp-qqS-// f))

star-idS : {n : ℕ} (X : ObS (suc n)) → starS (idS n (ftS X)) X (id₁S n (ftS X)) ≡ X
star-idS = //-elimP (λ {((Γ , A), (dΓ , dA)) → DCtx= (ap (_,_ Γ) ([idMor]Ty A))}) --ap-irr (λ x z → proj ((Γ , x) , z)) ([idMor]Ty A)

qq-idS : (X : ObS (suc n)) → qqS (idS n (ftS X)) X (id₁S n (ftS X)) ≡ idS (suc n) X
qq-idS {n = n} = //-elimP (λ {((Γ , A), (dΓ , dA)) → DMor= (ap (_,_ Γ) ([idMor]Ty A)) refl refl}) --ap-irr2 (λ x z t → (proj (dmor ((Γ , x) , (dΓ , z)) ((Γ , A), (dΓ , dA)) (weakenMor' last (idMor n) , var last) t))) ([idMor]Ty A) {b = SubstTy dA (idMorDerivable dΓ)} {b' = dA} {c = (WeakMor (A [ idMor _ ]Ty) (idMorDerivable dΓ)) , (congTm (weaken[]Ty A (idMor n) last) refl (VarLast (congTy (! ([idMor]Ty _)) dA)))} {c' = (WeakMor A (idMorDerivable dΓ)) , (congTm (ap weakenTy (! ([idMor]Ty A)) ∙ weaken[]Ty A (idMor n) last) refl (VarLast dA))

star-compS-// : (g : DMor m k) (f : DMor n m) (X : DCtx (suc k)) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj g) ≡ ftS (proj X)) → starS (compS (proj g) (proj f) p) (proj X) (comp₁S (proj g) (proj f) p ∙ q) ≡ starS (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q))
star-compS-// (dmor Δd@(Δ , dΔ) Θd θ dθ) (dmor Γd@(Γ , dΓ) Δd'@(Δ' , dΔ') δ dδ) ((Γ' , A), (dΓ' , dA)) p q =  DCtx= (ap (_,_ Γ) (! ([]Ty-assoc _ _ _))) --ap-irr (λ x z → proj ((Γ , x), z)) (! ([]Ty-assoc δ θ A))

star-compS : (g : MorS m k) (f : MorS n m) (X : ObS (suc k)) (p : ∂₁S f ≡ ∂₀S g) (q : ∂₁S g ≡ ftS X) → starS (compS g f p) X (comp₁S g f p ∙ q) ≡ starS f (starS g X q) (p ∙ ! (ft-starS g X q))
star-compS = //-elimP (λ g → //-elimP (λ f → //-elimP (star-compS-// g f)))


qq-compS-// : (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (X : DCtx (suc k)) (q : ∂₁S (proj g) ≡ ftS (proj X)) → qqS (compS (proj g) (proj f) p) (proj X) (comp₁S (proj g) (proj f) p ∙ q) ≡ compS (qqS (proj g) (proj X) q) (qqS (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q))) (qq₁S (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q)) ∙ ! (qq₀S (proj g) (proj X) q))
qq-compS-// (dmor Δd@(Δ , dΔ) Θd θ dθ) (dmor Γd@(Γ , dΓ) Δd'@(Δ' , dΔ') δ dδ) p ((Γ' , A), (dΓ' , dA)) q = DMor= (ap (_,_ Γ) (! ([]Ty-assoc _ _ _))) refl (ap (λ z → z , var last) (weaken[]Mor _ _ _ ∙ ! (weakenMorInsert _ _ _ ))) --eq (((CtxRefl dΓ ,, congTyRefl (SubstTy dA (SubstMor (ConvMor dθ (CtxSymm (reflect p)) (reflect q)) dδ)) (! ([]Ty-assoc δ θ A))) , (CtxRefl dΓ' ,, TyRefl dA)) , (congMorRefl (weaken[]Mor _ _ _ ∙ ! (weakenMorInsert _ _ _)) (WeakMor _ (SubstMor (ConvMor dθ (CtxSymm (reflect p)) (reflect q)) dδ)) , TmRefl (weakenDerLast dA (SubstMor (ConvMor dθ (CtxSymm (reflect p)) (reflect q)) dδ))))

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
                  let (dΔf=Δg , _ , _ , dA[g]=A[δ] , _) = reflect f₁
                  in
                  eq ((CtxRefl dΘ , (CtxRefl dΘ ,, TyTran (SubstTy (SubstTy dA (ConvMor dδ (CtxSymm dΔf=Δg) (reflect g₁))) dθ) (SubstTyEq dA[g]=A[δ] dθ) (congTyEq (! ([]Ty-assoc _ _ _)) (ap (_[_]Ty A) (! (weakenMorInsert _ _ _))) (TyRefl (SubstTy dA (SubstMor (ConvMor dδ (CtxSymm dΔf=Δg) (reflect g₁)) dθ)))))) , idMor+= dΘ (TmRefl du))


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

is-section₀S : (u : MorS n (suc n)) (uₛ : is-sectionS u) {X : ObS (suc n)} (u₁ : ∂₁S u ≡ X) → ∂₀S u ≡ ftS X
is-section₀S u uₛ u₁ = ! (id₁S _ (∂₀S u)) ∙ ap ∂₁S (! uₛ) ∙ comp₁S (ppS (∂₁S u)) u (! (pp₀S _)) ∙ pp₁S (∂₁S u) ∙ ap ftS u₁


DMor-dTm : {Γ : DCtx (suc n)} (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ proj Γ) → Derivable (Ctx-Ty (ctx Γ) ⊢ Tm a :> Ty Γ)
DMor-dTm {Γ = ((Γ , A) , (dΓ , dA))} aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da)) aₛ a₁ =
           let (dΓa'=Γ , Γa'dAA , _ , Γa'dAa=A , ΓdAa=A)  = reflect a₁
               a₀ : ∂₀S (proj aa) ≡ proj (_ , dΓ)
               a₀ = is-section₀S (proj aa) aₛ a₁
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
                                   dlhsa= = (CtxTran (reflect (is-section₀S (proj aa) aₛ refl)) dΓa'=Γ)
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


piStrS-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (b : DMor (suc n) (suc (suc n))) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) → DMor n (suc n)
piStrS-// i a aₛ a₁ b bₛ b₁ =
            (dmor (lhs a)
                  ((ctx (lhs a) , uu i) , (der (lhs a) , UU))
                  ((idMor _) , (pi i (Tm a) (Tm b)))
                  (idMor+ (der (lhs a))
                          (PiUU (DMor-dTm a aₛ a₁) (DMor-dTm b bₛ b₁))))

piStrS-eq : (i : ℕ) (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (a'₁ : ∂₁S (proj a') ≡ UUStrS i (∂₀S (proj a'))) (b b' : DMor (suc n) (suc (suc n))) (rb : b ≃ b') (bₛ : is-sectionS (proj b)) (b'ₛ : is-sectionS (proj b')) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) (b'₁ : ∂₁S (proj b') ≡ UUStrS i (ElStrS i (proj a') a'ₛ a'₁))→ proj {R = MorEquiv} (piStrS-// i a aₛ a₁ b bₛ b₁) ≡ proj (piStrS-// i a' a'ₛ a'₁ b' b'ₛ b'₁)
piStrS-eq i a a' ra@((da₀=a'₀ , _) , _) aₛ a'ₛ a₁ a'₁ b b' rb bₛ b'ₛ b₁ b'₁ =
            eq ((da₀=a'₀ , (da₀=a'₀ ,, UUCong)) ,
                (idMor+= (der (lhs a))
                         (PiUUCong (DMor-dTm a aₛ a₁)
                                   (DMor-dTm= (da₀=a'₀ ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁)
                                   (DMor-dTm= ((da₀=a'₀ ,, ElCong (DMor-dTm= (da₀=a'₀ ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁)) ,, UUCong) b b' rb bₛ b'ₛ b₁ b'₁))))


piStrS : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (b : MorS (suc n) (suc (suc n))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁)) → MorS n (suc n)
piStrS i = //-elim-PiP3 (λ a aₛ a₁ → //-elim-PiP2 (λ b bₛ b₁ → proj (piStrS-// i a aₛ a₁ b bₛ b₁))
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


lamStrS-// : (B : DCtx (suc (suc n))) (u : DMor (suc n) (suc (suc n))) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) → DMor n (suc n)
lamStrS-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u uₛ u₁ =
  dmor (Γ , dΓ) ((Γ , pi A B), (dΓ , Pi dA dB)) (idMor _ , lam A B (Tm u)) (idMor+ dΓ (Lam dA dB (DMor-dTm u uₛ u₁)))

lamStrS-eq : {B B' : DCtx (suc (suc n))} (rB : B ≃ B') {u u' : DMor (suc n) (suc (suc n))} (u~u' : u ≃ u') (uₛ : is-sectionS (proj u)) (u'ₛ : is-sectionS (proj u')) (u₁ : ∂₁S (proj u) ≡ proj B) (u'₁ : ∂₁S (proj u') ≡ proj B') → proj {R = MorEquiv} (lamStrS-// B u uₛ u₁) ≡ proj (lamStrS-// B' u' u'ₛ u'₁)
lamStrS-eq {B = (((Γ , A) , B) , ((dΓ , dA) , dB))} {B' = (((Γ' , A') , B') , ((dΓ' , dA') , dB'))} rB@((dΓ= , _ , _ , dA= , _) , _ , _ , dB= , _) u~u' uₛ u'ₛ u₁ u'₁ = eq ((dΓ= , (dΓ= ,, PiCong dA dA= dB=)) , idMor+= dΓ (LamCong dA dA= dB= (DMor-dTm= rB _ _ u~u' uₛ u'ₛ u₁ u'₁))) 

lamStrS : (B : ObS (suc (suc n))) (u : MorS (suc n) (suc (suc n))) (us : is-sectionS u) (u₁ : ∂₁S u ≡ B) → MorS n (suc n)
lamStrS = //-elim-PiS (λ B → //-elim-PiP2 (λ u uₛ u₁ → proj (lamStrS-// B u uₛ u₁)) (λ ru uₛ u'ₛ → PathOver-Prop→Cst (λ u₁ u'₁ → lamStrS-eq (ref B) ru uₛ u'ₛ u₁ u'₁))) (λ rB → //-elimP (λ u → PathOver-CstPropPi λ uₛ → PathOver-Prop→Cst (λ u₁ u₁' → lamStrS-eq rB (ref u) uₛ uₛ u₁ u₁')))


lamStrₛS-// : (B : DCtx (suc (suc n))) (u : DMor (suc n) (suc (suc n))) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) → is-sectionS (proj (lamStrS-// B u uₛ u₁))
lamStrₛS-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u uₛ u₁ = eq ((CtxRefl dΓ , CtxRefl dΓ) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor _)) refl (MorRefl (idMorDerivable dΓ)))

lamStrₛS : (B : ObS (suc (suc n))) (u : MorS (suc n) (suc (suc n))) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ B) → is-sectionS (lamStrS B u uₛ u₁)
lamStrₛS = //-elimP (λ B → //-elimP (λ u uₛ u₁ → lamStrₛS-// B u uₛ u₁))


lamStr₁S-// : (B : DCtx (suc (suc n))) (u : DMor (suc n) (suc (suc n))) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) → ∂₁S (proj (lamStrS-// B u uₛ u₁)) ≡ PiStrS (proj B)
lamStr₁S-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u us u₁ = refl

lamStr₁S : (B : ObS (suc (suc n))) (u : MorS (suc n) (suc (suc n))) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ B) → ∂₁S (lamStrS B u uₛ u₁) ≡ PiStrS B
lamStr₁S = //-elimP (λ B → (//-elimP (λ u uₛ u₁ → lamStr₁S-// B u uₛ u₁)))


appStrS-// : (B : DCtx (suc (suc n))) (f : DMor n (suc n)) (fₛ : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor n (suc n)) (as : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) → DMor n (suc n)
appStrS-// (((Γ , A) , B), ((dΓ , dA) , dB)) f fₛ f₁ a aₛ a₁ = 
  (dmor (Γ , dΓ)
        ((Γ , substTy B (Tm a)) ,  (dΓ , SubstTy dB (idMor+ dΓ (DMor-dTm a aₛ a₁))))
        (idMor _ , app A B (Tm f) (Tm a))
        (idMor+ dΓ (App dA dB (DMor-dTm f fₛ f₁) (DMor-dTm a aₛ a₁))))
 
appStr-eq : (B B' : DCtx (suc (suc n))) (rB : B ≃ B') (f f' : DMor n (suc n)) (rf : f ≃ f') (fₛ : is-sectionS (proj f)) (f'ₛ : is-sectionS (proj f')) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (f₁' : ∂₁S (proj f') ≡ PiStrS (proj B')) (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (a'₁ : ∂₁S (proj a') ≡ ftS (proj B')) → proj {R = MorEquiv} (appStrS-// B f fₛ f₁ a aₛ a₁) ≡ proj (appStrS-// B' f' f'ₛ f₁' a' a'ₛ a'₁)
appStr-eq (((Γ , A) , B), ((dΓ , dA) , dB)) 
          (((Γ+ , A+) , B+), ((dΓ+ , dA+) , dB+))
          rB@((dΓ= , _ , _ , dA= , _) , _ , _ , dB= , _)
          f f' rf fₛ f'ₛ f₁ f'₁ a a' ra  aₛ a'ₛ a₁ a'₁ =
                                eq ((dΓ= , (dΓ= ,, SubstTyMorEq2 dΓ (dΓ , dA) dB= (idMor+= dΓ (DMor-dTm= (fst rB) a a' ra aₛ a'ₛ a₁ a'₁)))) ,
                                    (idMor+= dΓ (AppCong dA dA= dB= (DMor-dTm= (dΓ= ,, PiCong dA dA= dB=) f f' rf fₛ f'ₛ f₁ f'₁) (DMor-dTm= (dΓ= ,, dA=) a a' ra aₛ a'ₛ a₁ a'₁))))

appStrS : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fₛ : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) → MorS n (suc n)
appStrS =
  //-elim-PiS (λ B → //-elim-PiP2 (λ f fₛ f₁ → //-elim-PiP2 (λ a aₛ a₁ → proj (appStrS-// B f fₛ f₁ a aₛ a₁))
    (λ ra as as' → PathOver-Prop→Cst (λ a₁ a₁' → appStr-eq B B (ref B) f f (ref f) fₛ fₛ f₁ f₁ _ _ ra as as' a₁ a₁')))
    (λ rf fₛ fₛ' → PathOver-Prop→Cst (λ f₁ f₁' → funext (//-elimP (λ a → funextP (λ as → funextP (λ a₁ → appStr-eq B B (ref B) _ _ rf fₛ fₛ' f₁ f₁' a a (ref a) as as a₁ a₁)))))))
    (λ rB → //-elimP λ f → PathOver-CstPropPi (λ fₛ → PathOver-Prop→ (λ f₁ f₁' → PathOver-CstPi (//-elimP (λ a → PathOver-CstPropPi (λ as → PathOver-Prop→Cst (λ a₁ a₁' → appStr-eq _ _ rB f f (ref f) fₛ fₛ f₁ f₁' a a (ref a) as as a₁ a₁')))))))

appStrₛS-// : (B : DCtx (suc (suc n))) (f : DMor n (suc n)) (fₛ : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor n (suc n)) (as : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) → is-sectionS (appStrS (proj B) (proj f) fₛ f₁ (proj a) as a₁)
appStrₛS-// (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γf' , Af) , (dΓf' , dAf)) (δf , f) (dδf , df~)) fₛ f₁ aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) as a₁
  = eq ((CtxRefl dΓ , CtxRefl dΓ) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ idMor[]Mor _)) refl (MorRefl (idMorDerivable dΓ)))

appStrₛS : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fₛ : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) → is-sectionS (appStrS B f fₛ f₁ a as a₁)
appStrₛS = //-elimP (λ B → //-elimP (λ f fₛ f₁ → //-elimP (appStrₛS-// B f fₛ f₁)))

appStr₁S-// : (B : DCtx (suc (suc n))) (f : DMor n (suc n)) (fₛ : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) → ∂₁S (appStrS (proj B) (proj f) fₛ f₁ (proj a) aₛ a₁) ≡ starS (proj a) (proj B) a₁
appStr₁S-// (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γf' , Af) , (dΓf' , dAf)) (δf , f) (dδf , df~)) fₛ f₁ aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) aₛ a₁
  = let (dΓ= , _ , _ , daTy= , _) = reflect a₁
        dΓ=' = CtxTran (CtxSymm dΓ=) (sectionS-eq-ctx {dA = dAa} {dδ = dδa} {du = da~} aₛ)        
 in eq (dΓ=' ,, SubstTyMorEq dB (idMor+ dΓ (DMor-dTm aa aₛ a₁)) (ConvMorEq (MorSymm dΓa dΓa' (sectionS-eq {dA = dAa} {dδ = dδa} {du = da~} aₛ)) (CtxSymm dΓ=') dΓ= , TmRefl (congTm (! ([idMor]Ty A)) refl (DMor-dTm aa aₛ a₁))))

appStr₁S : (B : ObS (suc (suc n))) (f : MorS n (suc n)) (fₛ : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS n (suc n)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) → ∂₁S (appStrS B f fₛ f₁ a as a₁) ≡ starS a B a₁
appStr₁S = //-elimP (λ B → //-elimP (λ f fₛ f₁ → //-elimP (appStr₁S-// B f fₛ f₁)))


sigStrS-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (b : DMor (suc n) (suc (suc n))) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) → DMor n (suc n)
sigStrS-// i a aₛ a₁ b bₛ b₁ =
  dmor (lhs a)
       ((ctx (lhs a) , uu i) , (der (lhs a) , UU))
       (idMor _ , sig i (Tm a) (Tm b))
       (idMor+ (der (lhs a)) (SigUU (DMor-dTm a aₛ a₁) (DMor-dTm b bₛ b₁)))

sigStrS-eq : (i : ℕ) (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (a'₁ : ∂₁S (proj a') ≡ UUStrS i (∂₀S (proj a'))) (b b' : DMor (suc n) (suc (suc n))) (rb : b ≃ b') (bₛ : is-sectionS (proj b)) (b'ₛ : is-sectionS (proj b')) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) (b'₁ : ∂₁S (proj b') ≡ UUStrS i (ElStrS i (proj a') a'ₛ a'₁)) → proj {R = MorEquiv} (sigStrS-// i a aₛ a₁ b bₛ b₁) ≡ proj (sigStrS-// i a' a'ₛ a'₁ b' b'ₛ b'₁)
sigStrS-eq i a a' ra@((da₀=a'₀ , _) , _) aₛ a'ₛ a₁ a'₁ b b' rb bₛ b'ₛ b₁ b'₁ =
           eq ((da₀=a'₀ , (da₀=a'₀ ,, UUCong)) , (idMor+= (der (lhs a))
                                                          (SigUUCong (DMor-dTm a aₛ a₁)
                                                                     (DMor-dTm= (da₀=a'₀ ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁)
                                                                     (DMor-dTm= ((da₀=a'₀ ,, ElCong (DMor-dTm= (da₀=a'₀ ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁)) ,, UUCong) b b' rb bₛ b'ₛ b₁ b'₁))))

sigStrS : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (b : MorS (suc n) (suc (suc n))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁)) → MorS n (suc n)
sigStrS i = //-elim-PiP3 (λ a aₛ a₁ → //-elim-PiP2 (λ b bₛ b₁ → proj (sigStrS-// i a aₛ a₁ b bₛ b₁))
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


pairStrS-// : (B : DCtx (suc (suc n))) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (b : DMor n (suc n)) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj B) a₁) → DMor n (suc n)
pairStrS-// BB@(((Γ , A) , B) , ((dΓ , dA) , dB)) a aₛ a₁ b bₛ b₁ =
  dmor (Γ , dΓ)
       ((Γ , sig A B) , (dΓ , Sig dA dB))
       (idMor _ , pair A B (Tm a) (Tm b))
       (idMor+ dΓ (Pair dA dB (DMor-dTm a aₛ a₁) (DMor-dTm+ BB a aₛ a₁ b bₛ b₁)))

       

pairStrS-eq : (B B' : DCtx (suc (suc n))) (rB : B ≃ B') (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (a'₁ : ∂₁S (proj a') ≡ ftS (proj B')) (b b' : DMor n (suc n)) (rb : b ≃ b') (bₛ : is-sectionS (proj b)) (b'ₛ : is-sectionS (proj b')) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj B) a₁) (b'₁ : ∂₁S (proj b') ≡ starS (proj a') (proj B') a'₁) → proj {R = MorEquiv} (pairStrS-// B a aₛ a₁ b bₛ b₁) ≡ proj (pairStrS-// B' a' a'ₛ a'₁ b' b'ₛ b'₁)
pairStrS-eq BB@(((Γ , A) , B) , ((dΓ , dA) , dB))
            BB'@(((Γ' , A') , B') , ((dΓ' , dA') , dB')) rB@(rA@(dΓ= , _ , _ , dA= , _) , _ , _ , dB= , _)
            a@(dmor _ ((Γa' , Aa) , (_ ,  dAa)) (_ , _) (dδa , da))
            a'@(dmor _ ((Γa'' , Aa') , (_ ,  dAa')) (_ , _) (dδa' , da')) ra aₛ a'ₛ a₁ a'₁ b b' rb bₛ b'ₛ b₁ b'₁ = 
                              eq ((dΓ= , (dΓ= ,, SigCong dA dA= dB=)) ,
                                 idMor+= dΓ
                                 (PairCong dA dA= dB= (DMor-dTm= rA a a' ra aₛ a'ₛ a₁ a'₁) (DMor-dTm+= BB BB' rB a a' ra aₛ a'ₛ a₁ a'₁ b b' rb bₛ b'ₛ b₁ b'₁)))


pairStrS : (B : ObS (suc (suc n))) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) (b : MorS n (suc n)) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ starS a B a₁) → MorS n (suc n)
pairStrS = //-elim-PiS (λ B → //-elim-PiP3 (λ a aₛ a₁ → //-elim-PiP2 (λ b bₛ b₁ → proj (pairStrS-// B a aₛ a₁ b bₛ b₁))
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


pr1StrS-// : (B : DCtx (suc (suc n))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) → DMor n (suc n)
pr1StrS-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u uₛ u₁ =
  dmor (Γ , dΓ)
       ((Γ , A) , (dΓ , dA))
       (idMor _ , pr1 A B (Tm u))
       (idMor+ dΓ (Pr1 dA dB (DMor-dTm u uₛ u₁)))

pr1StrS-eq : (B B' : DCtx (suc (suc n))) (rB : B ≃ B') (u u' : DMor n (suc n)) (ru : u ≃ u') (uₛ : is-sectionS (proj u)) (u'ₛ : is-sectionS (proj u')) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) (u'₁ : ∂₁S (proj u') ≡ SigStrS (proj B')) → proj {R = MorEquiv} (pr1StrS-// B u uₛ u₁) ≡ proj (pr1StrS-// B' u' u'ₛ u'₁)
pr1StrS-eq (((Γ , A) , B) , ((dΓ , dA) , dB)) (((Γ' , A') , B') , ((dΓ' , dA') , dB'))  rB@((dΓ= , _ , _ , dA= , _) , _ , _ , dB= , _) u u' ru uₛ u'ₛ u₁ u'₁ = eq ((dΓ= , (dΓ= ,, dA=)) , idMor+= dΓ (Pr1Cong dA dA= dB= (DMor-dTm= (dΓ= ,, SigCong dA dA= dB=) u u' ru uₛ u'ₛ u₁ u'₁)))


pr1StrS : (B : ObS (suc (suc n))) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B) → MorS n (suc n)
pr1StrS = //-elim-PiS (λ B → //-elim-PiP2 (λ u uₛ u₁ → proj (pr1StrS-// B u uₛ u₁))
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


pr2StrS-// : (B : DCtx (suc (suc n))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) → DMor n (suc n)
pr2StrS-// (((Γ , A) , B) , ((dΓ , dA) , dB)) u uₛ u₁ =
  dmor (Γ , dΓ)
       ((Γ , substTy B (pr1 A B (Tm u))) , (dΓ , SubstTy dB (idMor+ dΓ (Pr1 dA dB (DMor-dTm u uₛ u₁) ))))
       (idMor _ , pr2 A B (Tm u))
       (idMor+ dΓ (Pr2 dA dB (DMor-dTm u uₛ u₁)))

pr2StrS-eq : (B B' : DCtx (suc (suc n))) (rB : B ≃ B') (u u' : DMor n (suc n)) (ru : u ≃ u') (uₛ : is-sectionS (proj u)) (u'ₛ : is-sectionS (proj u')) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) (u'₁ : ∂₁S (proj u') ≡ SigStrS (proj B')) → proj {R = MorEquiv} (pr2StrS-// B u uₛ u₁) ≡ proj (pr2StrS-// B' u' u'ₛ u'₁)
pr2StrS-eq (((Γ , A) , B) , ((dΓ , dA) , dB)) (((Γ' , A') , B') , ((dΓ' , dA') , dB'))  rB@((dΓ= , _ , _ , dA= , _) , _ , _ , dB= , _) u u' ru uₛ u'ₛ u₁ u'₁ = eq ((dΓ= , (dΓ= ,, SubstTyFullEq {Δ = (Γ , A)} (ConvTy dB' (CtxSymm dΓ= ,, ConvTyEq (TySymm dA=) dΓ=)) (idMor+ dΓ (Pr1 dA dB (DMor-dTm u uₛ u₁))) dB= (idMor+= dΓ (Pr1Cong dA dA= dB= (DMor-dTm= (dΓ= ,, SigCong dA dA= dB=) u u' ru uₛ u'ₛ u₁ u'₁))))) , idMor+= dΓ (Pr2Cong dA dA= dB= (DMor-dTm= (dΓ= ,, SigCong dA dA= dB=) u u' ru uₛ u'ₛ u₁ u'₁)))


pr2StrS : (B : ObS (suc (suc n))) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B) → MorS n (suc n)
pr2StrS = //-elim-PiS (λ B → //-elim-PiP2 (λ u uₛ u₁ → proj (pr2StrS-// B u uₛ u₁))
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


natStrS-// : (i : ℕ) (X : DCtx n) → DMor n (suc n)
natStrS-// i X = dmor X ((ctx X , uu i) , (der X , UU)) (idMor _ , nat i) (idMor+ (der X) NatUU)

natStrS-eq : (i : ℕ) (X X' : DCtx n) (rX : X ≃ X') → proj {R = MorEquiv} (natStrS-// i X) ≡ proj (natStrS-// i X')
natStrS-eq i X X' rX = eq ((rX , (rX ,, UUCong)) , (idMor+= (der X) NatUUCong))

natStrS : (i : ℕ) (X : ObS n) → MorS n (suc n)
natStrS i = //-rec (λ X → proj (natStrS-// i X)) (λ {X} {X'} rX → natStrS-eq i X X' rX)

natStrₛS-// : (i : ℕ) (X : DCtx n) → is-sectionS (natStrS i (proj X))
natStrₛS-// i X = eq ((CtxRefl (der X) , CtxRefl (der X)) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable (der X))))

natStrₛS : (i : ℕ) (X : ObS n) → is-sectionS (natStrS i X)
natStrₛS i = //-elimP (λ X → natStrₛS-// i X)


natStr₁S-// : (i : ℕ) (X : DCtx n) → ∂₁S (natStrS i (proj X)) ≡ UUStrS i (proj X)
natStr₁S-// i X = refl

natStr₁S : (i : ℕ) (X : ObS n) → ∂₁S (natStrS i X) ≡ UUStrS i X
natStr₁S i = //-elimP  (λ X → natStr₁S-// i X)


zeroStrS-// : (X : DCtx n) → DMor n (suc n)
zeroStrS-// X = dmor X ((ctx X , nat) , (der X , Nat)) (idMor _ , zero) (idMor+ (der X) Zero)

zeroStrS-eq : (X X' : DCtx n) (rX : X ≃ X') → proj {R = MorEquiv} (zeroStrS-// X) ≡ proj (zeroStrS-// X')
zeroStrS-eq X X' rX = eq ((rX , (rX ,, NatCong)) , (idMor+= (der X) ZeroCong))

zeroStrS : (X : ObS n) → MorS n (suc n)
zeroStrS = //-rec (λ X → proj (zeroStrS-// X)) λ {X} {X'} rX → zeroStrS-eq X X' rX

zeroStrₛS-// : (X : DCtx n) → is-sectionS (zeroStrS (proj X))
zeroStrₛS-// X = eq ((CtxRefl (der X) , CtxRefl (der X)) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable (der X))))

zeroStrₛS : (X : ObS n) → is-sectionS (zeroStrS X)
zeroStrₛS = //-elimP (λ X → zeroStrₛS-// X)


zeroStr₁S-// : (X : DCtx n) → ∂₁S (zeroStrS (proj X)) ≡ NatStrS (proj X)
zeroStr₁S-// X = refl

zeroStr₁S : (X : ObS n) → ∂₁S (zeroStrS X) ≡ NatStrS X
zeroStr₁S = //-elimP  (λ X → zeroStr₁S-// X)


sucStrS-// : (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (∂₀S (proj u))) → DMor n (suc n)
sucStrS-// u uₛ u₁ = dmor (lhs u) ((ctx (lhs u) , nat) , (der (lhs u) , Nat)) (idMor _ , (suc (Tm u))) (idMor+ (der (lhs u)) (Suc (DMor-dTm u uₛ u₁)))

sucStrS-eq : (u u' : DMor n (suc n)) (ru : u ≃ u') (uₛ : is-sectionS (proj u)) (u'ₛ : is-sectionS (proj u')) (u₁ : ∂₁S (proj u) ≡ NatStrS (∂₀S (proj u))) (u'₁ : ∂₁S (proj u') ≡ NatStrS (∂₀S (proj u'))) → proj {R = MorEquiv} (sucStrS-// u uₛ u₁) ≡ proj (sucStrS-// u' u'ₛ u'₁)
sucStrS-eq u u' ru@((lhs= , rhs=) , mor=) uₛ u'ₛ u₁ u'₁ = eq ((lhs= , (lhs= ,, NatCong)) , idMor+= (der (lhs u)) (SucCong (DMor-dTm= (lhs= ,, NatCong) u u' ru uₛ u'ₛ u₁ u'₁)))

sucStrS : (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ NatStrS (∂₀S u)) → MorS n (suc n)
sucStrS = //-elim-PiP2 (λ u uₛ u₁ → proj (sucStrS-// u uₛ u₁)) (λ {u} {u'} ru uₛ u'ₛ → PathOver-Prop→Cst (λ u₁ u'₁ → sucStrS-eq u u' ru uₛ u'ₛ u₁ u'₁)) 

sucStrₛS-// : (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (∂₀S (proj u))) → is-sectionS (sucStrS (proj u) uₛ u₁)
sucStrₛS-// u uₛ u₁ = eq ((CtxRefl (der (lhs u)) , CtxRefl (der (lhs u))) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable (der (lhs u)))))

sucStrₛS : (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ NatStrS (∂₀S u)) → is-sectionS (sucStrS u uₛ u₁)
sucStrₛS = //-elimP (λ u uₛ u₁ → sucStrₛS-// u uₛ u₁)

sucStr₁S-// : (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (∂₀S (proj u))) → ∂₁S (sucStrS (proj u) uₛ u₁) ≡ NatStrS (∂₀S (proj u))
sucStr₁S-// u uₛ u₁ = refl

sucStr₁S : (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ NatStrS (∂₀S u)) → ∂₁S (sucStrS u uₛ u₁) ≡ NatStrS (∂₀S u)
sucStr₁S = //-elimP (λ u uₛ u₁ → sucStr₁S-// u uₛ u₁)


idStrS-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj a) aₛ a₁)  (v : DMor n (suc n)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj a) aₛ a₁) → DMor n (suc n)
idStrS-// i a aₛ a₁ u uₛ u₁ v vₛ v₁ = dmor (lhs a) ((ctx (lhs a) , uu i) , (der (lhs a) , UU)) (idMor _ , id i (Tm a) (Tm u) (Tm v)) (idMor+ (der (lhs a)) (IdUU (DMor-dTm a aₛ a₁) (DMor-dTm u uₛ u₁) (DMor-dTm v vₛ v₁)))


idStrS-eq : (i : ℕ) (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (a'₁ : ∂₁S (proj a') ≡ UUStrS i (∂₀S (proj a'))) (u u' : DMor n (suc n)) (ru : u ≃ u') (uₛ : is-sectionS (proj u)) (u'ₛ : is-sectionS (proj u')) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj a) aₛ a₁)  (u'₁ : ∂₁S (proj u') ≡ ElStrS i (proj a') a'ₛ a'₁) (v v' : DMor n (suc n)) (rv : v ≃ v') (vₛ : is-sectionS (proj v)) (v'ₛ : is-sectionS (proj v')) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj a) aₛ a₁) (v'₁ : ∂₁S (proj v') ≡ ElStrS i (proj a') a'ₛ a'₁) → proj {R = MorEquiv} (idStrS-// i a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ proj (idStrS-// i a' a'ₛ a'₁ u' u'ₛ u'₁ v' v'ₛ v'₁)
idStrS-eq i a a' ra@((lhs= , rhs=) , mor=) aₛ a'ₛ a₁ a'₁ u u' ru uₛ u'ₛ u₁ u'₁ v v' rv vₛ v'ₛ v₁ v'₁ = eq ((lhs= , (lhs= ,, UUCong)) , idMor+= (der (lhs a)) (IdUUCong (DMor-dTm= (lhs= ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁) (DMor-dTm= (lhs= ,, ElCong (DMor-dTm= (lhs= ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁)) u u' ru uₛ u'ₛ u₁ u'₁) (DMor-dTm= (lhs= ,, ElCong (DMor-dTm= (lhs= ,, UUCong) a a' ra aₛ a'ₛ a₁ a'₁)) v v' rv vₛ v'ₛ v₁ v'₁)))


idStrS : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ ElStrS i a aₛ a₁)  (v : MorS n (suc n)) (vₛ : is-sectionS v) (v₁ : ∂₁S v ≡ ElStrS i a aₛ a₁) → MorS n (suc n)
idStrS i = //-elim-PiP3 (λ a aₛ a₁ → //-elim-PiP2 (λ u uₛ u₁ → //-elim-PiP2 (λ v vₛ v₁ → proj (idStrS-// i a aₛ a₁ u uₛ u₁ v vₛ v₁)) (λ {v} {v'} rv vₛ v'ₛ → PathOver-Prop→Cst (λ v₁ v'₁ → idStrS-eq i a a (ref a) aₛ aₛ a₁ a₁ u u (ref u) uₛ uₛ u₁ u₁ v v' rv vₛ v'ₛ v₁ v'₁)))
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

reflStrS-// : (A : DCtx (suc n)) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ (proj A)) → DMor n (suc n)
reflStrS-// ((Γ , A) , (dΓ , dA)) a aₛ a₁ = dmor (Γ , dΓ) ((Γ , id A (Tm a) (Tm a)) , (dΓ , Id dA (DMor-dTm a aₛ a₁) (DMor-dTm a aₛ a₁))) (idMor _ , refl A (Tm a)) (idMor+ dΓ (Refl dA (DMor-dTm a aₛ a₁)))

reflStrS-eq : (A A' : DCtx (suc n)) (rA : A ≃ A') (a a' : DMor n (suc n)) (ra : a ≃ a') (aₛ : is-sectionS (proj a)) (a'ₛ : is-sectionS (proj a')) (a₁ : ∂₁S (proj a) ≡ (proj A)) (a'₁ : ∂₁S (proj a') ≡ (proj A')) → proj {R = MorEquiv} (reflStrS-// A a aₛ a₁) ≡ proj (reflStrS-// A' a' a'ₛ a'₁)
reflStrS-eq ((Γ , A) , (dΓ , dA)) ((Γ' , A') , (dΓ' , dA')) rA@(dΓ= , _ , _ , dA= , _) a a' ra aₛ a'ₛ a₁ a'₁ = eq ((dΓ= , (dΓ= ,, IdCong dA= (DMor-dTm= (dΓ= ,, dA=) a a' ra aₛ a'ₛ a₁ a'₁) (DMor-dTm= (dΓ= ,, dA=) a a' ra aₛ a'ₛ a₁ a'₁))) , idMor+= dΓ (ReflCong dA= (DMor-dTm= (dΓ= ,, dA=) a a' ra aₛ a'ₛ a₁ a'₁)))

reflStrS  : (A : ObS (suc n)) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ A) → MorS n (suc n)
reflStrS = //-elim-PiS (λ A → //-elim-PiP2 (λ a aₛ a₁ → proj (reflStrS-// A a aₛ a₁)) λ {a} {a'} ra aₛ a'ₛ → PathOver-Prop→Cst (λ a₁ a'₁ → reflStrS-eq A A (ref A) a a' ra aₛ a'ₛ a₁ a'₁)) (λ {A} {A'} rA → //-elimP (λ a → PathOver-CstPropPi (λ aₛ → PathOver-Prop→Cst (λ a₁ a₁' → reflStrS-eq A A' rA a a (ref a) aₛ aₛ a₁ a₁'))))

reflStrₛS-// : (A : DCtx (suc n)) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ (proj A)) → is-sectionS (reflStrS (proj A) (proj a) aₛ a₁)
reflStrₛS-// ((Γ , A) , (dΓ , dA)) a aₛ a₁ = eq ((CtxRefl dΓ , CtxRefl dΓ) , congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable dΓ)))

reflStrₛS :  (A : ObS (suc n)) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ A) → is-sectionS (reflStrS A a aₛ a₁)
reflStrₛS = //-elimP (λ A → (//-elimP (λ a aₛ a₁ → reflStrₛS-// A a aₛ a₁)))


reflStr₁S-// : (A : DCtx (suc n)) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ (proj A)) → ∂₁S (reflStrS (proj A) (proj a) aₛ a₁) ≡ IdStrS (proj A) (proj a) aₛ a₁ (proj a) aₛ a₁
reflStr₁S-// ((Γ , A) , (dΓ , dA)) a aₛ a₁ = refl

reflStr₁S :  (A : ObS (suc n)) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ A) → ∂₁S (reflStrS A a aₛ a₁) ≡ IdStrS A a aₛ a₁ a aₛ a₁
reflStr₁S = //-elimP (λ A → (//-elimP (λ a aₛ a₁ → reflStr₁S-// A a aₛ a₁)))


--Naturality of type formers

open StructuredCCat

ssₛS : (f : MorS m (suc n)) → is-sectionS (ssS f)
ssₛS f = ap2-irr compS (ap ppS (ss₁S f)) refl ∙ (ss-ppS f) ∙ ap (idS _) (! (ss₀S f))

starTmS : (g : MorS n m) (u : MorS m (suc m)) (u₀ : ∂₀S u ≡ ∂₁S g) → MorS n (suc n)
starTmS g u u₀ = ssS (compS u g (! u₀))

ss₁'S : {f : MorS m (suc n)} {X : ObS (suc n)} (p : ∂₁S f ≡ X) → ∂₁S (ssS f) ≡ starS (compS (ppS X) f (p ∙ ! (pp₀S X))) X (comp₁S (ppS X) f (p ∙ ! (pp₀S X)) ∙ pp₁S X)
ss₁'S {f = f} refl = ss₁S f

starTm₁S : (g : MorS n m) (u : MorS m (suc m)) (uₛ : is-sectionS u) (u₀ : ∂₀S u ≡ ∂₁S g) {X : ObS (suc m)} (p : ∂₁S u ≡ X) → ∂₁S (starTmS g u u₀) ≡ starS g X (! u₀ ∙ is-section₀S u uₛ p)
starTm₁S g u uₛ u₀ p = ss₁'S (comp₁S u g (! u₀)) ∙ ap2-irr starS (! (assocS (ppS (∂₁S u)) u g (! u₀) (! (pp₀S (∂₁S u)))) ∙ ap2-irr compS (uₛ ∙ ap (idS _) u₀) refl ∙ id-rightS g) p

starTm₀S : (g : MorS n m) (u : MorS m (suc m)) (u₀ : ∂₀S u ≡ ∂₁S g) → ∂₀S (starTmS g u u₀) ≡ ∂₀S g
starTm₀S g u u₀ = ss₀S (compS u g (! u₀)) ∙ comp₀S u g (! u₀)

star+S : (g : MorS n m) (A : ObS (suc (suc m))) (A= : ftS (ftS A) ≡ ∂₁S g) → ObS (suc (suc n))
star+S g A A= = starS (qqS g (ftS A) (! A=)) A (qq₁S g (ftS A) (! A=))


starTm+S : (g : MorS n m) (u : MorS (suc m) (suc (suc m))) (p : ftS (∂₀S u) ≡ ∂₁S g) → MorS (suc n) (suc (suc n))
starTm+S g u p = ssS (compS u (qqS g (∂₀S u) (! p)) (qq₁S g (∂₀S u) (! p)))

starTm+₁S : (g : MorS n m) (u : MorS (suc m) (suc (suc m))) (uₛ : is-sectionS u) {X : ObS (suc (suc m))} (u₁ : ∂₁S u ≡ X) (p : ftS (∂₀S u) ≡ ∂₁S g) → ∂₁S (starTm+S g u p) ≡ star+S g X (ap ftS (! (is-section₀S u uₛ u₁)) ∙ p)
starTm+₁S g u uₛ u₁ p = starTm₁S (qqS g (∂₀S u) (! p)) u uₛ (! (qq₁S g (∂₀S u) (! p))) u₁ ∙ ap2-irr starS {a = qqS g (∂₀S u) (! p)} (ap2-irr qqS {a = g} refl (is-section₀S u uₛ u₁) {b = ! p} {b' = ! (ap ftS (! (is-section₀S u uₛ u₁)) ∙ p)}) refl {b = ! (! (qq₁S g (∂₀S u) (! p) ∙ is-section₀S u uₛ u₁))} 


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


IdStrNatS-// : (g : DMor n m) (A : DCtx (suc m)) (u : DMor m (suc m)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ (proj A))
                                                 (v : DMor m (suc m)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ (proj A)) (p : ftS (proj A) ≡ ∂₁S (proj g))
  → starS (proj g) (IdStrS (proj A) (proj u) uₛ u₁ (proj v) vₛ v₁) (! (IdStr=S (proj A) (proj u) uₛ u₁ (proj v) vₛ v₁ ∙ p))
    ≡ IdStrS (starS (proj g) (proj A) (! p))
      (starTmS (proj g) (proj u) (is-section₀S (proj u) uₛ u₁ ∙ p)) (ssₛS (compS (proj u) (proj g) (! (is-section₀S (proj u) uₛ u₁ ∙ p))))
      (starTm₁S (proj g) (proj u) uₛ (is-section₀S (proj u) uₛ u₁ ∙ p) u₁)
      (starTmS (proj g) (proj v) (is-section₀S (proj v) vₛ v₁ ∙ p)) (ssₛS (compS (proj v) (proj g) (! (is-section₀S (proj v) vₛ v₁ ∙ p))))
      (starTm₁S (proj g) (proj v) vₛ (is-section₀S (proj v) vₛ v₁ ∙ p) v₁)
IdStrNatS-// (dmor (Δ , dΔ) (Γ' , dΓ') g dg) ((Γ , A) , (dΓ , dA)) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , u) (_ , _)) uₛ u₁ (dmor (_ , _) ((_ , _) , (_ , _)) (_ , v) (_ , _)) vₛ v₁ p =
  refl

IdStrNatS : (g : MorS n m) (A : ObS (suc m)) (u : MorS m (suc m)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ A) (v : MorS m (suc m)) (vₛ : is-sectionS v) (v₁ : ∂₁S v ≡ A) (p : ftS A ≡ ∂₁S g)
  → starS g (IdStrS A u uₛ u₁ v vₛ v₁) (! (IdStr=S A u uₛ u₁ v vₛ v₁ ∙ p))
    ≡ IdStrS (starS g A (! p))
      (starTmS g u (is-section₀S u uₛ u₁ ∙ p)) (ssₛS (compS u g (! (is-section₀S u uₛ u₁ ∙ p))))
      (starTm₁S g u uₛ (is-section₀S u uₛ u₁ ∙ p) u₁)
      (starTmS g v (is-section₀S v vₛ v₁ ∙ p)) (ssₛS (compS v g (! (is-section₀S v vₛ v₁ ∙ p))))
      (starTm₁S g v vₛ (is-section₀S v vₛ v₁ ∙ p) v₁)
IdStrNatS = //-elimP (λ g → //-elimP (λ A → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → IdStrNatS-// g A u uₛ u₁ v vₛ v₁))))

-- Naturality of term formers

uuStr₀S : ∀ {n} i X → _
uuStr₀S {n} i X = is-section₀S {n} (uuStrS i X) (uuStrₛS i X) (uuStr₁S i X) ∙ UUStr=S (suc i) X

uuStrNatS-// : (i : ℕ) {n m : ℕ} (g : DMor n m) (X : DCtx m) (p : proj X ≡ ∂₁S (proj g)) → starTmS (proj g) (uuStrS i (proj X)) (uuStr₀S i (proj X) ∙ p) ≡ uuStrS i (∂₀S (proj g))
uuStrNatS-// i g X p = refl

uuStrNatS : (i : ℕ) {n m : ℕ} (g : MorS n m) (X : ObS m) (p : X ≡ ∂₁S g)
             → starTmS g (uuStrS i X) (uuStr₀S i X ∙ p) ≡ uuStrS i (∂₀S g)
uuStrNatS i = //-elimP (λ g → //-elimP (λ X p → uuStrNatS-// i g X p))


piStr₀S : ∀ {n} i a aₛ a₁ b bₛ b₁ → _
piStr₀S {n} i a aₛ a₁ b bₛ b₁ = is-section₀S {n} (piStrS i a aₛ a₁ b bₛ b₁) (piStrₛS i a aₛ a₁ b bₛ b₁) (piStr₁S i a aₛ a₁ b bₛ b₁) ∙ UUStr=S i (∂₀S a)

piStrNatS-// : (i : ℕ) {n m : ℕ} (g : DMor n m) (a : DMor m (suc m)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a)))
                                                                     (b : DMor (suc m) (suc (suc m))) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b)≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) (p : ∂₀S (proj a) ≡ ∂₁S (proj g))
                                                                     (let b₀ = ap ftS (is-section₀S (proj b) bₛ b₁ ∙ (UUStr=S i (ElStrS i (proj a) aₛ a₁))) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)
             → starTmS (proj g) (piStrS i (proj a) aₛ a₁ (proj b) bₛ b₁) (piStr₀S i (proj a) aₛ a₁ (proj b) bₛ b₁ ∙ p) ≡ piStrS i (starTmS (proj g) (proj a) p) (ssₛS (compS (proj a) (proj g) (! p))) (starTm₁S (proj g) (proj a) aₛ p a₁ ∙ UUStrNatS (proj g) (∂₀S (proj a)) p ∙ ap (UUStrS i) (! (ss₀S (compS (proj a) (proj g) (! p)) ∙ comp₀S (proj a) (proj g) (! p))))
                                                                           (starTm+S (proj g) (proj b) b₀) (ssₛS (compS (proj b) (qqS (proj g) (∂₀S (proj b)) (! b₀)) (qq₁S (proj g) (∂₀S (proj b)) (! b₀))))
                                                                           (starTm+₁S (proj g) (proj b) bₛ b₁ b₀ ∙ UUStrNatS (qqS (proj g) (ftS (UUStrS i (ElStrS i (proj a) aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p))) (ElStrS i (proj a) aₛ a₁) (! (qq₁S (proj g) (ftS (UUStrS i (ElStrS i (proj a) aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)) ∙ UUStr=S i (ElStrS i (proj a) aₛ a₁))) ∙ ap (UUStrS i) (qq₀S (proj g) (ftS (UUStrS i (ElStrS i (proj a) aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)) ∙ ap2-irr starS {a = proj g} refl (UUStr=S i (ElStrS i (proj a) aₛ a₁)) {b =  ! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)} {b' = ! (ElStr=S i (proj a) aₛ a₁ ∙ p)} ∙ (ElStrNatS (proj g) (proj a) aₛ a₁ p)))
piStrNatS-// i g@(dmor (_ , _) (_ , _) _ _) a@(dmor _ ((_ , _) , (_ , _)) (_ , _) (_ , _)) aₛ a₁ b@(dmor ((_ , _) , (_ , _)) (((_ , _) , _) , ((_ , _) , _)) ((_ , _) , _)  ((_ , _) , _)) bₛ b₁ p = refl

piStrNatS : (i : ℕ) {n m : ℕ} (g : MorS n m) (a : MorS m (suc m)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a))
                                                                   (b : MorS (suc m) (suc (suc m))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁)) (p : ∂₀S a ≡ ∂₁S g)
                                                                   (let b₀ = ap ftS (is-section₀S b bₛ b₁ ∙ (UUStr=S i (ElStrS i a aₛ a₁))) ∙ ElStr=S i a aₛ a₁ ∙ p)
             →  starTmS g (piStrS i a aₛ a₁ b bₛ b₁) (piStr₀S i a aₛ a₁ b bₛ b₁ ∙ p) ≡ piStrS i (starTmS g a p) (ssₛS (compS a g (! p))) (starTm₁S g a aₛ p a₁ ∙ UUStrNatS g (∂₀S a) p ∙ ap (UUStrS i) (! (ss₀S (compS a g (! p)) ∙ comp₀S a g (! p))))
                                                                           (starTm+S g b b₀) (ssₛS (compS b (qqS g (∂₀S b) (! b₀)) (qq₁S g (∂₀S b) (! b₀))))
                                                                           (starTm+₁S g b bₛ b₁ b₀ ∙ UUStrNatS (qqS g (ftS (UUStrS i (ElStrS i a aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i a aₛ a₁)) ∙ ElStr=S i a aₛ a₁ ∙ p))) (ElStrS i a aₛ a₁) (! (qq₁S g (ftS (UUStrS i (ElStrS i a aₛ a₁))) (! (ap ftS (! (is-section₀S b bₛ b₁))  ∙ b₀)) ∙ UUStr=S i (ElStrS i a aₛ a₁))) ∙ ap (UUStrS i) (qq₀S g (ftS (UUStrS i (ElStrS i a aₛ a₁))) (! (ap ftS (! (is-section₀S b bₛ b₁))  ∙ b₀)) ∙ ap2-irr starS {a = g} refl (UUStr=S i (ElStrS i a aₛ a₁)) {b = ! (ap ftS (! (is-section₀S b bₛ b₁)) ∙ b₀)} {b' = ! (ElStr=S i a aₛ a₁ ∙ p)} ∙ (ElStrNatS g a aₛ a₁ p)))
piStrNatS i = //-elimP (λ g → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ p → piStrNatS-// i g a aₛ a₁ b bₛ b₁ p)))



lamStr₀S : ∀ {n} B u uₛ u₁ → _
lamStr₀S {n} B u uₛ u₁ = is-section₀S {n} (lamStrS B u uₛ u₁) (lamStrₛS B u uₛ u₁) (lamStr₁S B u uₛ u₁) ∙ PiStr=S B

-- CtxSubstRefl : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} {A : TyExpr m} → (⊢ Γ) → (Γ ⊢ δ ∷> Δ) → Derivable (Δ ⊢ A) → ⊢ (Γ , A [ δ ]Ty) == (Γ , A [ δ ]Ty)
-- CtxSubstRefl dΓ dδ dA = (CtxRefl dΓ ,, TyRefl (SubstTy dA dδ))

-- WeakSubstTmEq : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} {A : TyExpr m} {B : TyExpr (suc m)} {u v : TmExpr (suc m)} → (⊢ Γ) → Derivable (Δ ⊢ A) →  Derivable ((Δ , A) ⊢ u == v :> B) → (Γ ⊢ δ ∷> Δ) → Derivable ((Γ , A [ δ ]Ty) ⊢ u [ (weakenMor δ , var last) ]Tm == v [ (weakenMor δ , var last) ]Tm :> B [ (weakenMor δ , var last)  ]Ty)
-- WeakSubstTmEq {δ = δ} {A = A} dΓ dA du=v dδ = ConvTmEq (SubstTmEq du=v ((WeakMor (A [ δ ]Ty) dδ) , weakenDerLast dA dδ)) (CtxSubstRefl dΓ dδ dA)


up-to-rhsTyEq : {Γ : DCtx n} {A B : TyExpr n}  {δ : Mor n (suc n)} {w₁ : _} {w₂ : _} {w₃ : _} {w₄ : _} (Tyeq : A ≡ B) → proj {R = MorEquiv} (dmor Γ ((ctx Γ , A) , w₁) δ w₂) ≡ proj (dmor Γ ((ctx Γ , B) , w₃) δ w₄)
up-to-rhsTyEq {Γ = Γ} {δ = δ} TyEq = ap-irr2 (λ z p q → proj (dmor Γ ((ctx Γ , z) , p) δ q)) TyEq

lamStrNatS-// : {n m : ℕ} (g : DMor n m)(B : DCtx (suc (suc m))) (u : DMor (suc m) (suc (suc m))) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))
              →  starTmS (proj g) (lamStrS (proj B) (proj u) uₛ u₁) (lamStr₀S (proj B) (proj u) uₛ u₁ ∙ p) ≡ lamStrS (star+S (proj g) (proj B) p) (starTm+S (proj g) (proj u) (ap ftS (is-section₀S (proj u) uₛ u₁) ∙ p)) (ssₛS (compS (proj u) (qqS (proj g) (∂₀S (proj u)) (! (ap ftS (is-section₀S (proj u) uₛ u₁) ∙ p))) (qq₁S (proj g) (∂₀S (proj u)) (! (ap ftS (is-section₀S (proj u) uₛ u₁) ∙ p))))) (starTm+₁S (proj g) (proj u) uₛ u₁ (ap ftS (is-section₀S (proj u) uₛ u₁) ∙ p))
lamStrNatS-// {n} {m} g@(dmor (Γg , dΓg) (Δg , dΔg) δ dδ) BB@(((Γ , A) , B) , ((dΓ , dA) , dB)) uu@(dmor ((Δu , Au) , (dΔu , dAu)) (((Δ'u , A'u) , Bu) , ((dΔ'u , dA'u) , dBu)) ((idu , lastu), u) (didu , du)) uₛ u₁ p = up-to-rhsTyEq (ap (_[_]Ty _) (idMor[]Mor δ)) 

--! (eq ((CtxRefl dΓg , (CtxRefl dΓg ,, congTyEq refl (ap (λ z → pi A B [ z ]Ty) (! (idMor[]Mor δ))) (TyRefl (SubstTy (Pi dA dB) (ConvMor dδ (CtxRefl dΓg) (CtxSymm (reflect p))) )))) , MorRefl (idMor+ dΓg (SubstTm (Lam dA dB (DMor-dTm uu uₛ u₁)) (ConvMor dδ (CtxRefl dΓg) (CtxSymm (reflect p))))))) 
              


lamStrNatS : {n m : ℕ} (g : MorS n m) (B : ObS (suc (suc m))) (u : MorS (suc m) (suc (suc m))) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ B) (p : ftS (ftS B) ≡ ∂₁S g)
           → starTmS g (lamStrS B u uₛ u₁) (lamStr₀S B u uₛ u₁ ∙ p) ≡ lamStrS (star+S g B p) (starTm+S g u (ap ftS (is-section₀S u uₛ u₁) ∙ p)) (ssₛS  (compS u (qqS g (∂₀S u) (! (ap ftS (is-section₀S u uₛ u₁) ∙ p))) (qq₁S g (∂₀S u) (! (ap ftS (is-section₀S u uₛ u₁) ∙ p))))) (starTm+₁S g u uₛ u₁ (ap ftS (is-section₀S u uₛ u₁) ∙ p))
lamStrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ u uₛ u₁ → lamStrNatS-// g B u uₛ u₁)))


-- appStrNatS-// : (g : DMor n m) (B : DCtx (suc (suc m))) (f : DMor m (suc m)) (fₛ : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor m (suc m)) (as : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))  → ssS (compS (appStrS (proj B) (proj f) fₛ f₁ (proj a) as a₁) (proj g) (! (appStr₀S (proj B) (proj f) fₛ f₁ (proj a) as a₁ ∙ p))) ≡ appStrS (starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p))) (ssS (compS (proj f) (proj g) (! (is-section₀S {u = proj f} fₛ ∙ ap ftS f₁ ∙ (PiStr=S (proj B)) ∙ p)))) (ssₛS (compS (proj f) (proj g) (! (is-section₀S {u = proj f} fₛ ∙ ap ftS f₁ ∙ (PiStr=S (proj B)) ∙ p)))) (ss-comp-section₁S (proj g) (proj f) fₛ (! (is-section₀S {u = proj f} fₛ ∙ ap ftS f₁ ∙ (PiStr=S (proj B)) ∙ p)) ∙  ap2-irr starS {a = (proj g)} refl f₁ {b = ! (is-section₀S {u = proj f} fₛ ∙ ap ftS f₁ ∙ PiStr=S (proj B) ∙ p) ∙ is-section₀S {u = proj f} fₛ} ∙ (PiStrNatS (proj g) (proj B) p)) (ssS (compS (proj a) (proj g) (! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p)))) (ssₛS (compS (proj a) (proj g) (! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p)))) (ss-comp-section₁S (proj g) (proj a) as (! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p)) ∙ ! (ft-starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p)) ∙ qq₀S (proj g) (ftS (proj B)) (! p) ∙ ap2-irr starS {a = (proj g)} refl (! a₁) {b = ! p} {b' = ! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p) ∙ is-section₀S {u = proj a} as}))
-- appStrNatS-// gg@(dmor (Δ , dΔ) (Γg , dΓg) δg dδg) (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γf' , piABf) , (dΓf' , dpiABf)) (δf , f) (dδf , df~)) fₛ f₁ aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) as a₁ p =
--                             let ((_ , dΓf'=Γf) , dδf=id) = reflect fₛ
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


-- appStrNatS : (g : MorS n m) (B : ObS (suc (suc m))) (f : MorS m (suc m)) (fₛ : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS m (suc m)) (as : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) (p : ftS (ftS B) ≡ ∂₁S g)              → ssS (compS (appStrS B f fₛ f₁ a as a₁) g (! (appStr₀S B f fₛ f₁ a as a₁ ∙ p))) ≡ appStrS (starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p))) (ssS (compS f g (! (is-section₀S fₛ ∙ ap ftS f₁ ∙ (PiStr=S B) ∙ p)))) (ssₛS (compS f g (! (is-section₀S fₛ ∙ ap ftS f₁ ∙ (PiStr=S B) ∙ p)))) (ss-comp-section₁S g f fₛ (! (is-section₀S fₛ ∙ ap ftS f₁ ∙ (PiStr=S B) ∙ p)) ∙ ap2-irr starS {a = g} refl f₁  ∙ (PiStrNatS g B p)) (ssS (compS a g (! (is-section₀S as ∙ ap ftS a₁ ∙ p)))) (ssₛS (compS a g (! (is-section₀S as ∙ ap ftS a₁ ∙ p)))) (ss-comp-section₁S g a as (! (is-section₀S as ∙ ap ftS a₁ ∙ p)) ∙ ! (ft-starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p)) ∙ qq₀S g (ftS B) (! p) ∙ ap2-irr starS {a = g} refl (! a₁)))
-- appStrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ f fₛ f₁ → //-elimP (λ a as a₁ → appStrNatS-// g B f fₛ f₁ a as a₁))))


appStr₀S : ∀ {n} B f fₛ f₁ a aₛ a₁ → _
appStr₀S {n} B f fₛ f₁ a aₛ a₁ = is-section₀S {n} (appStrS B f fₛ f₁ a aₛ a₁) (appStrₛS B f fₛ f₁ a aₛ a₁) (appStr₁S B f fₛ f₁ a aₛ a₁) ∙ ft-starS a B a₁ ∙ is-section₀S a aₛ a₁

appStrNatS-// : {n m : ℕ} (g : DMor n m) (B : DCtx (suc (suc m))) (f : DMor m (suc m)) (fₛ : is-sectionS (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor m (suc m)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))
                (let a₀ = is-section₀S (proj a) aₛ a₁ ∙ p) (let f₀ = is-section₀S (proj f) fₛ f₁ ∙ PiStr=S (proj B) ∙ p)
             → starTmS (proj g) (appStrS (proj B) (proj f) fₛ f₁ (proj a) aₛ a₁) (appStr₀S (proj B) (proj f) fₛ f₁ (proj a) aₛ a₁ ∙ p)
                ≡ appStrS (star+S (proj g) (proj B) p)
                         (starTmS (proj g) (proj f) f₀) (ssₛS (compS (proj f) (proj g) (! f₀))) (starTm₁S (proj g) (proj f) fₛ f₀ f₁ ∙ PiStrNatS (proj g) (proj B) p)
                         (starTmS (proj g) (proj a) a₀) (ssₛS (compS (proj a) (proj g) (! a₀))) (starTm₁S (proj g) (proj a) aₛ a₀ a₁ ∙ ! (ft-starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p)) ∙ qq₀S (proj g) (ftS (proj B)) (! p)))
appStrNatS-// g@(dmor (Δ , dΔ) (Γg , dΓg) δ dδ) (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γ'f , piABf) , (dΓ'f , dpiABf)) (δf , f) (dδf , df~)) fs f₁ aa@(dmor (Γa , dΓa) ((Γ'a , Aa) , (dΓ'a , dAa)) (δa , a) (dδa , da~)) as a₁ p = up-to-rhsTyEq (ap (_[_]Ty _) (idMor[]Mor δ) ∙ ! (substCommutes[]Ty _ _ _))


appStrNatS : {n m : ℕ} (g : MorS n m) (B : ObS (suc (suc m))) (f : MorS m (suc m)) (fₛ : is-sectionS f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS m (suc m)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) (p : ftS (ftS B) ≡ ∂₁S g)
                (let a₀ = is-section₀S a aₛ a₁ ∙ p) (let f₀ = is-section₀S f fₛ f₁ ∙ PiStr=S B ∙ p)
             → starTmS g (appStrS B f fₛ f₁ a aₛ a₁) (appStr₀S B f fₛ f₁ a aₛ a₁ ∙ p)
                ≡ appStrS (star+S g B p)
                         (starTmS g f f₀) (ssₛS (compS f g (! f₀))) (starTm₁S g f fₛ f₀ f₁ ∙ PiStrNatS g B p)
                         (starTmS g a a₀) (ssₛS (compS a g (! a₀))) (starTm₁S g a aₛ a₀ a₁ ∙ ! (ft-starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p)) ∙ qq₀S g (ftS B) (! p)))
appStrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ f fₛ f₁ → //-elimP (λ a aₛ a₁ p → appStrNatS-// g B f fₛ f₁ a aₛ a₁ p))))



sigStr₀S : ∀ {n} i a aₛ a₁ b bₛ b₁ → _
sigStr₀S {n} i a aₛ a₁ b bₛ b₁ = is-section₀S {n} (sigStrS i a aₛ a₁ b bₛ b₁) (sigStrₛS i a aₛ a₁ b bₛ b₁) (sigStr₁S i a aₛ a₁ b bₛ b₁) ∙ UUStr=S i (∂₀S a)

sigStrNatS-// : (i : ℕ) {n m : ℕ} (g : DMor n m) (a : DMor m (suc m)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a)))
                                                                     (b : DMor (suc m) (suc (suc m))) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b)≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) (p : ∂₀S (proj a) ≡ ∂₁S (proj g))
                                                                     (let b₀ = ap ftS (is-section₀S (proj b) bₛ b₁ ∙ (UUStr=S i (ElStrS i (proj a) aₛ a₁))) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)
             → starTmS (proj g) (sigStrS i (proj a) aₛ a₁ (proj b) bₛ b₁) (sigStr₀S i (proj a) aₛ a₁ (proj b) bₛ b₁ ∙ p) ≡ sigStrS i (starTmS (proj g) (proj a) p) (ssₛS (compS (proj a) (proj g) (! p))) (starTm₁S (proj g) (proj a) aₛ p a₁ ∙ UUStrNatS (proj g) (∂₀S (proj a)) p ∙ ap (UUStrS i) (! (ss₀S (compS (proj a) (proj g) (! p)) ∙ comp₀S (proj a) (proj g) (! p))))
                                                                           (starTm+S (proj g) (proj b) b₀) (ssₛS (compS (proj b) (qqS (proj g) (∂₀S (proj b)) (! b₀)) (qq₁S (proj g) (∂₀S (proj b)) (! b₀))))
                                                                           (starTm+₁S (proj g) (proj b) bₛ b₁ b₀ ∙ UUStrNatS (qqS (proj g) (ftS (UUStrS i (ElStrS i (proj a) aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p))) (ElStrS i (proj a) aₛ a₁) (! (qq₁S (proj g) (ftS (UUStrS i (ElStrS i (proj a) aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)) ∙ UUStr=S i (ElStrS i (proj a) aₛ a₁))) ∙ ap (UUStrS i) (qq₀S (proj g) (ftS (UUStrS i (ElStrS i (proj a) aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)) ∙ ap2-irr starS {a = proj g} refl (UUStr=S i (ElStrS i (proj a) aₛ a₁)) {b =  ! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)} {b' = ! (ElStr=S i (proj a) aₛ a₁ ∙ p)} ∙ (ElStrNatS (proj g) (proj a) aₛ a₁ p)))
sigStrNatS-// i (dmor (_ , _) (_ , _) _ _) (dmor _ ((_ , _) , (_ , _)) (_ , _) (_ , _)) aₛ a₁ (dmor ((_ , _) , (_ , _)) (((_ , _) , _) , ((_ , _) , _)) ((_ , _) , _)  ((_ , _) , _)) bₛ b₁ p = refl

sigStrNatS : (i : ℕ) {n m : ℕ} (g : MorS n m) (a : MorS m (suc m)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a))
                                                                   (b : MorS (suc m) (suc (suc m))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁)) (p : ∂₀S a ≡ ∂₁S g)
                                                                   (let b₀ = ap ftS (is-section₀S b bₛ b₁ ∙ (UUStr=S i (ElStrS i a aₛ a₁))) ∙ ElStr=S i a aₛ a₁ ∙ p)
             →  starTmS g (sigStrS i a aₛ a₁ b bₛ b₁) (sigStr₀S i a aₛ a₁ b bₛ b₁ ∙ p) ≡ sigStrS i (starTmS g a p) (ssₛS (compS a g (! p))) (starTm₁S g a aₛ p a₁ ∙ UUStrNatS g (∂₀S a) p ∙ ap (UUStrS i) (! (ss₀S (compS a g (! p)) ∙ comp₀S a g (! p))))
                                                                           (starTm+S g b b₀) (ssₛS (compS b (qqS g (∂₀S b) (! b₀)) (qq₁S g (∂₀S b) (! b₀))))
                                                                           (starTm+₁S g b bₛ b₁ b₀ ∙ UUStrNatS (qqS g (ftS (UUStrS i (ElStrS i a aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i a aₛ a₁)) ∙ ElStr=S i a aₛ a₁ ∙ p))) (ElStrS i a aₛ a₁) (! (qq₁S g (ftS (UUStrS i (ElStrS i a aₛ a₁))) (! (ap ftS (! (is-section₀S b bₛ b₁))  ∙ b₀)) ∙ UUStr=S i (ElStrS i a aₛ a₁))) ∙ ap (UUStrS i) (qq₀S g (ftS (UUStrS i (ElStrS i a aₛ a₁))) (! (ap ftS (! (is-section₀S b bₛ b₁))  ∙ b₀)) ∙ ap2-irr starS {a = g} refl (UUStr=S i (ElStrS i a aₛ a₁)) {b = ! (ap ftS (! (is-section₀S b bₛ b₁)) ∙ b₀)} {b' = ! (ElStr=S i a aₛ a₁ ∙ p)} ∙ (ElStrNatS g a aₛ a₁ p)))
sigStrNatS i = //-elimP (λ g → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ p → sigStrNatS-// i g a aₛ a₁ b bₛ b₁ p)))


pairStr₀S : ∀ {n} B a aₛ a₁ b bₛ b₁ → _
pairStr₀S {n} B a aₛ a₁ b bₛ b₁ = is-section₀S {n} (pairStrS B a aₛ a₁ b bₛ b₁) (pairStrₛS B a aₛ a₁ b bₛ b₁) (pairStr₁S B a aₛ a₁ b bₛ b₁) ∙ SigStr=S B

pairStrNatS-// : {n m : ℕ} (g : DMor n m) (B : DCtx (suc (suc m))) (a : DMor m (suc m)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (b : DMor m (suc m)) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj B) a₁) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))
                 (let a₀ = is-section₀S (proj a) aₛ a₁ ∙ p) (let b₀ = is-section₀S (proj b) bₛ b₁ ∙ ft-starS (proj a) (proj B) a₁ ∙ a₀)
             → starTmS (proj g) (pairStrS (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁) (pairStr₀S (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁ ∙ p) ≡ pairStrS (star+S (proj g) (proj B) p) (starTmS (proj g) (proj a) a₀) (ssₛS (compS (proj a) (proj g) (! a₀))) (starTm₁S (proj g) (proj a) aₛ a₀ a₁ ∙ ! (ft-starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p)) ∙ qq₀S (proj g) (ftS (proj B)) (! p))) (starTmS (proj g) (proj b) b₀) (ssₛS (compS (proj b) (proj g) (! b₀))) (starTm₁S (proj g) (proj b) bₛ b₀ b₁ ∙ starstar synCCat (proj g) (proj a) aₛ (proj B) {a₁ = a₁} {g₁ = ! (ft-starS (proj a) (proj B) a₁ ∙ a₀)} {a₀ = a₀} {p = p})
pairStrNatS-// (dmor (_ , _) (_ , _) δ _) (((_ , _) , _), ((_ , _) , _)) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) aₛ a₁ (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) bₛ b₁ p = up-to-rhsTyEq (ap (_[_]Ty _) (idMor[]Mor δ))

pairStrNatS : {n m : ℕ} (g : MorS n m) (B : ObS (suc (suc m))) (a : MorS m (suc m)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) (b : MorS m (suc m)) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ starS a B a₁) (p : ftS (ftS B) ≡ ∂₁S g)
                 (let a₀ = is-section₀S a aₛ a₁ ∙ p) (let b₀ = is-section₀S b bₛ b₁ ∙ ft-starS a B a₁ ∙ a₀)
             → starTmS g (pairStrS B a aₛ a₁ b bₛ b₁) (pairStr₀S B a aₛ a₁ b bₛ b₁ ∙ p) ≡ pairStrS (star+S g B p) (starTmS g a a₀) (ssₛS (compS a g (! a₀))) (starTm₁S g a aₛ a₀ a₁ ∙ ! (ft-starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p)) ∙ qq₀S g (ftS B) (! p))) (starTmS g b b₀) (ssₛS (compS b g (! b₀))) (starTm₁S g b bₛ b₀ b₁ ∙ starstar synCCat g a aₛ B {a₀ = a₀} {p = p})
pairStrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ p → pairStrNatS-// g B a aₛ a₁ b bₛ b₁ p))))

pr1Str₀S : ∀ {n} B u uₛ u₁ → _
pr1Str₀S {n} B u uₛ u₁ = is-section₀S {n} (pr1StrS B u uₛ u₁) (pr1StrₛS B u uₛ u₁) (pr1Str₁S B u uₛ u₁)

pr1StrNatS-// : {n m : ℕ} (g : DMor n m) (B : DCtx (suc (suc m))) (u : DMor m (suc m)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))
                (let u₀ = is-section₀S (proj u) uₛ u₁ ∙ SigStr=S (proj B) ∙ p)
             → starTmS (proj g) (pr1StrS (proj B) (proj u) uₛ u₁) (pr1Str₀S (proj B) (proj u) uₛ u₁ ∙ p) ≡ pr1StrS (star+S (proj g) (proj B) p) (starTmS (proj g) (proj u) u₀) (ssₛS (compS (proj u) (proj g) (! u₀))) (starTm₁S (proj g) (proj u) uₛ u₀ u₁ ∙ SigStrNatS (proj g) (proj B) p)
pr1StrNatS-// (dmor (_ , _) (_ , _) δ _) (((_ , _) , _), ((_ , _) , _)) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) uₛ u₁ p = up-to-rhsTyEq (ap (_[_]Ty _) (idMor[]Mor δ))


pr1StrNatS : {n m : ℕ} (g : MorS n m) (B : ObS (suc (suc m))) (u : MorS m (suc m)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B) (p : ftS (ftS B) ≡ ∂₁S g)
                (let u₀ = is-section₀S u uₛ u₁ ∙ SigStr=S B ∙ p)
             → starTmS g (pr1StrS B u uₛ u₁) (pr1Str₀S B u uₛ u₁ ∙ p) ≡ pr1StrS (star+S g B p) (starTmS g u u₀) (ssₛS (compS u g (! u₀))) (starTm₁S g u uₛ u₀ u₁ ∙ SigStrNatS g B p)
pr1StrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ u uₛ u₁ p → pr1StrNatS-// g B u uₛ u₁ p)))



pr2Str₀S : ∀ {n} B u uₛ u₁ → _
pr2Str₀S {n} B u uₛ u₁ = is-section₀S {n} (pr2StrS B u uₛ u₁) (pr2StrₛS B u uₛ u₁) (pr2Str₁S B u uₛ u₁) ∙ ft-starS (pr1StrS B u uₛ u₁) B (pr1Str₁S B u uₛ u₁) ∙ pr1Str₀S B u uₛ u₁

pr2StrNatS-// : {n m : ℕ} (g : DMor n m) (B : DCtx (suc (suc m))) (u : DMor m (suc m)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))
                (let u₀ = is-section₀S (proj u) uₛ u₁ ∙ SigStr=S (proj B) ∙ p)
             → starTmS (proj g) (pr2StrS (proj B) (proj u) uₛ u₁) (pr2Str₀S (proj B) (proj u) uₛ u₁ ∙ p) ≡ pr2StrS (star+S (proj g) (proj B) p) (starTmS (proj g) (proj u) u₀) (ssₛS (compS (proj u) (proj g) (! u₀))) (starTm₁S (proj g) (proj u) uₛ u₀ u₁ ∙ SigStrNatS (proj g) (proj B) p)
pr2StrNatS-// (dmor (_ , _) (_ , _) δ _) (((_ , A) , B), ((_ , _) , _)) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , u) (_ , _)) uₛ u₁ p = up-to-rhsTyEq ((ap (_[_]Ty _) (idMor[]Mor δ) ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty _) (ap (λ z → (z , (pr1 A B u) [ δ ]Tm)) (idMor[]Mor δ))) ∙ ! ([]Ty-assoc _ _ _ ∙ (ap (_[_]Ty _) (ap (λ z → (z  , (pr1 A B u) [ δ ]Tm)) (weakenMorInsert _ _ _ ∙ [idMor]Mor δ)))))


pr2StrNatS : {n m : ℕ} (g : MorS n m) (B : ObS (suc (suc m))) (u : MorS m (suc m)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ SigStrS B) (p : ftS (ftS B) ≡ ∂₁S g)
                (let u₀ = is-section₀S u uₛ u₁ ∙ SigStr=S B ∙ p)
             → starTmS g (pr2StrS B u uₛ u₁) (pr2Str₀S B u uₛ u₁ ∙ p) ≡ pr2StrS (star+S g B p) (starTmS g u u₀) (ssₛS (compS u g (! u₀))) (starTm₁S g u uₛ u₀ u₁ ∙ SigStrNatS g B p)
pr2StrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ u uₛ u₁ p → pr2StrNatS-// g B u uₛ u₁ p)))


natStr₀S : ∀ {n} i X → _
natStr₀S {n} i X = is-section₀S {n} (natStrS i X) (natStrₛS i X) (natStr₁S i X) ∙ UUStr=S i X

natStrNatS-// : (i : ℕ) {n m : ℕ} (g : DMor n m) (X : DCtx m) (p : proj X ≡ ∂₁S (proj g))
             → starTmS (proj g) (natStrS i (proj X)) (natStr₀S i (proj X) ∙ p) ≡ natStrS i (∂₀S (proj g))
natStrNatS-// i (dmor (_ , _) (_ , _) _ _) (_ , _) p = refl

natStrNatS : (i : ℕ) {n m : ℕ} (g : MorS n m) (X : ObS m) (p : X ≡ ∂₁S g)
             → starTmS g (natStrS i X) (natStr₀S i X ∙ p) ≡ natStrS i (∂₀S g)
natStrNatS i = //-elimP (λ g → //-elimP (λ X p → natStrNatS-// i g X p))


zeroStr₀S : ∀ {n} X → _
zeroStr₀S {n} X = is-section₀S {n} (zeroStrS X) (zeroStrₛS X) (zeroStr₁S X) ∙ NatStr=S X

zeroStrNatS-// : {n m : ℕ} (g : DMor n m) (X : DCtx m) (p : proj X ≡ ∂₁S (proj g))
             → starTmS (proj g) (zeroStrS (proj X)) (zeroStr₀S (proj X) ∙ p) ≡ zeroStrS (∂₀S (proj g))
zeroStrNatS-// (dmor (_ , _) (_ , _) _ _) (_ , _) p = refl

zeroStrNatS : {n m : ℕ} (g : MorS n m) (X : ObS m) (p : X ≡ ∂₁S g)
             → starTmS g (zeroStrS X) (zeroStr₀S X ∙ p) ≡ zeroStrS (∂₀S g)
zeroStrNatS = //-elimP (λ g → //-elimP (λ X p → zeroStrNatS-// g X p))


sucStr₀S : ∀ {n} u uₛ u₁ → _
sucStr₀S {n} u uₛ u₁ = is-section₀S {n} (sucStrS u uₛ u₁) (sucStrₛS u uₛ u₁) (sucStr₁S u uₛ u₁) ∙ NatStr=S (∂₀S u)

sucStrNatS-// : {n m : ℕ} (g : DMor n m) (u : DMor m (suc m)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (∂₀S (proj u))) (p : ∂₀S (proj u) ≡ ∂₁S (proj g))
             → starTmS (proj g) (sucStrS (proj u) uₛ u₁) (sucStr₀S (proj u) uₛ u₁ ∙ p) ≡ sucStrS (starTmS (proj g) (proj u) p) (ssₛS (compS (proj u) (proj g) (! p))) (starTm₁S (proj g) (proj u) uₛ p u₁ ∙ NatStrNatS (proj g) (∂₀S (proj u)) p ∙ ap NatStrS (! (ss₀S (compS (proj u) (proj g) (! p)) ∙ comp₀S (proj u) (proj g) (! p))))
sucStrNatS-// (dmor (_ , _) (_ , _) _ _) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) uₛ u₁ p = refl


sucStrNatS : {n m : ℕ} (g : MorS n m) (u : MorS m (suc m)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ NatStrS (∂₀S u)) (p : ∂₀S u ≡ ∂₁S g)
             → starTmS g (sucStrS u uₛ u₁) (sucStr₀S u uₛ u₁ ∙ p) ≡ sucStrS (starTmS g u p) (ssₛS (compS u g (! p))) (starTm₁S g u uₛ p u₁ ∙ NatStrNatS g (∂₀S u) p ∙ ap NatStrS (! (ss₀S (compS u g (! p)) ∙ comp₀S u g (! p))))
sucStrNatS = //-elimP (λ g → //-elimP (λ u uₛ u₁ p → sucStrNatS-// g u uₛ u₁ p))


idStr₀S : ∀ {n} i a aₛ a₁ u uₛ u₁ v vₛ v₁ → _
idStr₀S {n} i a aₛ a₁ u uₛ u₁ v vₛ v₁ = is-section₀S {n} (idStrS i a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStrₛS i a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStr₁S i a aₛ a₁ u uₛ u₁ v vₛ v₁) ∙ UUStr=S i (∂₀S a)

idStrNatS-// : (i : ℕ) {n m : ℕ} (g : DMor n m) (a : DMor m (suc m)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (u : DMor m (suc m)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj a) aₛ a₁)
                                                (v : DMor m (suc m)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj a) aₛ a₁) (p : ∂₀S (proj a) ≡ ∂₁S (proj g))
                                                (let u₀ = is-section₀S (proj u) uₛ u₁ ∙ ElStr=S i (proj a) aₛ a₁ ∙ p) (let v₀ = is-section₀S (proj v) vₛ v₁ ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)
             → starTmS (proj g) (idStrS i (proj a) aₛ a₁ (proj u) uₛ u₁ (proj v) vₛ v₁) (idStr₀S i (proj a) aₛ a₁ (proj u) uₛ u₁ (proj v) vₛ v₁ ∙ p) ≡ idStrS i (starTmS (proj g) (proj a) p) (ssₛS (compS (proj a) (proj g) (! p))) (starTm₁S (proj g) (proj a) aₛ p a₁ ∙ UUStrNatS (proj g) (∂₀S (proj a)) p ∙ ap (UUStrS i) (! (ss₀S (compS (proj a) (proj g) (! p)) ∙ comp₀S (proj a) (proj g) (! p))))
                                                                                   (starTmS (proj g) (proj u) u₀) (ssₛS (compS (proj u) (proj g) (! u₀))) (starTm₁S (proj g) (proj u) uₛ u₀ u₁ ∙ ElStrNatS (proj g) (proj a) aₛ a₁ p) (starTmS (proj g) (proj v) v₀) (ssₛS (compS (proj v) (proj g) (! v₀))) (starTm₁S (proj g) (proj v) vₛ v₀ v₁ ∙ ElStrNatS (proj g) (proj a) aₛ a₁ p)
idStrNatS-// i (dmor (_ , _) (_ , _) _ _) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) aₛ a₁ (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) uₛ u₁ (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) vₛ v₁ p = refl

idStrNatS : (i : ℕ) {n m : ℕ} (g : MorS n m) (a : MorS m (suc m)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (u : MorS m (suc m)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ ElStrS i a aₛ a₁)
                                                (v : MorS m (suc m)) (vₛ : is-sectionS v) (v₁ : ∂₁S v ≡ ElStrS i a aₛ a₁) (p : ∂₀S a ≡ ∂₁S g)
                                                (let u₀ = is-section₀S u uₛ u₁ ∙ ElStr=S i a aₛ a₁ ∙ p) (let v₀ = is-section₀S v vₛ v₁ ∙ ElStr=S i a aₛ a₁ ∙ p)
             → starTmS g (idStrS i a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStr₀S i a aₛ a₁ u uₛ u₁ v vₛ v₁ ∙ p) ≡ idStrS i (starTmS g a p) (ssₛS (compS a g (! p))) (starTm₁S g a aₛ p a₁ ∙ UUStrNatS g (∂₀S a) p ∙ ap (UUStrS i) (! (ss₀S (compS a g (! p)) ∙ comp₀S a g (! p))))
                                                                                   (starTmS g u u₀) (ssₛS (compS u g (! u₀))) (starTm₁S g u uₛ u₀ u₁ ∙ ElStrNatS g a aₛ a₁ p) (starTmS g v v₀) (ssₛS (compS v g (! v₀))) (starTm₁S g v vₛ v₀ v₁ ∙ ElStrNatS g a aₛ a₁ p)
idStrNatS i = //-elimP (λ g → //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ p → idStrNatS-// i g a aₛ a₁ u uₛ u₁ v vₛ v₁ p))))




reflStr₀S : ∀ {n} A u uₛ u₁ → _
reflStr₀S {n} A u uₛ u₁ = is-section₀S {n} (reflStrS A u uₛ u₁) (reflStrₛS A u uₛ u₁) (reflStr₁S A u uₛ u₁) ∙ IdStr=S A u uₛ u₁ u uₛ u₁

reflStrNatS-// : {n m : ℕ} (g : DMor n m) (A : DCtx (suc m)) (u : DMor m (suc m)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ (proj A)) (p : ftS (proj A) ≡ ∂₁S (proj g))
                 (let u₀ = is-section₀S (proj u) uₛ u₁ ∙ p)
             → starTmS (proj g) (reflStrS (proj A) (proj u) uₛ u₁) (reflStr₀S (proj A) (proj u) uₛ u₁ ∙ p) ≡ reflStrS (starS (proj g) (proj A) (! p)) (starTmS (proj g) (proj u) u₀) (ssₛS (compS (proj u) (proj g) (! u₀))) (starTm₁S (proj g) (proj u) uₛ u₀ u₁)
reflStrNatS-// (dmor (_ , _) (_ , _) δ _) ((_ , A) , (_ , _)) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , u) (_ , _)) uₛ u₁ p = up-to-rhsTyEq (ap (_[_]Ty (id A u u)) (idMor[]Mor δ))

reflStrNatS : {n m : ℕ} (g : MorS n m) (A : ObS (suc m)) (u : MorS m (suc m)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ A) (p : ftS A ≡ ∂₁S g)
                 (let u₀ = is-section₀S u uₛ u₁ ∙ p)
             → starTmS g (reflStrS A u uₛ u₁) (reflStr₀S A u uₛ u₁ ∙ p) ≡ reflStrS (starS g A (! p)) (starTmS g u u₀) (ssₛS (compS u g (! u₀))) (starTm₁S g u uₛ u₀ u₁)
reflStrNatS = //-elimP (λ g → //-elimP (λ A → //-elimP (λ u uₛ u₁ p → reflStrNatS-// g A u uₛ u₁ p)))

betaPiStrS-// : (B : DCtx (suc (suc n))) (u : DMor (suc n) (suc (suc n))) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B))
            → appStrS (proj B) (lamStrS (proj B) (proj u) uₛ u₁) (lamStrₛS (proj B) (proj u) uₛ u₁) (lamStr₁S (proj B) (proj u) uₛ u₁) (proj a) aₛ a₁ ≡ starTmS (proj a) (proj u) (is-section₀S (proj u) uₛ refl ∙ ap ftS u₁ ∙ ! a₁)
betaPiStrS-// (((Γ , A) , B) , ((dΓ , dA) , dB)) uu@(dmor (ΓAu  , _) ((ΓA'u , Bu) , (dΓA'u , dBu)) (idu , u) (didu , du[idu])) uₛ u₁
            aa@(dmor (Γa , _) ((Γ'a , Aa) , (_ , dAa)) (ida , a) (dida , da[ida])) aₛ a₁ =
                  let (dΓA'u=ΓA , _ , _ , dBu=B , _) = reflect u₁
                      ((_ , dΓA'u=ΓAu) , _) = reflect uₛ
                      (dΓ'a=Γ , _ , _ , dAa=A , _) = reflect a₁
                      ((_ , dΓ'a=Γa) , _) = reflect aₛ
                      dΓ=Γa = CtxTran (CtxSymm dΓ'a=Γ) dΓ'a=Γa
                      dΓA=ΓAu = CtxTran (CtxSymm dΓA'u=ΓA) dΓA'u=ΓAu
                      da = (DMor-dTm aa aₛ a₁)
                      du = (DMor-dTm uu uₛ u₁)
                      did=ida = MorSymm dΓ dΓ (ConvMorEq (sectionS-eq {dA = dAa} {dδ = dida} {du = da[ida]} aₛ) (CtxSymm dΓ=Γa) dΓ'a=Γ)
                      did=idu = MorSymm (dΓ , dA) (dΓ , dA) (ConvMorEq (sectionS-eq {dA = dBu} {dδ = didu} {du = du[idu]} uₛ) (CtxSymm dΓA=ΓAu) dΓA'u=ΓA)
                  in
                  eq ((dΓ=Γa , (dΓ=Γa ,, SubstTyMorEq2 dΓ (dΓ , dA) (ConvTyEq (TySymm dBu=B) dΓA'u=ΓA) (MorTran {δ' = ida , a} dΓ (dΓ , dA) (did=ida , TmRefl (congTm (! ([idMor]Ty A)) refl da)) (congMorEq refl refl (idMor[]Mor _) refl (SubstMorEq did=idu ((ConvMor dida (CtxSymm dΓ=Γa) dΓ'a=Γ) , (Conv dA da (congTyEq ([idMor]Ty A) refl (SubstTyMorEq dA (idMorDerivable dΓ) did=ida))))))))) , idMor+= dΓ (TmTran (SubstTm du (idMor+ dΓ da)) (BetaPi dA dB du da) (SubstTmMorEq du (idMor+ dΓ da) (did=ida , TmRefl (congTm (! ([idMor]Ty A)) refl da)))))


betaPiStrS : (B : ObS (suc (suc n))) (u : MorS (suc n) (suc (suc n))) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ B) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B)
            → appStrS B (lamStrS B u uₛ u₁) (lamStrₛS B u uₛ u₁) (lamStr₁S B u uₛ u₁) a aₛ a₁ ≡ starTmS a u (is-section₀S u uₛ refl ∙ ap ftS u₁ ∙ ! a₁)
betaPiStrS = //-elimP (λ B → //-elimP (λ u uₛ u₁ → //-elimP (λ a aₛ a₁ → betaPiStrS-// B u uₛ u₁ a aₛ a₁)))



betaSig1StrS-// : (B : DCtx (suc (suc n))) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (b : DMor n (suc n)) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj B) a₁) → pr1StrS (proj B) (pairStrS (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁) (pairStrₛS (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁) (pairStr₁S (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁) ≡ proj a
betaSig1StrS-// BB@(((Γ , A) , B) , ((dΓ , dA) , dB)) aa@(dmor (Γa  , _) ((Γ'a , Aa) , (dΓ'a , dAa)) (ida , a) (dida , da[ida])) aₛ a₁ bb@(dmor (Γb  , _) ((Γ'b , B[a]) , (dΓ'b , dB[a])) (idb , b) (didb , db[idba])) bₛ b₁ = let
           (dΓ'a=Γ , _ , _ , Γ'adAa=A , ΓdAa=A) = reflect a₁
           ((_ , dΓ'a=Γa) , _) = reflect aₛ
           dΓ=Γa = CtxTran (CtxSymm dΓ'a=Γ) dΓ'a=Γa
           did=ida = MorSymm dΓ dΓ (ConvMorEq (sectionS-eq {dA = dAa} {dδ = dida} {du = da[ida]} aₛ) (CtxSymm dΓ=Γa) dΓ'a=Γ)
           in
           eq ((dΓ=Γa , (CtxSymm dΓ'a=Γ ,, TySymm ΓdAa=A)) , (did=ida , congTmEqTy (! ([idMor]Ty A)) (BetaSig1 dA dB (DMor-dTm aa aₛ a₁) (DMor-dTm+ BB aa aₛ a₁ bb bₛ b₁))))


betaSig1StrS : (B : ObS (suc (suc n))) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) (b : MorS n (suc n)) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ starS a B a₁) → pr1StrS B (pairStrS B a aₛ a₁ b bₛ b₁) (pairStrₛS B a aₛ a₁ b bₛ b₁) (pairStr₁S B a aₛ a₁ b bₛ b₁) ≡ a
betaSig1StrS = //-elimP (λ B → //-elimP (λ u uₛ u₁ → //-elimP (λ a aₛ a₁ → betaSig1StrS-// B u uₛ u₁ a aₛ a₁)))

betaSig2StrS-// : (B : DCtx (suc (suc n))) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (b : DMor n (suc n)) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj B) a₁) → pr2StrS (proj B) (pairStrS (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁) (pairStrₛS (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁) (pairStr₁S (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁) ≡ proj b
betaSig2StrS-// BB@(((Γ , A) , B) , ((dΓ , dA) , dB)) aa@(dmor (Γa  , _) ((Γ'a , Aa) , (dΓ'a , dAa)) (ida , a) (dida , da[ida])) aₛ a₁ bb@(dmor (Γb  , _) ((Γ'b , B[a]) , (dΓ'b , dB[a])) (idb , b) (didb , db[idb])) bₛ b₁ = let
           (dΓ'a=Γ , _ , _ , Γ'adAa=A , ΓdAa=A) = reflect a₁
           ((_ , dΓ'a=Γa) , _) = reflect aₛ
           (dΓ'b=Γa , _ , _ , dB[a]=B[ida,a] , _) = reflect b₁
           ((_ , dΓ'b=Γb) , _) = reflect bₛ
           dΓ=Γa = CtxTran (CtxSymm dΓ'a=Γ) dΓ'a=Γa
           dΓa=Γb = CtxTran (CtxSymm dΓ'b=Γa) dΓ'b=Γb
           did=ida = MorSymm dΓ dΓ (ConvMorEq (sectionS-eq {dA = dAa} {dδ = dida} {du = da[ida]} aₛ) (CtxSymm dΓ=Γa) dΓ'a=Γ)
           did=idb = MorSymm dΓ dΓ (ConvMorEq (sectionS-eq {dA = dB[a]} {dδ = didb} {du = db[idb]} bₛ) (CtxSymm (CtxTran dΓ=Γa dΓa=Γb)) (CtxTran dΓ'b=Γa (CtxSymm dΓ=Γa)))
           da = DMor-dTm aa aₛ a₁
           db = DMor-dTm+ BB aa aₛ a₁ bb bₛ b₁
           dB[id,a]=B[a] = TyTran (SubstTy {δ = ida , a} dB ((ConvMor dida (CtxSymm dΓ=Γa) dΓ'a=Γ) , (Conv (SubstTy dAa (ConvMor dida (CtxSymm dΓ=Γa) (CtxRefl dΓ'a))) (ConvTm da[ida] (CtxSymm dΓ=Γa)) (SubstTyEq Γ'adAa=A (ConvMor dida (CtxSymm dΓ=Γa) (CtxRefl dΓ'a)))))) (SubstTyMorEq dB (idMor+ dΓ da) (did=ida , (TmRefl (congTm (! ([idMor]Ty A)) refl da)))) (ConvTyEq (TySymm dB[a]=B[ida,a]) (CtxTran dΓ'b=Γa (CtxSymm dΓ=Γa)))
           in
           eq ((CtxTran dΓ=Γa dΓa=Γb , (CtxTran dΓ=Γa (CtxSymm dΓ'b=Γa) ,, TyTran (SubstTy dB (idMor+ dΓ da)) (SubstTyMorEq dB (idMor+ dΓ (Pr1 dA dB (Pair dA dB da db))) (idMor+= dΓ (BetaSig1 dA dB da db))) dB[id,a]=B[a])) , (did=idb , ConvEq (SubstTy dB (idMor+ dΓ da)) (BetaSig2 dA dB da db) (congTyEq refl (! ([idMor]Ty _)) (SubstTyMorEq dB (idMor+ dΓ da) (idMor+= dΓ (TmSymm (BetaSig1 dA dB da db))))))) 


betaSig2StrS : (B : ObS (suc (suc n))) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ ftS B) (b : MorS n (suc n)) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ starS a B a₁) → pr2StrS B (pairStrS B a aₛ a₁ b bₛ b₁) (pairStrₛS B a aₛ a₁ b bₛ b₁) (pairStr₁S B a aₛ a₁ b bₛ b₁) ≡ b
betaSig2StrS = //-elimP (λ B → //-elimP (λ u uₛ u₁ → //-elimP (λ a aₛ a₁ → betaSig2StrS-// B u uₛ u₁ a aₛ a₁)))


eluuStrS-// : (i : ℕ) (X : DCtx n) → ElStrS (suc i) (uuStrS i (proj X)) (uuStrₛS i (proj X)) (uuStr₁S i (proj X) ∙ ap (UUStrS (suc i)) (! (uuStr₀S i (proj X)))) ≡ UUStrS i (proj X)
eluuStrS-// i (Γ , dΓ) = eq (CtxRefl dΓ ,, ElUU=)

eluuStrS : (i : ℕ) (X : ObS n) → ElStrS (suc i) (uuStrS i X) (uuStrₛS i X) (uuStr₁S i X ∙ ap (UUStrS (suc i)) (! (uuStr₀S i X))) ≡ UUStrS i X
eluuStrS i = //-elimP (λ X → eluuStrS-// i X)

elpiStrS-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (b : DMor (suc n) (suc (suc n))) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁))
            → ElStrS i (piStrS i (proj a) aₛ a₁ (proj b) bₛ b₁) (piStrₛS i (proj a) aₛ a₁ (proj b) bₛ b₁) (piStr₁S i (proj a) aₛ a₁ (proj b) bₛ b₁ ∙ ap (UUStrS i) (! (piStr₀S i (proj a) aₛ a₁ (proj b) bₛ b₁))) ≡ PiStrS (ElStrS i (proj b) bₛ (b₁ ∙ ap (UUStrS i) (! (is-section₀S (proj b) bₛ b₁ ∙ UUStr=S i (ElStrS i (proj a) aₛ a₁)))))
elpiStrS-// i aa@(dmor (Γa , _) ((Γ'a , Ua) , (dΓ'a , dUa)) (ida , a) (dida , da[ida])) aₛ a₁ bb@(dmor ((Γb , Elab) , _) (((Γ'b , Ela'b) , Ub) , ((dΓ'b , dEla'b) , dUb)) (idb , b) (didb , db[idb])) bₛ b₁ =
  let
    (dΓ'a=Γa , _ , _ , dUa=U , _) = reflect a₁
    ((dΓ'b=Γa , _ , _ , _ , dEla'b=Ela) , _ , _ , dBb=U , _) = reflect b₁
    ((_ , (dΓ'b=Γb , _ , _ , dEla'b=Elab , _)) , _) = reflect bₛ
    da = DMor-dTm aa aₛ a₁
    db = DMor-dTm bb bₛ b₁
  in
  eq (CtxTran (CtxSymm dΓ'b=Γa) dΓ'b=Γb ,, TyTran (Pi (El da) (El db)) (ElPi= da db) (PiCong (El da) (TyTran (ConvTy dEla'b dΓ'b=Γa) (TySymm dEla'b=Ela) (ConvTyEq dEla'b=Elab dΓ'b=Γa)) (TyRefl (El db))))

elpiStrS : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (b : MorS (suc n) (suc (suc n))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁))
            → ElStrS i (piStrS i a aₛ a₁ b bₛ b₁) (piStrₛS i a aₛ a₁ b bₛ b₁) (piStr₁S i a aₛ a₁ b bₛ b₁ ∙ ap (UUStrS i) (! (piStr₀S i a aₛ a₁ b bₛ b₁))) ≡ PiStrS (ElStrS i b bₛ (b₁ ∙ ap (UUStrS i) (! (is-section₀S b bₛ b₁ ∙ UUStr=S i (ElStrS i a aₛ a₁)))))
elpiStrS i = //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → elpiStrS-// i a aₛ a₁ b bₛ b₁))



elsigStrS-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (b : DMor (suc n) (suc (suc n))) (bₛ : is-sectionS (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj a) aₛ a₁))
            → ElStrS i (sigStrS i (proj a) aₛ a₁ (proj b) bₛ b₁) (sigStrₛS i (proj a) aₛ a₁ (proj b) bₛ b₁) (sigStr₁S i (proj a) aₛ a₁ (proj b) bₛ b₁ ∙ ap (UUStrS i) (! (sigStr₀S i (proj a) aₛ a₁ (proj b) bₛ b₁))) ≡ SigStrS (ElStrS i (proj b) bₛ (b₁ ∙ ap (UUStrS i) (! (is-section₀S (proj b) bₛ b₁ ∙ UUStr=S i (ElStrS i (proj a) aₛ a₁)))))
elsigStrS-// i aa@(dmor (Γa , _) ((Γ'a , Ua) , (dΓ'a , dUa)) (ida , a) (dida , da[ida])) aₛ a₁ bb@(dmor ((Γb , Elab) , _) (((Γ'b , Ela'b) , Ub) , ((dΓ'b , dEla'b) , dUb)) (idb , b) (didb , db[idb])) bₛ b₁ =
  let
    (dΓ'a=Γa , _ , _ , dUa=U , _) = reflect a₁
    ((dΓ'b=Γa , _ , _ , _ , dEla'b=Ela) , _ , _ , dBb=U , _) = reflect b₁
    ((_ , (dΓ'b=Γb , _ , _ , dEla'b=Elab , _)) , _) = reflect bₛ
    da = DMor-dTm aa aₛ a₁
    db = DMor-dTm bb bₛ b₁
  in
  eq (CtxTran (CtxSymm dΓ'b=Γa) dΓ'b=Γb ,, TyTran (Sig (El da) (El db)) (ElSig= da db) (SigCong (El da) (TyTran (ConvTy dEla'b dΓ'b=Γa) (TySymm dEla'b=Ela) (ConvTyEq dEla'b=Elab dΓ'b=Γa)) (TyRefl (El db))))

elsigStrS : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (b : MorS (suc n) (suc (suc n))) (bₛ : is-sectionS b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁))
            → ElStrS i (sigStrS i a aₛ a₁ b bₛ b₁) (sigStrₛS i a aₛ a₁ b bₛ b₁) (sigStr₁S i a aₛ a₁ b bₛ b₁ ∙ ap (UUStrS i) (! (sigStr₀S i a aₛ a₁ b bₛ b₁))) ≡ SigStrS (ElStrS i b bₛ (b₁ ∙ ap (UUStrS i) (! (is-section₀S b bₛ b₁ ∙ UUStr=S i (ElStrS i a aₛ a₁)))))
elsigStrS i = //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → elsigStrS-// i a aₛ a₁ b bₛ b₁))


elnatStrS-// : (i : ℕ) (X : DCtx n) → ElStrS i (natStrS i (proj X)) (natStrₛS i (proj X)) (natStr₁S i (proj X) ∙ ap (UUStrS i) (! (natStr₀S i (proj X)))) ≡ NatStrS (proj X)
elnatStrS-// i (Γ , dΓ) = eq (CtxRefl dΓ ,, ElNat=)

elnatStrS : (i : ℕ) (X : ObS n) → ElStrS i (natStrS i X) (natStrₛS i X) (natStr₁S i X ∙ ap (UUStrS i) (! (natStr₀S i X))) ≡ NatStrS X
elnatStrS i = //-elimP (λ X → elnatStrS-// i X)


elidStrS-// : (i : ℕ) (a : DMor n (suc n)) (aₛ : is-sectionS (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (u : DMor n (suc n)) (uₛ : is-sectionS (proj u)) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj a) aₛ a₁)
                      (v : DMor n (suc n)) (vₛ : is-sectionS (proj v)) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj a) aₛ a₁) → ElStrS i (idStrS i (proj a) aₛ a₁ (proj u) uₛ u₁ (proj v) vₛ v₁) (idStrₛS i (proj a) aₛ a₁ (proj u) uₛ u₁ (proj v) vₛ v₁) (idStr₁S i (proj a) aₛ a₁ (proj u) uₛ u₁ (proj v) vₛ v₁  ∙ ap (UUStrS i) (! (idStr₀S i (proj a) aₛ a₁ (proj u) uₛ u₁ (proj v) vₛ v₁))) ≡ IdStrS (ElStrS i (proj a) aₛ a₁) (proj u) uₛ u₁ (proj v) vₛ v₁
elidStrS-// i aa@(dmor (Γa , dΓa) ((Γ'a , Ua) , (dΓ'a , dUa)) (ida , a) (dida , da[ida])) aₛ a₁ uu@(dmor (Γu , _) ((Γ'u , Elau) , (dΓ'u , dElau)) (idu , u) (didu , du[idu])) uₛ u₁ vv@(dmor (Γv , _) ((Γ'v , Elav) , (dΓ'v , dElav)) (idv , v) (didv , dv[idv])) vₛ v₁ = eq (CtxRefl dΓa ,, ElId= (DMor-dTm aa aₛ a₁) (DMor-dTm uu uₛ u₁) (DMor-dTm vv vₛ v₁))


elidStrS : (i : ℕ) (a : MorS n (suc n)) (aₛ : is-sectionS a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (u : MorS n (suc n)) (uₛ : is-sectionS u) (u₁ : ∂₁S u ≡ ElStrS i a aₛ a₁)
                   (v : MorS n (suc n)) (vₛ : is-sectionS v) (v₁ : ∂₁S v ≡ ElStrS i a aₛ a₁) → ElStrS i (idStrS i a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStrₛS i a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStr₁S i a aₛ a₁ u uₛ u₁ v vₛ v₁  ∙ ap (UUStrS i) (! (idStr₀S i a aₛ a₁ u uₛ u₁ v vₛ  v₁))) ≡ IdStrS (ElStrS i a aₛ a₁) u uₛ u₁ v vₛ v₁
elidStrS i = //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → elidStrS-// i a aₛ a₁ u uₛ u₁ v vₛ v₁)))

open StructuredCCat

strSynCCat : StructuredCCat

ccat strSynCCat = synCCat

CCatwithUU.UUStr (ccatUU strSynCCat) = UUStrS
CCatwithUU.UUStr= (ccatUU strSynCCat) = UUStr=S _ _
CCatwithUU.UUStrNat (ccatUU strSynCCat) g {X = X} p = UUStrNatS g X p

CCatwithEl.ElStr (ccatEl strSynCCat) = ElStrS
CCatwithEl.ElStr= (ccatEl strSynCCat) {v = v} = ElStr=S _ v _ _
CCatwithEl.ElStrNat (ccatEl strSynCCat) g {v = v} p = ElStrNatS g v _ _ p

CCatwithPi.PiStr (ccatPi strSynCCat) = PiStrS
CCatwithPi.PiStr= (ccatPi strSynCCat) {B = B} = PiStr=S B
CCatwithPi.PiStrNat (ccatPi strSynCCat) g {B = B} p = PiStrNatS g B p

CCatwithSig.SigStr (ccatSig strSynCCat) = SigStrS
CCatwithSig.SigStr= (ccatSig strSynCCat) {B = B} = SigStr=S B
CCatwithSig.SigStrNat (ccatSig strSynCCat) g {B = B} p = SigStrNatS g B p

CCatwithNat.NatStr (ccatNat strSynCCat) = NatStrS
CCatwithNat.NatStr= (ccatNat strSynCCat) = NatStr=S _
CCatwithNat.NatStrNat (ccatNat strSynCCat) g {X = X} p = NatStrNatS g X p

CCatwithId.IdStr (ccatId strSynCCat) = IdStrS
CCatwithId.IdStr= (ccatId strSynCCat) {A = A} {a = a} {b = b} = IdStr=S A a _ _ b _ _
CCatwithId.IdStrNat (ccatId strSynCCat) g {A = A} {a = u} {b = v} p = IdStrNatS g A u _ _ v _ _ p



CCatwithuu.uuStr (ccatuu strSynCCat) = uuStrS
CCatwithuu.uuStrₛ (ccatuu strSynCCat) {X = X} = uuStrₛS _ X
CCatwithuu.uuStr₁ (ccatuu strSynCCat) {X = X} = uuStr₁S _ X
CCatwithuu.uuStrNat (ccatuu strSynCCat) g {X = X} p = uuStrNatS _ g X p

CCatwithpi.piStr (ccatpi strSynCCat) = piStrS
CCatwithpi.piStrₛ (ccatpi strSynCCat) {a = a} {b = b} = piStrₛS _ a _ _ b _ _
CCatwithpi.piStr₁ (ccatpi strSynCCat) {a = a} {b = b} = piStr₁S _ a _ _ b _ _
CCatwithpi.piStrNat (ccatpi strSynCCat) g {a = a} {b = b} p = piStrNatS _ g a _ _ b _ _ p

CCatwithlam.lamStr (ccatlam strSynCCat) = lamStrS
CCatwithlam.lamStrₛ (ccatlam strSynCCat) {B = B} {u = u} = lamStrₛS B u _ _
CCatwithlam.lamStr₁ (ccatlam strSynCCat) {B = B} {u = u} = lamStr₁S B u _ _
CCatwithlam.lamStrNat (ccatlam strSynCCat) g {B = B} {u = u} p = lamStrNatS g B u _ _ p

CCatwithapp.appStr (ccatapp strSynCCat) = appStrS
CCatwithapp.appStrₛ (ccatapp strSynCCat) {B = B} {f = f} {a = a} = appStrₛS B f _ _ a _ _
CCatwithapp.appStr₁ (ccatapp strSynCCat) {B = B} {f = f} {a = a} = appStr₁S B f _ _ a _ _
CCatwithapp.appStrNat (ccatapp strSynCCat) g {B = B} {f = f} {a = a} p = appStrNatS g B f _ _ a _ _ p

CCatwithsig.sigStr (ccatsig strSynCCat) = sigStrS
CCatwithsig.sigStrₛ (ccatsig strSynCCat) {a = a} {b = b} = sigStrₛS _ a _ _ b _ _
CCatwithsig.sigStr₁ (ccatsig strSynCCat) {a = a} {b = b} = sigStr₁S _ a _ _ b _ _
CCatwithsig.sigStrNat (ccatsig strSynCCat) g {a = a} {b = b} p = sigStrNatS _ g a _ _ b _ _ p

CCatwithpair.pairStr (ccatpair strSynCCat) = pairStrS
CCatwithpair.pairStrₛ (ccatpair strSynCCat) {B = B} {a = a} {b = b} = pairStrₛS B a _ _ b _ _
CCatwithpair.pairStr₁ (ccatpair strSynCCat) {B = B} {a = a} {b = b} = pairStr₁S B a _ _ b _ _
CCatwithpair.pairStrNat (ccatpair strSynCCat) g {B = B} {a = a} {b = b} p = pairStrNatS g B a _ _ b _ _ p

CCatwithpr1.pr1Str (ccatpr1 strSynCCat) = pr1StrS
CCatwithpr1.pr1Strₛ (ccatpr1 strSynCCat) {B = B} {u = u} = pr1StrₛS B u _ _
CCatwithpr1.pr1Str₁ (ccatpr1 strSynCCat) {B = B} {u = u} = pr1Str₁S B u _ _
CCatwithpr1.pr1StrNat (ccatpr1 strSynCCat) g {B = B} {u = u} p = pr1StrNatS g B u _ _ p

CCatwithpr2.pr2Str (ccatpr2 strSynCCat) = pr2StrS
CCatwithpr2.pr2Strₛ (ccatpr2 strSynCCat) {B = B} {u = u} = pr2StrₛS B u _ _
CCatwithpr2.pr2Str₁ (ccatpr2 strSynCCat) {B = B} {u = u} = pr2Str₁S B u _ _
CCatwithpr2.pr2StrNat (ccatpr2 strSynCCat) g {B = B} {u = u} p  = pr2StrNatS g B u _ _ p

CCatwithnat.natStr (ccatnat strSynCCat) = natStrS
CCatwithnat.natStrₛ (ccatnat strSynCCat) {X = X} = natStrₛS _ X
CCatwithnat.natStr₁ (ccatnat strSynCCat) {X = X} = natStr₁S _ X
CCatwithnat.natStrNat (ccatnat strSynCCat) g {X = X} p = natStrNatS _ g X p

CCatwithzero.zeroStr (ccatzero strSynCCat) = zeroStrS
CCatwithzero.zeroStrₛ (ccatzero strSynCCat) {X = X} = zeroStrₛS X
CCatwithzero.zeroStr₁ (ccatzero strSynCCat) {X = X} = zeroStr₁S X
CCatwithzero.zeroStrNat (ccatzero strSynCCat) g {X = X} p = zeroStrNatS g X p

CCatwithsuc.sucStr (ccatsuc strSynCCat) = sucStrS
CCatwithsuc.sucStrₛ (ccatsuc strSynCCat) {u = u} = sucStrₛS u _ _
CCatwithsuc.sucStr₁ (ccatsuc strSynCCat) {u = u} = sucStr₁S u _ _
CCatwithsuc.sucStrNat (ccatsuc strSynCCat) g {u = u} p = sucStrNatS g u _ _ p

CCatwithid.idStr (ccatid strSynCCat) = idStrS
CCatwithid.idStrₛ (ccatid strSynCCat) {a = a} {u = u} {v = v} = idStrₛS _ a _ _ u _ _ v _ _
CCatwithid.idStr₁ (ccatid strSynCCat) {a = a} {u = u} {v = v} = idStr₁S _ a _ _ u _ _ v _ _
CCatwithid.idStrNat (ccatid strSynCCat) g {a = a} {u = u} {v = v} p = idStrNatS _ g a _ _ u _ _ v _ _ p

CCatwithrefl.reflStr (ccatrefl strSynCCat) = reflStrS
CCatwithrefl.reflStrₛ (ccatrefl strSynCCat) {A = A} {a = a} = reflStrₛS A a _ _
CCatwithrefl.reflStr₁ (ccatrefl strSynCCat) {A = A} {a = a} = reflStr₁S A a _ _
CCatwithrefl.reflStrNat (ccatrefl strSynCCat) g {A = A} {u = u} p = reflStrNatS g A u _ _ p


betaPiStr strSynCCat {B = B} {u = u} {a = a} = betaPiStrS B u _ _ a _ _
betaSig1Str strSynCCat {B = B} {a = a} {b = b} = betaSig1StrS B a _ _ b _ _
betaSig2Str strSynCCat {B = B} {a = a} {b = b} = betaSig2StrS B a _ _ b _ _
eluuStr strSynCCat {X = X} = eluuStrS _ X
elpiStr strSynCCat {a = a} {b = b} = elpiStrS _ a _ _ b _ _
elsigStr strSynCCat {a = a} {b = b} = elsigStrS _ a _ _ b _ _
elnatStr strSynCCat {X = X} = elnatStrS _ X
elidStr strSynCCat {a = a} {u = u} {v = v} = elidStrS _ a _ _ u _ _ v _ _
