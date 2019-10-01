{-# OPTIONS --rewriting --prop --without-K #-}

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

∂₀S-// : DMor n m → DCtx n
∂₀S-// δ = ctx (lhs δ) ,' der (lhs δ)

∂₀S : {n m : ℕ} → MorS n m → ObS n
∂₀S = //-rec (λ δ → proj (∂₀S-// δ)) (λ r → eq (box (unMor≃-lhs r)))

∂₁S-// : DMor n m → DCtx m
∂₁S-// δ = ctx (rhs δ) ,' der (rhs δ)

∂₁S : {n m : ℕ} → MorS n m → ObS m
∂₁S = //-rec (λ δ → proj (∂₁S-// δ)) (λ r → eq (box (unMor≃-rhs r)))

idS-// : (n : ℕ) → DCtx n → DMor n n
idS-// n Γ = dmor Γ Γ (idMor n) (idMorDerivable (der Γ))

idS : (n : ℕ) → ObS n → MorS n n
idS n = //-rec (λ Γ → proj (idS-// n Γ)) (λ rΓ → eq (box (unOb≃ rΓ) (unOb≃ rΓ) (MorRefl (idMorDerivable (CtxEqCtx1 (unOb≃ rΓ))))))

id₀S : (n : ℕ) (X : ObS n) → ∂₀S (idS n X) ≡ X
id₀S n = //-elimP (λ Γ → eq (box (CtxRefl (der Γ))))

id₁S : (n : ℕ) (X : ObS n) → ∂₁S (idS n X) ≡ X
id₁S n = //-elimP (λ Γ → eq (box (CtxRefl (der Γ))))

compS-// : (g : DMor m k) (f : DMor n m) (X : DCtx m) (g₀ : ∂₀S (proj g) ≡ proj X) (f₁ : ∂₁S (proj f) ≡ proj X) → DMor n k
compS-// g f X g₀ f₁ = dmor (lhs f) (rhs g) (mor g [ mor f ]Mor) (SubstMor (morDer g) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb (f₁ ∙ ! g₀))))

compS-eq : (g g' : DMor m k) (rg : g ≃ g') (f f' : DMor n m) (rf : f ≃ f') (X X' : DCtx m) (rX : X ≃ X') (g₀ : ∂₀S (proj g)≡ proj X) (g'₀ : ∂₀S (proj g') ≡ proj X') (f₁ : ∂₁S (proj f) ≡ proj X) (f'₁ : ∂₁S (proj f') ≡ proj X') → proj {R = MorEquiv} (compS-// g f X g₀ f₁) ≡ proj (compS-// g' f' X' g'₀ f'₁)
compS-eq g g' rg f f' rf X X' rX g₀ g'₀ f₁ f'₁ = eq (box (unMor≃-lhs rf) (unMor≃-rhs rg) (SubstMorFullEq (der (lhs f)) (der (lhs g)) (der (rhs g)) (unMor≃-mor rg) (ConvMorEq (unMor≃-mor rf) (CtxRefl (der (lhs f))) (reflectOb (f₁ ∙ ! g₀)))))
 
compS : (g : MorS m k) (f : MorS n m) (X : ObS m) (g₀ : ∂₀S g ≡ X) (f₁ : ∂₁S f ≡ X) → MorS n k
compS = //-elim-PiS (λ g → //-elim-PiS (λ f → //-elim-PiP2 (λ X g₀ f₁ → proj (compS-// g f X g₀ f₁))
                                                           (λ rX g₀ g₀' → PathOver-Prop→Cst (λ f₁ f₁' → compS-eq g g (ref g) f f (ref f) _ _ rX g₀ g₀' f₁ f₁')))
                                       (λ rf → //-elimP (λ X → PathOver-Prop→ (λ g₀ g₀' → PathOver-Prop→Cst (λ f₁ f₁' → compS-eq g g (ref g) _ _ rf X X (ref X) g₀ g₀' f₁ f₁')))))
                    (λ rg → //-elimP (λ f → PathOver-CstPi (//-elimP (λ X → PathOver-Prop→ (λ g₀ g'₀ → PathOver-Prop→Cst (λ f₁ f₁' → compS-eq _ _ rg f f (ref f) X X (ref X) g₀ g'₀ f₁ f₁'))))))

comp₀S-// : (g : DMor m k) (f : DMor n m) (X : DCtx m) (g₀ : ∂₀S (proj g) ≡ proj X) (f₁ : ∂₁S (proj f) ≡ proj X) → ∂₀S (compS (proj g) (proj f) (proj X) g₀ f₁) ≡ ∂₀S (proj f)
comp₀S-// g f X g₀ f₁ = refl

comp₀S : (g : MorS m k) (f : MorS n m) (X : ObS m) (g₀ : ∂₀S g ≡ X) (f₁ : ∂₁S f ≡ X) → ∂₀S (compS g f X g₀ f₁) ≡ ∂₀S f
comp₀S = //-elimP (λ g → //-elimP (λ f → //-elimP (λ X → comp₀S-// g f X)))

comp₁S-// :(g : DMor m k) (f : DMor n m) (X : DCtx m) (g₀ : ∂₀S (proj g) ≡ proj X) (f₁ : ∂₁S (proj f) ≡ proj X) → ∂₁S (compS (proj g) (proj f) (proj X) g₀ f₁) ≡ ∂₁S (proj g)
comp₁S-// g f X g₀ f₁ = refl

comp₁S : (g : MorS m k) (f : MorS n m) (X : ObS m) (g₀ : ∂₀S g ≡ X) (f₁ : ∂₁S f ≡ X) → ∂₁S (compS g f X g₀ f₁) ≡ ∂₁S g
comp₁S = //-elimP (λ g → //-elimP (λ f → //-elimP (λ X → comp₁S-// g f X)))

ftS-// : {n : ℕ} → DCtx (suc n) → DCtx n
ftS-// Γ = (getCtx (ctx Γ) ,' getdCtx Γ)

ftS-eq : {Γ Γ' : DCtx (suc n)} → Γ ≃ Γ' → proj {R = ObEquiv} (ftS-// Γ) ≡ proj (ftS-// Γ')
ftS-eq r = eq (box (getCtx= (unOb≃ r)))

ftS : {n : ℕ} → ObS (suc n) → ObS n
ftS = //-rec (λ X → proj (ftS-// X)) ftS-eq

ppS-// : (X : DCtx (suc n)) → DMor (suc n) n
ppS-// Γ = dmor Γ (ftS-// Γ) (weakenMor (idMor _)) (ConvMor (WeakMor (idMorDerivable (getdCtx Γ))) (CtxTy=Ctx' Γ) (CtxRefl (getdCtx Γ)))

ppS-eq : {X X' : DCtx (suc n)} (_ : X ≃ X') → proj {R = MorEquiv} (ppS-// X) ≡ proj (ppS-// X')
ppS-eq {X = X} rX = eq (box (unOb≃ rX) (getCtx= (unOb≃ rX)) (MorRefl (ConvMor (WeakMor (idMorDerivable (getdCtx X))) (CtxTy=Ctx' X) (CtxRefl (getdCtx X)))))

ppS : (X : ObS (suc n)) → MorS (suc n) n
ppS = //-rec (λ X → proj (ppS-// X)) ppS-eq

pp₀S : (X : ObS (suc n)) → ∂₀S (ppS X) ≡ X
pp₀S = //-elimP (λ {((Γ , A), (dΓ , dA)) → refl})

pp₁S : (X : ObS (suc n)) → ∂₁S (ppS X) ≡ ftS X
pp₁S = //-elimP (λ {((Γ , A), (dΓ , dA)) → refl})

ptS : ObS 0
ptS = proj (◇ ,' tt)

pt-uniqueS : (X : ObS 0) → X ≡ proj (◇ , tt)
pt-uniqueS = //-elimP (λ {(◇ , tt) → eq (box tt)})

ptmorS : (X : ObS n) → MorS n 0
ptmorS = //-rec (λ Γ → proj (dmor Γ (◇ , tt) ◇ tt)) (λ r → eq (box (unOb≃ r) tt tt))

ptmor₀S : (X : ObS n) → ∂₀S (ptmorS X) ≡ X
ptmor₀S = //-elimP (λ Γ → eq (box (CtxRefl (der Γ))))

ptmor₁S : (X : ObS n) → ∂₁S (ptmorS X) ≡ ptS
ptmor₁S = //-elimP (λ Γ → refl)

ptmor-uniqueS-// : (X : DCtx n) (f : DMor n 0) (p : ∂₀S (proj f) ≡ proj X) (q : ∂₁S (proj f) ≡ ptS) → proj f ≡ ptmorS (proj X)
ptmor-uniqueS-// X (dmor' Γ (◇ , tt) ◇ tt) p q = eq (box (reflectOb p) (reflectOb q) tt)

ptmor-uniqueS : (X : ObS n) (f : MorS n 0) (p : ∂₀S f ≡ X) (q : ∂₁S f ≡ ptS) → f ≡ ptmorS X
ptmor-uniqueS = //-elimP (λ X → //-elimP (ptmor-uniqueS-// X))

id-rightS-// : (f : DMor n m) (X : DCtx m) (f₁ : ∂₁S (proj f) ≡ proj X)→ compS (idS m (proj X)) (proj f) (proj X) (id₀S m (proj X)) f₁ ≡ (proj f)
id-rightS-// f X f₁ = eq (box (CtxRefl (der (lhs f))) (reflectOb (! f₁)) (congMorEq refl refl (! (idMor[]Mor _)) refl (MorRefl (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb f₁)))))

id-rightS : (f : MorS n m) (X : ObS m) (f₁ : ∂₁S f ≡ X) → compS (idS m X) f X (id₀S m X) f₁ ≡ f
id-rightS = //-elimP (λ f → //-elimP (λ X → id-rightS-// f X))

id-leftS-// : (f : DMor n m) (X : DCtx n) (f₀ : ∂₀S (proj f) ≡ proj X) → compS (proj f) (idS n (proj X)) (proj X) f₀ (id₁S n (proj X)) ≡ (proj f)
id-leftS-// f X f₀ = eq (box (reflectOb (! f₀)) (CtxRefl (der (rhs f))) (congMorEq refl refl (! ([idMor]Mor _)) refl (MorRefl (ConvMor (morDer f) (reflectOb f₀) (CtxRefl (der (rhs f)))))))

id-leftS : (f : MorS n m) (X : ObS n) (f₀ : ∂₀S f ≡ X) → compS f (idS n X) X f₀ (id₁S n X) ≡ f
id-leftS = //-elimP (λ f → //-elimP (λ X → id-leftS-// f X))

assocS-// : (h : DMor k l) (g : DMor m k) (f : DMor n m) (X : DCtx m) (f₁ : ∂₁S (proj f) ≡ proj X) (g₀ : ∂₀S (proj g) ≡ proj X) (Y : DCtx k) (g₁ : ∂₁S (proj g) ≡ proj Y) (h₀ : ∂₀S (proj h) ≡ proj Y) → compS (compS (proj h) (proj g) (proj Y) h₀ g₁) (proj f) (proj X) (comp₀S (proj h) (proj g) (proj Y) h₀ g₁ ∙ g₀) f₁  ≡ compS (proj h) (compS (proj g) (proj f) (proj X) g₀ f₁) (proj Y) h₀ (comp₁S (proj g) (proj f) (proj X) g₀ f₁ ∙ g₁)
assocS-// h g f X f₁ g₀ Y g₁ h₀ = eq (box (CtxRefl (der (lhs f))) (CtxRefl (der (rhs h))) (congMorEq refl refl refl ([]Mor-assoc (mor f) (mor g) (mor h)) (MorRefl (SubstMor (SubstMor (morDer h) (ConvMor (morDer g) (reflectOb (g₀ ∙ ! f₁)) (reflectOb (g₁ ∙ ! h₀)))) (morDer f)))))


assocS : (h : MorS k l) (g : MorS m k) (f : MorS n m) (X : ObS m) (f₁ : ∂₁S f ≡ X) (g₀ : ∂₀S g ≡ X) (Y : ObS k) (g₁ : ∂₁S g ≡ Y) (h₀ : ∂₀S h ≡ Y) → compS (compS h g Y h₀ g₁) f X (comp₀S h g Y h₀ g₁ ∙ g₀) f₁ ≡  compS h (compS g f X g₀ f₁) Y h₀ (comp₁S g f X g₀ f₁ ∙ g₁)
assocS = //-elimP (λ h → //-elimP (λ g → //-elimP (λ f → //-elimP (λ X f₁ g₀ → //-elimP (λ Y → assocS-// h g f X f₁ g₀ Y)))))

starS-// : (f : DMor m n) (X : DCtx (suc n)) (Y : DCtx n) (q : ftS (proj X) ≡ proj Y) (f₁ : ∂₁S (proj f) ≡ (proj Y)) → DCtx (suc m)
starS-// f X Y q f₁ = ((ctx (lhs f) , getTy X [ mor f ]Ty) ,' (der (lhs f) , (SubstTy (getdTy X) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb (f₁ ∙ ! q))))))

starS-eq : (f g : DMor m n) (r : f ≃ g) (X X' : DCtx (suc n)) (rX : X ≃ X') (Y Y' : DCtx n) (rY : Y ≃ Y') (q : ftS (proj X) ≡ proj Y) (q' : ftS (proj X') ≡ proj Y') (f₁ : ∂₁S (proj f) ≡ proj Y) (g₁ : ∂₁S (proj g) ≡ proj Y') → proj {R = ObEquiv} (starS-// f X Y q f₁) ≡ proj (starS-// g X' Y' q' g₁)
starS-eq f g r X X' rX Y Y' rY q q' f₁ g₁ = eq (box (unMor≃-lhs r ,, SubstTyFullEq (ConvTy (getdTy X') (reflectOb (q' ∙ ! (f₁ ∙ eq rY)))) (morDer f) (ConvTyEq (getTy= rX) (reflectOb (q ∙ ! f₁))) (unMor≃-mor r)))

starS : (f : MorS m n) (X : ObS (suc n)) (Y : ObS n) (q : ftS X ≡ Y) (f₁ : ∂₁S f ≡ Y) → ObS (suc m)
starS = //-elim-PiS (λ f → //-elim-PiS (λ X → //-elim-PiP2 (λ Y q f₁ → proj (starS-// f X Y q f₁))
                                                           (λ rY q q' → PathOver-Prop→Cst (λ f₁ f₁' → starS-eq f f (ref f) X X (ref X) _ _ rY q q' f₁ f₁')))
                                       (λ rX → //-elimP (λ Y → PathOver-Prop→Cst (λ q q' → funextP (λ f₁ → starS-eq f f (ref f) _ _ rX Y Y (ref Y) q q' f₁ f₁)))))
                    (λ r → //-elimP (λ X → PathOver-CstPi (//-elimP (λ Y → PathOver-Prop→ (λ q q' → PathOver-Prop→Cst (λ f₁ f₁' → starS-eq _ _ r X X (ref X) Y Y (ref Y) q q' f₁ f₁'))))))

qqS-// : (f : DMor m n) (X : DCtx (suc n)) (Y : DCtx n) (q : ftS (proj X) ≡ proj Y) (f₁ : ∂₁S (proj f) ≡  proj Y) → DMor (suc m) (suc n)
qqS-// f X Y q f₁ = dmor (starS-// f X Y q f₁) X (weakenMor+ (mor f)) (ConvMor (WeakMor+ (getdTy X) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb (f₁ ∙ ! q)))) (CtxRefl (der (lhs f) , SubstTy (getdTy X) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb (f₁ ∙ ! q))))) (CtxTy=Ctx' X))

qqS-eq : (f g : DMor m n) (r : f ≃ g) (X X' : DCtx (suc n)) (rX : X ≃ X') (Y Y' : DCtx n) (rY : Y ≃ Y') (q : ftS (proj X) ≡ proj Y) (q' : ftS (proj X') ≡ proj Y') (f₁ : ∂₁S (proj f) ≡  proj Y) (g₁ : ∂₁S (proj g) ≡ proj Y') → proj {R = MorEquiv} (qqS-// f X Y q f₁) ≡ proj (qqS-// g X' Y' q' g₁)
qqS-eq f g r X X' rX Y Y' rY q q' f₁ g₁ = eq (box (unMor≃-lhs r ,, SubstTyFullEq (ConvTy (getdTy X') (reflectOb (q' ∙ ! (eq rY) ∙ ! f₁))) (morDer f) (ConvTyEq (getTy= rX) (reflectOb (q ∙ ! f₁))) (unMor≃-mor r)) (unOb≃ rX) (ConvMorEq (WeakMor+Eq (getdTy X) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb (f₁ ∙ ! q))) (ConvMorEq (unMor≃-mor r) (CtxRefl (der (lhs f))) (reflectOb (f₁ ∙ ! q)))) (CtxRefl (der (lhs f) , SubstTy (getdTy X) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb (f₁ ∙ ! q))))) (CtxTy=Ctx' X)))


qqS : (f : MorS m n) (X : ObS (suc n)) (Y : ObS n) (q : ftS X ≡ Y) (f₁ : ∂₁S f ≡ Y) → MorS (suc m) (suc n)
qqS {m = m} {n = n} =
  //-elim-PiS (λ f → //-elim-PiS (λ X → //-elim-PiP2 (λ Y q f₁ → proj (qqS-// f X Y q f₁))
                                                     (λ rY q q' → PathOver-Prop→Cst (λ f₁ f₁' → qqS-eq f f (ref f) X X (ref X) _ _ rY q q' f₁ f₁')))
                                 (λ rX → //-elimP (λ Y → PathOver-Prop→Cst (λ q q' → funextP (λ f₁ → qqS-eq f f (ref f) _ _ rX Y Y (ref Y) q q' f₁ f₁ )))))
             (λ rf → //-elimP (λ X → PathOver-CstPi (//-elimP (λ Y → PathOver-Prop→ λ q q' → PathOver-Prop→Cst (λ f₁ f₁' → qqS-eq _ _ rf X X (ref X) Y Y (ref Y) q q' f₁ f₁')))))


qq₀S-// : (f : DMor m n) (X : DCtx (suc n)) (Y : DCtx n) (q : ftS (proj X) ≡ proj Y) (f₁ : ∂₁S (proj f) ≡ proj Y) → ∂₀S (qqS (proj f) (proj X) (proj Y) q f₁) ≡ starS (proj f) (proj X) (proj Y) q f₁
qq₀S-// f X Y q f₁ = eq (box (CtxRefl (der (lhs f) , SubstTy (getdTy X) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb (f₁ ∙ ! q))))))

qq₀S : (f : MorS m n) (X : ObS (suc n)) (Y : ObS n) (q : ftS X ≡ Y) (f₁ : ∂₁S f ≡ Y) → ∂₀S (qqS f X Y q f₁) ≡ starS f X Y q f₁
qq₀S = //-elimP (λ f → //-elimP λ X → //-elimP (λ Y q f₁ → qq₀S-// f X Y q f₁))

qq₁S-// : (f : DMor m n) (X : DCtx (suc n)) (Y : DCtx n) (q : ftS (proj X) ≡ proj Y) (f₁ : ∂₁S (proj f) ≡ proj Y) → ∂₁S (qqS (proj f) (proj X) (proj Y) q f₁) ≡ proj X
qq₁S-// f X Y q f₁ = eq (box (CtxRefl (der X)))

qq₁S : (f : MorS m n) (X : ObS (suc n)) (Y : ObS n) (q : ftS X ≡ Y) (f₁ : ∂₁S f ≡ Y) → ∂₁S (qqS f X Y q f₁) ≡ X
qq₁S = //-elimP (λ f → //-elimP λ X → //-elimP (λ Y q f₁ → qq₁S-// f X Y q f₁))

ssS-// : (f : DMor m (suc n)) → DMor m (suc m)
ssS-// f = dmor (lhs f) ((ctx (lhs f) , getTy (rhs f) [ getMor f ]Ty) , (der (lhs f) , SubstTy (getdTy (rhs f)) (getdMor f))) (idMor _ , getTm f) (idMor+ (der (lhs f)) (getdTm f))

ssS-eq : (f f' : DMor m (suc n)) (rf : f ≃ f') → proj {R = MorEquiv} (ssS-// f) ≡ proj (ssS-// f')
ssS-eq f f' rf = eq (box (unMor≃-lhs rf) (unMor≃-lhs rf ,, SubstTyMorEq2 (der (lhs f)) (getdCtx (rhs f)) (getTy= {Γ = rhs f} {Γ' = rhs f'} (box (unMor≃-rhs rf))) (getLHS= {Δ = rhs f} (unMor≃-mor rf))) (idMor+= (der (lhs f)) (getRHS= (unMor≃-mor rf))))

ssS : (f : MorS m (suc n)) → MorS m (suc m)
ssS {n = n} = //-rec (λ f →  proj (ssS-// f)) (λ rf → ssS-eq _ _ rf)

ss₀S : (f : MorS m (suc n)) → ∂₀S (ssS f) ≡ ∂₀S f
ss₀S = //-elimP (λ f → refl)

ss₁S-// : (f : DMor m (suc n)) (X : DCtx (suc n)) (f₁ : ∂₁S (proj f) ≡ proj X)→ ∂₁S (ssS (proj f)) ≡ starS (compS (ppS (proj X)) (proj f) (proj X) (pp₀S (proj X)) f₁) (proj X) (ftS (proj X)) refl (comp₁S (ppS (proj X)) (proj f) (proj X) (pp₀S (proj X)) f₁ ∙ pp₁S (proj X))
ss₁S-// f X f₁ = eq (box (CtxRefl (der (lhs f)) ,, SubstTyMorEq2 (der (lhs f)) (getdCtx (rhs f)) (getTy= {Γ = rhs f} {Γ' = X}(box (reflectOb f₁))) (getLHS= {Δ = rhs f} (congMorEq refl refl refl (! (idMor[]Mor _)) (MorRefl (morDer f)))))) 

ss₁S : (f : MorS m (suc n)) (X : ObS (suc n)) (f₁ : ∂₁S f ≡ X) → ∂₁S (ssS f) ≡ starS (compS (ppS X) f X (pp₀S X) f₁) X (ftS X) refl (comp₁S (ppS X) f X (pp₀S X) f₁ ∙ pp₁S X)
ss₁S = //-elimP (λ f → //-elimP (λ X → ss₁S-// f X))
 
ft-starS-// : (f : DMor m n) (X : DCtx (suc n)) (Y : DCtx n) (q : ftS (proj X) ≡ proj Y) (f₁ : ∂₁S (proj f) ≡ proj Y) → ftS (starS (proj f) (proj X) (proj Y) q f₁) ≡ ∂₀S (proj f)
ft-starS-// f X Y q f₁ = eq (box (CtxRefl (der (lhs f)))) 

ft-starS : (f : MorS m n) (X : ObS (suc n))(Y : ObS n) (q : ftS X ≡ Y) (f₁ : ∂₁S f ≡ Y) → ftS (starS f X Y q f₁) ≡ ∂₀S f
ft-starS = //-elimP (λ f → //-elimP (λ X → //-elimP (λ Y → ft-starS-// f X Y)))

pp-qqS-// : (f : DMor m n) (X : DCtx (suc n)) (Y : DCtx n) (p : ftS (proj X) ≡ proj Y) (f₁ : ∂₁S (proj f) ≡ proj Y) → compS (ppS (proj X)) (qqS (proj f) (proj X) (proj Y) p f₁) (proj X) (pp₀S (proj X)) (qq₁S (proj f) (proj X) (proj Y) p f₁) ≡ compS (proj f) (ppS (starS (proj f) (proj X) (proj Y) p f₁)) (∂₀S (proj f)) refl (pp₁S (starS (proj f) (proj X) (proj Y) p f₁) ∙ ft-starS (proj f) (proj X) (proj Y) p f₁)
pp-qqS-// f X Y p f₁ = eq (box (CtxRefl (der (lhs f) , SubstTy (ConvTy (getdTy X) (reflectOb (p ∙ ! f₁))) (morDer f))) (reflectOb (p ∙ ! f₁)) (congMorEq refl refl (! ([weakenMor]Mor _ _ ∙ ap weakenMor (idMor[]Mor _))) weakenMor-to-[]Mor (MorRefl (WeakMor (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb (f₁ ∙ ! p)))))))

pp-qqS : (f : MorS m n) (X : ObS (suc n)) (Y : ObS n) (p : ftS X ≡ Y) (f₁ : ∂₁S f ≡ Y) → compS (ppS X) (qqS f X Y p f₁) X (pp₀S X) (qq₁S f X Y p f₁) ≡ compS f (ppS (starS f X Y p f₁)) (∂₀S f) refl (pp₁S (starS f X Y p f₁) ∙ ft-starS f X Y p f₁)
pp-qqS = //-elimP (λ f → //-elimP (λ X → //-elimP (λ Y → pp-qqS-// f X Y)))

star-idS : {n : ℕ} (X : ObS (suc n)) (Y : ObS n) (p : ftS X ≡ Y) → starS (idS n Y) X Y p (id₁S n Y) ≡ X
star-idS = //-elimP (λ X → //-elimP (λ Y p → eq (box (CtxTran (reflectOb (! p) ,, congTyEq (! ([idMor]Ty _)) refl (TyRefl (ConvTy (getdTy X) (reflectOb p)))) (CtxTy=Ctx' X))))) 

qq-idS : {n : ℕ} (X : ObS (suc n)) (Y : ObS n) (p : ftS X ≡ Y) → qqS (idS n Y) X Y p (id₁S n Y) ≡ idS (suc n) X
qq-idS  = //-elimP (λ X → //-elimP (λ Y p → eq (box (CtxTran (reflectOb (! p) ,, congTyEq (! ([idMor]Ty _)) refl (TyRefl (ConvTy (getdTy X) (reflectOb p)))) (CtxTy=Ctx' X)) (CtxRefl (der X)) (MorRefl (ConvMor (WeakMor+ (getdTy X) (idMorDerivable (getdCtx X))) (reflectOb p ,, TyRefl (SubstTy (getdTy X) (idMorDerivable (getdCtx X)))) (CtxTy=Ctx' X))))))

star-compS-// : (g : DMor m k) (f : DMor n m) (Y : DCtx m) (f₁ : ∂₁S (proj f) ≡ proj Y) (g₀ : ∂₀S (proj g) ≡ proj Y) (X : DCtx (suc k)) (Z : DCtx k) (p : ftS (proj X) ≡ proj Z) (g₁ : ∂₁S (proj g) ≡ proj Z) → starS (compS (proj g) (proj f) (proj Y) g₀ f₁) (proj X) (proj Z) p (comp₁S (proj g) (proj f) (proj Y) g₀ f₁ ∙ g₁) ≡ starS (proj f) (starS (proj g) (proj X) (proj Z) p g₁) (proj Y) (ft-starS (proj g) (proj X) (proj Z) p g₁ ∙ g₀) f₁
star-compS-// g f Y f₁ g₀ X Z p g₁ = eq (box (CtxRefl (der (lhs f)) ,, congTyEq  ([]Ty-assoc _ _ _) refl (TyRefl (SubstTy (SubstTy (ConvTy (getdTy X) (reflectOb (p ∙ ! g₁))) (morDer g)) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb (f₁ ∙ ! g₀)))))))

star-compS : (g : MorS m k) (f : MorS n m) (Y : ObS m) (f₁ : ∂₁S f ≡ Y) (g₀ : ∂₀S g ≡ Y) (X : ObS (suc k)) (Z : ObS k) (p : ftS X ≡ Z) (g₁ : ∂₁S g ≡ Z) → starS (compS g f Y g₀ f₁) X Z p (comp₁S g f Y g₀ f₁ ∙ g₁) ≡ starS f (starS g X Z p g₁) Y (ft-starS g X Z p g₁ ∙ g₀) f₁
star-compS = //-elimP (λ g → //-elimP (λ f → //-elimP (λ Y f₁ g₀ → //-elimP (λ X → //-elimP (λ Z → star-compS-// g f Y f₁ g₀ X Z)))))


qq-compS-// : (g : DMor m k) (f : DMor n m) (Y : DCtx m) (f₁ : ∂₁S (proj f) ≡ proj Y) (g₀ : ∂₀S (proj g) ≡ proj Y) (X : DCtx (suc k)) (Z : DCtx k) (p : ftS (proj X) ≡ proj Z) (g₁ : ∂₁S (proj g) ≡ proj Z)  → qqS (compS (proj g) (proj f) (proj Y) g₀ f₁) (proj X) (proj Z) p (comp₁S (proj g) (proj f) (proj Y) g₀ f₁ ∙ g₁) ≡ compS (qqS (proj g) (proj X) (proj Z) p g₁) (qqS (proj f) (starS (proj g) (proj X) (proj Z) p g₁) (proj Y) (ft-starS (proj g) (proj X) (proj Z) p g₁ ∙ g₀) f₁) (starS (proj g) (proj X) (proj Z) p g₁) (qq₀S (proj g) (proj X) (proj Z) p g₁) (qq₁S (proj f) (starS (proj g) (proj X) (proj Z) p g₁) (proj Y) (ft-starS (proj g) (proj X) (proj Z) p g₁ ∙ g₀) f₁)
qq-compS-// g f Y f₁ g₀ X Z p g₁ = eq (box (CtxRefl (der (lhs f)) ,, congTyEq ([]Ty-assoc _ _ _) refl (TyRefl (SubstTy (SubstTy (ConvTy (getdTy X) (reflectOb (p ∙ ! g₁))) (morDer g)) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb (f₁ ∙ ! g₀))))))
                                           (CtxRefl (der X))
                                           (congMorEq refl refl refl (ap (λ z → z , var last) (! ([weakenMor]Mor _ _))) (MorRefl (ConvMor (WeakMor (SubstMor (ConvMor (morDer g) (reflectOb (g₀ ∙ ! f₁)) (reflectOb (g₁ ∙ ! p))) (morDer f)) , congTmTy (weaken[]Ty _ _ _) (VarLast (SubstTy (ConvTy (getdTy X) (reflectOb (p ∙ ! g₁))) (SubstMor (morDer g) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb (f₁ ∙ ! g₀))))))) (CtxRefl {Γ = (_ , _)} (der (lhs f) , SubstTy (getdTy X) (SubstMor (ConvMor (morDer g) (reflectOb (g₀ ∙ ! f₁)) (reflectOb (g₁ ∙ ! p))) (morDer f))) ) (CtxTy=Ctx' X)))))

qq-compS : (g : MorS m k) (f : MorS n m) (Y : ObS m) (f₁ : ∂₁S f ≡ Y) (g₀ : ∂₀S g ≡ Y) (X : ObS (suc k)) (Z : ObS k) (p : ftS X ≡ Z) (g₁ : ∂₁S g ≡ Z)  → qqS (compS g f Y g₀ f₁) X Z p (comp₁S g f Y g₀ f₁ ∙ g₁) ≡ compS (qqS g X Z p g₁) (qqS f (starS g X Z p g₁) Y (ft-starS g X Z p g₁ ∙ g₀) f₁) (starS g X Z p g₁) (qq₀S g X Z p g₁) (qq₁S f (starS g X Z p g₁) Y (ft-starS g X Z p g₁ ∙ g₀) f₁)
qq-compS = //-elimP (λ g → //-elimP (λ f → //-elimP (λ Y f₁ g₀ → //-elimP (λ X → //-elimP (λ Z → qq-compS-// g f Y f₁ g₀ X Z)))))


ss-ppS-// : {m n : ℕ} (f : DMor m (suc n)) (X : DCtx m) (f₀ : ∂₀S (proj f) ≡ proj X) (Y : DCtx (suc n)) (f₁ : ∂₁S (proj f) ≡ proj Y) → compS (ppS (starS (compS (ppS (proj Y)) (proj f) (proj Y) (pp₀S (proj Y)) f₁) (proj Y) (ftS (proj Y)) refl (comp₁S (ppS (proj Y)) (proj f) (proj Y) (pp₀S (proj Y)) f₁ ∙ pp₁S (proj Y)))) (ssS (proj f)) (starS (compS (ppS (proj Y)) (proj f) (proj Y) (pp₀S (proj Y)) f₁) (proj Y) (ftS (proj Y)) refl (comp₁S (ppS (proj Y)) (proj f) (proj Y) (pp₀S (proj Y)) f₁ ∙ pp₁S (proj Y))) (pp₀S (starS (compS (ppS (proj Y)) (proj f) (proj Y) (pp₀S (proj Y)) f₁) (proj Y) (ftS (proj Y)) refl (comp₁S (ppS (proj Y)) (proj f) (proj Y) (pp₀S (proj Y)) f₁ ∙ pp₁S (proj Y)))) (ss₁S (proj f) (proj Y) f₁) ≡ idS m (proj X)
ss-ppS-// f X f₀ Y f₁ = eq (box (reflectOb f₀) (reflectOb f₀) (congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ idMor[]Mor _)) refl (MorRefl (idMorDerivable (der (lhs f))))))

ss-ppS : {m n : ℕ} (f : MorS m (suc n)) (X : ObS m) (f₀ : ∂₀S f ≡ X) (Y : ObS (suc n)) (f₁ : ∂₁S f ≡ Y) → compS (ppS (starS (compS (ppS Y) f Y (pp₀S Y) f₁) Y (ftS Y) refl (comp₁S (ppS Y) f Y (pp₀S Y) f₁ ∙ pp₁S Y))) (ssS f) (starS (compS (ppS Y) f Y (pp₀S Y) f₁) Y (ftS Y) refl (comp₁S (ppS Y) f Y (pp₀S Y) f₁ ∙ pp₁S Y)) (pp₀S (starS (compS (ppS Y) f Y (pp₀S Y) f₁) Y (ftS Y) refl (comp₁S (ppS Y) f Y (pp₀S Y) f₁ ∙ pp₁S Y))) (ss₁S f Y f₁) ≡ idS m X
ss-ppS = //-elimP (λ f → //-elimP (λ X f₀ → //-elimP (λ Y → ss-ppS-// f X f₀ Y)))

ss-qqS-// : {m n : ℕ} (f : DMor m (suc n)) (X : DCtx (suc n)) (f₁ : ∂₁S (proj f) ≡ proj X) → (proj f) ≡ compS (qqS (compS (ppS (proj X)) (proj f) (proj X) (pp₀S (proj X)) f₁) (proj X) (ftS (proj X)) refl (comp₁S (ppS (proj X)) (proj f) (proj X) (pp₀S (proj X)) f₁ ∙ pp₁S (proj X))) (ssS (proj f)) (starS (compS (ppS (proj X)) (proj f) (proj X) (pp₀S (proj X)) f₁) (proj X) (ftS (proj X)) refl (comp₁S (ppS (proj X)) (proj f) (proj X) (pp₀S (proj X)) f₁ ∙ pp₁S (proj X))) (qq₀S (compS (ppS (proj X)) (proj f) (proj X) (pp₀S (proj X)) f₁) (proj X) (ftS (proj X)) refl (comp₁S (ppS (proj X)) (proj f) (proj X) (pp₀S (proj X)) f₁ ∙ pp₁S (proj X))) (ss₁S (proj f) (proj X) f₁)
ss-qqS-// f X f₁ = eq (box (CtxRefl (der (lhs f))) (reflectOb f₁) (congMorEq {θ = (getLHS (mor f) , getRHS (mor f))}refl refl refl (! (ap (λ z → (z , getRHS (mor f))) (weakenMorInsert _ _ _ ∙ ([idMor]Mor _) ∙ weakenMorInsert' _ _ ∙ (idMor[]Mor _)))) (Mor=LHSRHS f)))

ss-qqS : {m n : ℕ} (f : MorS m (suc n)) (X : ObS (suc n)) (f₁ : ∂₁S f ≡ X) → f ≡ compS (qqS (compS (ppS X) f X (pp₀S X) f₁) X (ftS X) refl (comp₁S (ppS X) f X (pp₀S X) f₁ ∙ pp₁S X)) (ssS f) (starS (compS (ppS X) f X (pp₀S X) f₁) X (ftS X) refl (comp₁S (ppS X) f X (pp₀S X) f₁ ∙ pp₁S X)) (qq₀S (compS (ppS X) f X (pp₀S X) f₁) X (ftS X) refl (comp₁S (ppS X) f X (pp₀S X) f₁ ∙ pp₁S X)) (ss₁S f X f₁)
ss-qqS = //-elimP (λ f → //-elimP (λ X → ss-qqS-// f X))

ss-compS-// : {m n k : ℕ} (U : DCtx (suc k)) (X : DCtx k) (p : ftS (proj U) ≡ proj X) (g : DMor n k) (g₁ : ∂₁S (proj g) ≡ proj X) (f : DMor m (suc n)) (f₁ : ∂₁S (proj f) ≡ starS (proj g) (proj U) (proj X) p g₁) → ssS (proj f) ≡ ssS (compS (qqS (proj g) (proj U) (proj X) p g₁) (proj f) (starS (proj g) (proj U) (proj X) p g₁) (qq₀S (proj g) (proj U) (proj X) p g₁) f₁)
ss-compS-// U X p g g₁ f f₁ = eq (box (CtxRefl (der (lhs f))) (CtxRefl (der (lhs f)) ,, congTyEq refl (! (ap (λ z → (getTy U) [ z ]Ty) (weakenMorInsert' _ _) ∙ ! ([]Ty-assoc _ _ _))) (SubstTyEq (getTy= {Γ = rhs f} {Γ' = (ctx (lhs g) , getTy U [ mor g ]Ty) , (der (lhs g) , SubstTy (ConvTy (getdTy U) (reflectOb (p ∙ ! g₁))) (morDer g))} (box (reflectOb f₁))) (getdMor f))) (MorRefl (idMor+ (der (lhs f)) (getdTm f))))

ss-compS : {m n k : ℕ} (U : ObS (suc k)) (X : ObS k) (p : ftS U ≡ X) (g : MorS n k) (g₁ : ∂₁S g ≡ X) (f : MorS m (suc n)) (f₁ : ∂₁S f ≡ starS g U X p g₁) → ssS f ≡ ssS (compS (qqS g U X p g₁) f (starS g U X p g₁) (qq₀S g U X p g₁)  f₁)
ss-compS = //-elimP (λ U → //-elimP (λ X p → //-elimP (λ g g₁ → //-elimP (λ f → ss-compS-// U X p g g₁ f))))

{- The syntactic contextual category -}

synCCat : CCat
Ob synCCat = ObS
CCat.Mor synCCat = MorS
∂₀ synCCat = ∂₀S
∂₁ synCCat = ∂₁S
CCat.id synCCat = idS _
id₀ synCCat {n = n} {X = X} = id₀S n X
id₁ synCCat {n = n} {X = X} = id₁S n X
comp synCCat g f {X = X} g₀ f₁ = compS g f X g₀ f₁
comp₀ synCCat {g = g} {f = f} {g₀ = g₀} {f₁ = f₁} = comp₀S g f _ g₀ f₁
comp₁ synCCat {g = g} {f = f} {g₀ = g₀} {f₁ = f₁} = comp₁S g f _ g₀ f₁
ft synCCat = ftS
pp synCCat = ppS
pp₀ synCCat {X = X} = pp₀S X
pp₁ synCCat {X = X} = pp₁S X
star synCCat f X q f₁ = starS f X _ q f₁
qq synCCat f X q f₁ = qqS f X _ q f₁
qq₀ synCCat {f = f} {X = X} {q = q} {f₁ = f₁} = qq₀S f X _ q f₁
qq₁ synCCat {f = f} {X = X} {q = q} {f₁ = f₁} = qq₁S f X _ q f₁
ss synCCat f = ssS f
ss₀ synCCat {f = f} = ss₀S f
ss₁ synCCat {f = f} f₁ = ss₁S f _ f₁
pt synCCat = ptS
pt-unique synCCat = pt-uniqueS
ptmor synCCat = ptmorS
ptmor₀ synCCat {X = X} = ptmor₀S X
ptmor₁ synCCat {X = X} = ptmor₁S X
ptmor-unique synCCat = ptmor-uniqueS
id-right synCCat {f = f} f₁ = id-rightS f _ f₁
id-left synCCat {f = f} f₁ = id-leftS f _ f₁
assoc synCCat {h = h} {g = g} {f = f} {f₁ = f₁} {g₀ = g₀} {g₁ = g₁} {h₀ = h₀} = assocS h g f _ f₁ g₀ _ g₁ h₀ 
ft-star synCCat {f = f} {X = X} {p = p} {f₁ = f₁} = ft-starS f X _ p f₁
pp-qq synCCat {f = f} {X = X} {p = p} {f₁ = f₁} = pp-qqS f X _ p f₁
star-id synCCat {X = X} {p = p} = star-idS X _ p
qq-id synCCat {X = X} {p = p} = qq-idS X _ p
star-comp synCCat {g = g} {f = f} {f₁ = f₁} {g₀ = g₀} {p = p} {g₁ = g₁} = star-compS g f _ f₁ g₀ _ _ p g₁
qq-comp synCCat {g = g} {f = f} {f₁ = f₁} {g₀ = g₀} {p = p} {g₁ = g₁} = qq-compS g f _ f₁ g₀ _ _ p g₁
ss-pp synCCat {f = f} f₀ {f₁ = f₁} = ss-ppS f _ f₀ _ f₁
ss-qq synCCat {f = f} {f₁ = f₁} = ss-qqS f _ f₁
ss-comp synCCat {U = U} {p = p} {g = g} {g₁ = g₁} {f = f} {f₁ = f₁} = ss-compS U _ p g g₁ f f₁

{- The syntactic structured contextual category. We start with some helper functions. -}

module S = CCat+ synCCat

S-is-section₀ : {u : DMor n (suc n)} {X : S.Ob (suc n)} (uₛ : S.is-section (proj u)) (u₁ : S.∂₁ (proj u) ≡ X) → proj (ctx (lhs u) ,' der (lhs u)) ≡ S.ft X
S-is-section₀ uₛ u₁ = ap proj eta  ∙ S.is-section₀ uₛ u₁  where
  eta : {Y : DCtx n} → (ctx Y , der Y) ≡ Y
  eta {Y = ctxY , derY} = refl


getMor=idMor' : {a : DMor n (suc n)} (aₛ : S.is-section (proj a)) → ctx (lhs a) ⊢ getMor a == idMor n ∷> getCtx (ctx (rhs a))
getMor=idMor' {a = dmor' _ (Δ , dΔ) (δ , u) _} aₛ = congMorEq refl refl (weakenMorInsert _ _ u  ∙ idMor[]Mor _) refl ((unMor≃-mor (reflect (S.is-section= refl aₛ (DCtx= {w₂ = dΔ} refl)))))

morTm=idMorTm' : {a : DMor n (suc n)} (aₛ : S.is-section (proj a)) → ctx (lhs a) ⊢ mor a == idMor n , getRHS (mor a) ∷> (ctx (rhs a))
morTm=idMorTm' {a = dmor' _ ((_ , _) , (_ , _)) (δ , _) (_ , du)} aₛ = (getMor=idMor' aₛ) , (TmRefl du)


dTy : {Γ : DCtx n} (A : DCtx (suc n)) (A= : proj {R = ObEquiv} (getCtx (ctx A) , getdCtx A) ≡ proj Γ) → Derivable (ctx Γ ⊢ getTy A)
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


getMor=idMor : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) → ctx Γ ⊢ getMor a == idMor n ∷> ctx Γ
getMor=idMor A= a aₛ a₁ = ConvMorEq (getMor=idMor' aₛ) (reflectOb (S.is-section₀ aₛ a₁ ∙  A=)) (CtxTran (getCtx= (reflectOb a₁)) (reflectOb A=))

morTm=idMorTm : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A)  → ctx Γ ⊢ mor a == idMor n , getRHS (mor a) ∷> (ctx Γ , getTy A)
morTm=idMorTm {A = A} A= a aₛ a₁ = ConvMorEq (morTm=idMorTm' aₛ) (reflectOb (S.is-section₀ aₛ a₁ ∙  A=)) (CtxTran (reflectOb a₁) (CtxSymm (CtxTy=Ctx A A=)))

dTm : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) → Derivable (ctx Γ ⊢ getTm a :> getTy A)
dTm {A = A} A= a aₛ a₁ =
  let lhsa=Γ = reflectOb (S.is-section₀ aₛ a₁ ∙ A=)
      lhsa=ftA = reflectOb (S.is-section₀ aₛ a₁)     
  in
  ConvTm2 (getdTm a) lhsa=Γ (TyTran (ConvTy (getdTy (rhs a)) (CtxTran (getCtx= (reflectOb a₁)) (CtxSymm (lhsa=ftA)))) (congTyEq refl ([idMor]Ty _) (SubstTyMorEq (getdTy (rhs a)) (getdMor a) (getMor=idMor' aₛ))) (ConvTyEq (lemmathing (reflect a₁)) (CtxSymm lhsa=ftA)))
                 

-- dTm' : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ⊢ ctx (∂₁S-// a) == ctx A) → Derivable (ctx Γ ⊢ getTm a :> getTy A)
-- dTm' {A = A} A= a aₛ a₁ =
--   let lhsa=Γ = reflectOb (S.is-section₀ aₛ (eq (box {Γ = ∂₁S-// a} {Γ' = A} a₁)) ∙ A=)
--       lhsa=ftA = reflectOb (S.is-section₀ aₛ (eq (box {Γ = ∂₁S-// a} {Γ' = A} a₁)))     
--   in
--   ConvTm2 (getdTm a) lhsa=Γ (TyTran (ConvTy (getdTy (rhs a)) (CtxTran (getCtx= (box {Γ = ∂₁S-// a} {Γ' = A} a₁)) (CtxSymm (lhsa=ftA)))) (congTyEq refl ([idMor]Ty _) (SubstTyMorEq (getdTy (rhs a)) (getdMor a) (getMor=idMor' aₛ))) (ConvTyEq (lemmathing (box {Γ = ∂₁S-// a} {Γ' = A} a₁)) (CtxSymm lhsa=ftA)))
                        
dTmSubst : {Γ : DCtx n} {A : DCtx (suc n)} (A= : S.ft (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : S.ft (proj B) ≡ proj A) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : S.∂₁ (proj a) ≡ proj A) (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : S.∂₁ (proj b) ≡ S.star (proj a) (proj B) B= a₁) → Derivable (ctx Γ ⊢ getTm b :> substTy (getTy B) (getTm a)) 
dTmSubst {Γ = Γ} {A} A= B B= a aₛ a₁ b bₛ b₁ =
  let lhsa=Γ = reflectOb (S.is-section₀ aₛ a₁ ∙ A=)
      lhsa=ftA = reflectOb (S.is-section₀ aₛ a₁)
      rhsa=A = reflectOb a₁
  in
  Conv (SubstTy (dTy B B=) (ConvMor (morDer a) lhsa=Γ rhsa=A)) (dTm (S-is-section₀ aₛ a₁ ∙ A=) b bₛ b₁) (SubstTyMorEq (dTy B B=) (ConvMor (morDer a) lhsa=Γ rhsa=A) (ConvMorEq (morTm=idMorTm' aₛ) lhsa=Γ rhsa=A))

dTm+ : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) {B : DCtx (suc (suc n))} (B= : ftS (proj B) ≡ proj A) (u : DMor (suc n) (suc (suc n))) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) → Derivable ((ctx Γ , getTy A) ⊢ getTm u :> getTy B)
dTm+ A= {B = B} B= u uₛ u₁ = dTm (combine A= B B=) u uₛ u₁

dTm= : {Γ : DCtx n} {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : ftS (proj A) ≡ proj Γ) {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ proj A) (a'₁ : ∂₁S (proj a') ≡ proj A') → Derivable (ctx Γ ⊢ getTm a == getTm a' :> getTy A)
dTm= rA A= {a} {a'} ra aₛ a'ₛ a₁ a'₁ = 
  let lhsa=Γ = reflectOb (S.is-section₀ aₛ a₁ ∙ A=)
      lhsa=ftA = reflectOb (S.is-section₀ aₛ a₁)
      rhsa=A = reflectOb a₁
  in
  ConvTmEq2 (getRHS= (unMor≃-mor ra)) lhsa=Γ (TyTran (ConvTy (getdTy (rhs a)) (CtxTran (getCtx= (reflectOb a₁)) (CtxSymm (lhsa=ftA)))) (congTyEq refl ([idMor]Ty _) (SubstTyMorEq (getdTy (rhs a)) (getdMor a) (getMor=idMor' aₛ))) (ConvTyEq (lemmathing (reflect a₁)) (CtxSymm lhsa=ftA)))


-- dTm=' : {Γ : DCtx n} {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : ftS (proj A) ≡ proj Γ) {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ⊢ ctx (∂₁S-// a) == ctx A) (a'₁ : ⊢ ctx (∂₁S-// a') == ctx A') → Derivable (ctx Γ ⊢ getTm a == getTm a' :> getTy A)
-- dTm=' {A = A} rA A= {a} {a'} ra aₛ a'ₛ a₁ a'₁ = 
--   let lhsa=Γ = reflectOb (S.is-section₀ aₛ (eq (box {Γ  = ∂₁S-// a} {Γ' = A} a₁)) ∙ A=)
--       lhsa=ftA = reflectOb (S.is-section₀ aₛ (eq (box {Γ  = ∂₁S-// a} {Γ' = A} a₁)))
--       rhsa=A = a₁
--   in
--   ConvTmEq2 (getRHS= (unMor≃-mor ra)) lhsa=Γ (TyTran (ConvTy (getdTy (rhs a)) (CtxTran (getCtx= (box {Γ = ∂₁S-// a} {Γ' = A} a₁)) (CtxSymm (lhsa=ftA)))) (congTyEq refl ([idMor]Ty _) (SubstTyMorEq (getdTy (rhs a)) (getdMor a) (getMor=idMor' aₛ))) (ConvTyEq (lemmathing (box {Γ = ∂₁S-// a} {Γ' = A} a₁)) (CtxSymm lhsa=ftA)))


dTmSubst= : {Γ : DCtx n} {A A' : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : ftS (proj B) ≡ proj A) (B'= : ftS (proj B') ≡ proj A') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ proj A) (a'₁ : ∂₁S (proj a') ≡ proj A') {b b' : DMor n (suc n)} (rb : b ≃ b') (bₛ : S.is-section (proj b)) (b'ₛ : S.is-section (proj b')) (b₁ : ∂₁S (proj b) ≡ S.star (proj a) (proj B) B= a₁) (b'₁ : ∂₁S (proj b') ≡ S.star (proj a') (proj B') B'= a'₁) → Derivable (ctx Γ ⊢ getTm b == getTm b' :> substTy (getTy B) (getTm a))
dTmSubst= {A = A} A= {B} {B'} rB B= B'= {a} {a'} ra aₛ a'ₛ a₁ a'₁ {b} {b'} rb bₛ b'ₛ b₁ b'₁  = 
  let lhsa=Γ = reflectOb (S.is-section₀ aₛ a₁ ∙ A=)
      lhsa=ftA = reflectOb (S.is-section₀ aₛ a₁)
      rhsa=A = reflectOb a₁
  in
    ConvEq (SubstTy (dTy B B=) (ConvMor (morDer a) lhsa=Γ rhsa=A)) (dTm= (box (unMor≃-lhs ra ,, SubstTyMorEq2 (der (lhs a)) (der (rhs a)) (ConvTyEq (dTy+= A= rB B=) (CtxTran (CtxTy=Ctx A A=) (CtxSymm rhsa=A))) (unMor≃-mor ra))) (S-is-section₀ aₛ a₁ ∙ A=) rb bₛ b'ₛ b₁ b'₁) (SubstTyMorEq (dTy B B=) (ConvMor (morDer a) lhsa=Γ rhsa=A) (ConvMorEq (morTm=idMorTm' aₛ) lhsa=Γ rhsa=A))


dTm+= : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : ftS (proj B) ≡ proj A) {u u' : DMor (suc n) (suc (suc n))} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : ∂₁S (proj u) ≡ proj B) (u'₁ : ∂₁S (proj u') ≡ proj B') → Derivable ((ctx Γ , getTy A) ⊢ getTm u == getTm u' :> getTy B)
dTm+= A= {B = B} rB B= ru uₛ u'ₛ u₁ u'₁ = dTm= rB (combine A= B B=) ru uₛ u'ₛ u₁ u'₁


up-to-rhsTyEq : {Γ : DCtx n} {A B : TyExpr n}  {δ : Mor n (suc n)} {w₁ : _} {w₂ : _} {w₃ : _} {w₄ : _} (Tyeq : A ≡ B) → proj {R = MorEquiv} (dmor' Γ ((ctx Γ , A) , w₁) δ w₂) ≡ proj (dmor' Γ ((ctx Γ , B) , w₃) δ w₄)
up-to-rhsTyEq refl = refl

up-to-rhsTyEq2 : {Γ : DCtx n} {A B : TyExpr n} {δ : Mor n n} {u u' : TmExpr n} {w₁ : _} {w₂ : _} {w₃ : _} {w₄ : _} → ctx Γ ⊢ δ == idMor n ∷> ctx Γ → Derivable (ctx Γ ⊢ A == B) → Derivable (ctx Γ ⊢ u == u' :> A)
               → proj {R = MorEquiv} (dmor' Γ ((ctx Γ , A) , w₁) (δ , u) w₂) ≡ proj (dmor' Γ ((ctx Γ , B) , w₃) (δ , u') w₄)
up-to-rhsTyEq2 {Γ = Γ} {δ = δ} δ= p q = eq (box (CtxRefl (der Γ)) (CtxRefl (der Γ) ,, p) (MorRefl (MorEqMor1 (der Γ) (der Γ) δ=) , ConvEq (TyEqTy1 (der Γ) p) q (congTyEq ([idMor]Ty _) refl (SubstTyMorEq (TyEqTy1 (der Γ) p) (idMorDerivable (der Γ)) (MorSymm (der Γ) (der Γ) δ=)))))


{- Elimination principles for Ty and Tm -}

_×S_ : (A B : Set) → Set
A ×S B = ΣSS A (λ _ → B)

infixr 42 _×S_

//-elim-Ctx : ∀ {l} {C : (Γ : ObS n) → Set l}
           → (proj* : (Γ : DCtx n) → C (proj Γ))
           → (eq* : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → PathOver C (eqR rΓ) (proj* Γ) (proj* Γ'))
           → (Γ : ObS n) → C Γ
//-elim-Ctx proj* eq* = //-elim proj* eq*

//-elimP-Ctx : ∀ {l} {C : (Γ : ObS n) → Prop l}
            → (proj* : (Γ : DCtx n) → C (proj (ctx Γ , der Γ)))
            → (Γ : ObS n) → C Γ
//-elimP-Ctx proj* = //-elimP (λ {(Γ , dΓ) → proj* (Γ , dΓ)})

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
uncurrifyTm C (u , uₛu₁) = C u (fst uₛu₁) (snd uₛu₁)

uncurrifyTm+ : ∀ {l} {X : Set} {A : X → ObS (suc n)} (C : (x : X) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ A x) → Set l) → ΣS (X ×S MorS n (suc n)) (λ {(x , u) → (S.is-section u) × (S.∂₁ u ≡ A x)}) → Set l
uncurrifyTm+ C ((x , u) , uₛu₁) = C x u (fst uₛu₁) (snd uₛu₁)

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

proj= : {C D : Set} {Γ Γ' : C} {BΓ BΓ' : D} {R : EquivRel D} {rΓ : Γ ≡R Γ'} (rBΓ : (R EquivRel.≃ BΓ) BΓ') → PathOver (λ _ → D // R) rΓ (proj BΓ) (proj BΓ')
proj= rBΓ = PathOver-Cst (eq rBΓ)
 
-- This function does the pattern matching on g₀ needed for the naturalities
JforNat : {A : Set} {∂₀g : A} {T : (Δ : A) (g₀ : ∂₀g ≡ Δ) → Prop}
        → (T ∂₀g refl)
        → ((Δ : A) (g₀ : ∂₀g ≡ Δ) → T Δ g₀)
JforNat d _ refl = d

{-- Term formers --}

dmorTm : (Γ : DCtx n) (A : TyExpr n) (dA : Derivable (ctx Γ ⊢ A)) (u : TmExpr n) (du : Derivable (ctx Γ ⊢ u :> A)) → DMor n (suc n)
dmorTm Γ A dA u du = dmor Γ ((ctx Γ , A) , (der Γ , dA)) (idMor _ , u) (idMor+ (der Γ) du)

dmorTm=' : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ')
        → {A A' : TyExpr n} (dA : _) (dA' : _) (dA= : Derivable (ctx Γ ⊢ A == A'))
        → {u u' : TmExpr n} (du : _) (du' : _) (du= : Derivable (ctx Γ ⊢ u == u' :> A))
        → dmorTm Γ A dA u du ≃ dmorTm Γ' A' dA' u' du'
dmorTm=' {Γ = Γ} rΓ _ _ dA= _ _ du= = box (unOb≃ rΓ) (unOb≃ rΓ ,, dA=) (idMor+= (der Γ) du=)

dmorTm= : {δ δ' : DMor n (suc n)} (δₛ : S.is-section (proj δ)) (δ'ₛ : S.is-section (proj δ'))  (let Γ = lhs δ) (let Γ' = lhs δ') {Δ : DCtx n} {Δ' : DCtx n} {{p : ctx Δ ≡ ctx Γ}} {{q : ctx Δ' ≡ ctx Γ'}} (rΔ : Δ ≃ Δ')
           (let A = getTy (rhs δ)) (let A' = getTy (rhs δ')) (let dA = getdTy (rhs δ)) (let dA' = getdTy (rhs δ')) (dA= : Derivable (ctx Γ ⊢ A == A'))
           (let u = getTm δ) (let u' = getTm δ') (let du = getdTm δ) (let du' = getdTm δ') (du= : Derivable (ctx Γ ⊢ u == u' :> A))
           → δ ≃ δ'
dmorTm=  {δ = δ} {δ' = δ'} δₛ δ'ₛ {{p}} {{q}} rΔ dA= du= = box (congCtxEq p q (unOb≃ rΔ))
                                               rhsδ=rhsδ'
                                               (MorTran (der (lhs δ)) (der (rhs δ)) (morTm=idMorTm' δₛ)
                                                        (MorTran (der (lhs δ)) (der (rhs δ)) (ConvMorEq (idMor+= (der (lhs δ)) du=) (CtxRefl (der (lhs δ)))
                                                                 (CtxSymm (CtxTran (CtxSymm (CtxTy=Ctx' (rhs δ)))
                                                                                   (CtxSymm (unMor≃-lhs (reflect (S.is-section= refl δₛ refl))) ,, TyRefl (getdTy (rhs δ))))))
                                                                 (MorSymm (der (lhs δ)) (der (rhs δ))
                                                                          (ConvMorEq (morTm=idMorTm' δ'ₛ) (CtxSymm (congCtxEq p q (unOb≃ rΔ)))
                                                                                                         (CtxSymm rhsδ=rhsδ')))))
                                         where rhsδ=rhsδ' : ⊢ ctx (rhs δ) == ctx (rhs δ')
                                               rhsδ=rhsδ' = (CtxTran (CtxTran (CtxSymm (CtxTy=Ctx' (rhs δ)))
                                                                     (CtxSymm (unMor≃-lhs (reflect (S.is-section= refl δₛ refl))) ,, TyRefl (getdTy (rhs δ))))
                                                            (CtxTran (congCtxEq p q (unOb≃ rΔ) ,, dA=)
                                                                     (CtxTran (CtxSymm (CtxSymm (unMor≃-lhs (reflect (S.is-section= refl δ'ₛ refl))) ,, TyRefl (getdTy (rhs δ'))))
                                                                              (CtxTy=Ctx' (rhs δ')))))

dmorTmₛ' : {Γ : DCtx n} {A : TyExpr n} (dA : Derivable (ctx Γ ⊢ A)) {u : TmExpr n} (du : Derivable (ctx Γ ⊢ u :> A)) → S.is-section (proj {R = MorEquiv} (dmorTm Γ A dA u du))
dmorTmₛ' {Γ = Γ} dA du = S.is-section→ (eq (box (CtxRefl (der Γ)) (CtxRefl (der Γ)) (congMorEq refl refl (! (weakenMorInsert _ _ _  ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable (der Γ))))))

dmorTmₛ : {δ : DMor n (suc n)} (let Γ = lhs δ) (let Δ = getCtx (ctx (rhs δ))) (let morδ = getMor δ) {{p : ctx Γ ≡ Δ}} {{q :  morδ ≡ idMor _}} → S.is-section (proj δ)
dmorTmₛ {δ = δ@(dmor' (_ , _) ((_ , _) , (_ , _)) (_ , u) _)} {{p}} {{q}} = S.is-section→ (DMor= refl (! p) (ap (λ z → weakenMor (idMor _)  [ z ]Mor) (Mor+= q refl) ∙ weakenMorInsert _ _ u ∙ idMor[]Mor _))

weakenObjS= : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) → S.weakenObj {A = proj A} A= ≡ proj (((ctx Γ , getTy A) , weakenTy (getTy A)) , (der Γ , dTy A A=) , WeakTy (dTy A A=))
weakenObjS= {A = A} A= = eq (box (CtxSymm (CtxTy=Ctx A A=) ,, congTyEq weakenTy-to-[]Ty refl (TyRefl (ConvTy (WeakTy (dTy A A=)) (CtxTy=Ctx A A=)))))
