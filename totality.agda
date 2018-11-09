{-# OPTIONS --prop #-}

open import common
open import syntx
open import contextualcat
open import rules

module _ (C : StructuredCCat) where

open StructuredCCat C
open CCat ccat renaming (Mor to MorC)
open M ccat
open import partialinterpretation C

{- Predicate saying whether an object "respects" a context in the sense that the types in Γ correspond to their interpretation in X.
   We cannot use (X ≡ ⟦ Γ ⟧) instead because it fails the termination checker somehow. -}

respectsCtx : (X : Ob n) (Γ : Ctx n) → Prop
respectsCtx {zero} X ◇ = Unit
respectsCtx {suc n} X (Γ , A) = respectsCtx (ft X) Γ × Σ (isDefined (⟦ A ⟧Ty (ft X))) (λ Aᵈ → toCtx (totalify (⟦ A ⟧Ty (ft X)) Aᵈ) ≡ X)

respectsCtxExt : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) (A : TyExpr n) (Aᵈ : isDefined (⟦ A ⟧Ty X))
              → respectsCtx (toCtx (totalify (⟦ A ⟧Ty X) Aᵈ)) (Γ , A)
respectsCtxExt X r A Aᵈ rewrite (toCtxEq (totalify (⟦ A ⟧Ty X) Aᵈ)) = r , (Aᵈ , refl)

{- Totality of the partial interpretation functions -}

isTotal⟦⟧Ty  : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) → isDefined (⟦ A ⟧Ty X)
isTotal⟦⟧Tm  : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → isDefined (⟦ u ⟧Tm X)
isTotal⟦⟧Mor : {Γ : Ctx n} (X : Ob n) {Δ : Ctx m} (Y : Ob m) (r : respectsCtx X Γ) (r' : respectsCtx Y Δ) {δ : Mor n m} (dδ : Γ ⊢ δ ∷> Δ) → isDefined (⟦ δ ⟧Mor X Y)

-- ⟦⟧Mor : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} (dΓ : ⊢ Γ) (dΔ : ⊢ Δ) (dδ : Γ ⊢ δ ∷> Δ) → MorC n m
-- ⟦⟧Mor {δ = δ} dΓ dΔ dδ = totalify (⟦ δ ⟧Mor (⟦⟧Ctx dΓ) (⟦⟧Ctx dΔ)) (isTotal⟦⟧Mor dΓ dΔ dδ)

{- The total interpretation functions themselves, derived from the totality -}

⟦⟧Ty : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) → Ty X 0
⟦⟧Ty X r {A = A} dA = totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA)

⟦⟧Tm : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → Tm X 0
⟦⟧Tm X r {u = u} du = totalify (⟦ u ⟧Tm X) (isTotal⟦⟧Tm X r du)

{- The type of the interpretation of a term is the interpretation of its type -}

getTy⟦⟧ : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) (Aᵈ : isDefined (⟦ A ⟧Ty X)) → getTy (⟦⟧Tm X r du) ≡ totalify (⟦ A ⟧Ty X) Aᵈ

{- Interpretation of definitional equalities -}

⟦⟧TyEq : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A')) (Aᵈ : isDefined (⟦ A ⟧Ty X)) (A'ᵈ : isDefined (⟦ A' ⟧Ty X))
        → totalify (⟦ A ⟧Ty X) Aᵈ ≡ totalify (⟦ A' ⟧Ty X) A'ᵈ
⟦⟧TmEq : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A)) (uᵈ : isDefined (⟦ u ⟧Tm X)) (u'ᵈ : isDefined (⟦ u' ⟧Tm X))
        → totalify (⟦ u ⟧Tm X) uᵈ ≡ totalify (⟦ u' ⟧Tm X) u'ᵈ

{- Interpretation of total substitutions -}

⟦tsubst⟧Tyᵈ : (X : Ob n) (Y : Ob m) (A : TyExpr m) {δ : Mor n m}
            → isDefined (⟦ A ⟧Ty Y)
            → isDefined (⟦ δ ⟧Mor X Y)
            → isDefined (⟦ A [ δ ]Ty ⟧Ty X)

⟦tsubst⟧Ty= : (X : Ob n) (Y : Ob m) (A : TyExpr m) {δ : Mor n m}
            (Aᵈ : isDefined (⟦ A ⟧Ty Y))
            (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            → totalify (⟦ A [ δ ]Ty ⟧Ty X) (⟦tsubst⟧Tyᵈ X Y A Aᵈ δᵈ)
              ≡ star^-with-eqs (totalify (⟦ δ ⟧Mor X Y) δᵈ) {!!} {!!} (totalify (⟦ A ⟧Ty Y) Aᵈ)

{- Extension of substitutions -}

⟦substExt⟧Tyᵈ : (X : Ob n) (Y : Ob m) {δ : Mor n m} (T : Ty Y 0)
              (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
              → isDefined (⟦ weakenMor δ , var last ⟧Mor (star (totalify (⟦ δ ⟧Mor X Y) δᵈ) (toCtx T) ({!!} ∙ ! (toCtxEq T))) (toCtx T))

{- Interpretation of substitutions -}

⟦subst⟧Tyᵈ : (X : Ob n) (u : TmExpr n) (A : TyExpr (suc n))
           (uᵈ : isDefined (⟦ u ⟧Tm X))
           → isDefined (⟦ A ⟧Ty (toCtx (getTy (totalify (⟦ u ⟧Tm X) uᵈ))))
           → isDefined (⟦ A [ idMor n , u ]Ty ⟧Ty X)

⟦subst⟧Ty= : (X : Ob n) (u : TmExpr n) (A : TyExpr (suc n))
           (uᵈ : isDefined (⟦ u ⟧Tm X))
           (Aᵈ : isDefined (⟦ A ⟧Ty (toCtx (getTy (totalify (⟦ u ⟧Tm X) uᵈ)))))
           → totalify (⟦ A [ idMor n , u ]Ty ⟧Ty X) (⟦subst⟧Tyᵈ X u A uᵈ Aᵈ)
             ≡ substCTy X (shift (toCtxEq (getTy (totalify (⟦ u ⟧Tm X) uᵈ))) (totalify (⟦ A ⟧Ty (toCtx (getTy (totalify (⟦ u ⟧Tm X) uᵈ)))) Aᵈ)) (totalify (⟦ u ⟧Tm X) uᵈ ) (ap-irr _,_ (! (toCtxEq (totalify (⟦ A ⟧Ty (toCtx (getTy (totalify (⟦ u ⟧Tm X) uᵈ)))) Aᵈ))))

-- -- ⟦subst⟧Ty : (X : Ob (m + n)) {A : TyExpr (suc m + n)} {u : TmExpr n} {p : {!!}} {dA : Derivable ({!!} ⊢ A)} {du : Derivable ({!!} ⊢ u :> {!!})}
-- --           → ⟦⟧Ty X (substTy A u) p
-- --           ≡ substCTy ? (shift {!!} (⟦⟧Ty ? A dA)) (⟦⟧Tm ? u du) {!!} -- (⟦⟧Ty ? A dA) (⟦⟧Tm X u du)

-- ⟦subst⟧Ty : (X : Ob n) (Y : Ob m) {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m} (dΔ : ⊢ Δ) (p : ⟦⟧Ctx Δ dΔ ≡ Y) (dA : Derivable (Δ ⊢ A)) (dδ : (Γ ⊢ δ ∷> Δ))
--           → ⟦⟧Ty X (A [ δ ]Ty) (SubstTy dA dδ)
--           ≡ star^-with-eqs (⟦⟧Mor X Y δ dΔ p dδ) refl (∂₀⟦⟧Mor X Y δ dΔ p dδ) (⟦⟧Ty (∂₁ (⟦⟧Mor X Y δ dΔ p dδ)) A dA)
-- ⟦subst⟧Tm : (X : Ob n) (Y : Ob m) {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {u : TmExpr m} {δ : Mor n m} (dΔ : ⊢ Δ) (p : ⟦⟧Ctx Δ dΔ ≡ Y) (du : Derivable (Δ ⊢ u :> A)) (dδ : (Γ ⊢ δ ∷> Δ))
--           → ⟦⟧Tm (∂₀ (⟦⟧Mor X Y δ dΔ p dδ)) (u [ δ ]Tm) (SubstTm du dδ)
--           ≡ star^tm (⟦⟧Mor X Y δ dΔ p dδ) (⟦⟧Tm (∂₁ (⟦⟧Mor X Y δ dΔ p dδ)) u du)

{- Interpretation of weakening -}

⟦weaken⟧Tyᵈ : (X : Ob (suc n)) (A : TyExpr n)
           → isDefined (⟦ A ⟧Ty (ft X))
           → isDefined (⟦ weakenTy A ⟧Ty X)

⟦weaken⟧Ty= : (X : Ob (suc n)) (A : TyExpr n) (Aᵈ : isDefined (⟦ A ⟧Ty (ft X)))
           → totalify (⟦ weakenTy A ⟧Ty X) (⟦weaken⟧Tyᵈ X A Aᵈ)
           ≡ weakenCTy (totalify (⟦ A ⟧Ty (ft X)) Aᵈ)

-- {- Now the definitions of all that -}

-- -- ⟦subst⟧Ty X Y {δ = δ} UU dδ = ! (UUStrNat (⟦⟧Mor X Y δ dδ))
-- -- ⟦subst⟧Ty X Y {A = pi A B} {δ = δ} (Pi dA dB) dδ = {!need rewrite!} where --! {!PiStrNat (⟦⟧Mor X δ dδ) (⟦⟧Ty (∂₁ (⟦⟧Mor X δ dδ)) A dA) (shift ? (⟦⟧Ty (toCtx (⟦⟧Ty (∂₁ (⟦⟧Mor X δ dδ)) A dA)) B dB)) ?!}
-- -- ⟦subst⟧Ty X Y (El dv) dδ = {!need rewrite!}
-- -- ⟦subst⟧Ty X Y (SubstTy dA dδ') dδ = {!!}
-- -- ⟦subst⟧Ty X Y (WeakTy dA) dδ = {!!}

-- -- ⟦subst⟧Tm X Y (VarRule x∈ dA) dδ = {!!}
-- -- ⟦subst⟧Tm X Y (Conv du dA= dA) dδ = ⟦subst⟧Tm X Y du dδ
-- -- ⟦subst⟧Tm X Y (Lam dA dB du) dδ = {!!}
-- -- ⟦subst⟧Tm X Y (App dA dB df da) dδ = {!!}
-- -- ⟦subst⟧Tm X Y (SubstTm du dδ') dδ = {!!}
-- -- ⟦subst⟧Tm X Y (WeakTm du) dδ = {!!}

-- isTotal⟦⟧Ctx {Γ = ◇} tt = tt
-- isTotal⟦⟧Ctx {Γ = Γ , A} (dΓ , dA) = (isTotal⟦⟧Ctx dΓ , (isTotal⟦⟧Ty dΓ dA , tt))

isTotal⟦⟧Ty X r UU = tt
isTotal⟦⟧Ty {Γ = Γ} X r {A = pi A B} (Pi dA dB) = (isTotal⟦⟧Ty X r dA , (isTotal⟦⟧Ty (toCtx (⟦⟧Ty X r dA)) (respectsCtxExt X r A (isTotal⟦⟧Ty X r dA)) dB , tt)) where
isTotal⟦⟧Ty X r (El dv) = (isTotal⟦⟧Tm X r dv , (getTy⟦⟧ X r dv tt , tt))

isTotal⟦⟧Tm X r (VarLast dA) = tt
isTotal⟦⟧Tm X r (VarPrev dA dx) = tt
isTotal⟦⟧Tm X r (Conv dA du dA=) = isTotal⟦⟧Tm X r du
isTotal⟦⟧Tm X r {u = lam A B u} (Lam dA dB du) =
  (isTotal⟦⟧Ty X r dA ,
  (isTotal⟦⟧Ty (toCtx (⟦⟧Ty X r dA)) (respectsCtxExt X r A (isTotal⟦⟧Ty X r dA)) dB ,
  (isTotal⟦⟧Tm (toCtx (⟦⟧Ty X r dA)) (respectsCtxExt X r A (isTotal⟦⟧Ty X r dA)) du ,
  (getTy⟦⟧ (toCtx (⟦⟧Ty X r dA)) (respectsCtxExt X r A (isTotal⟦⟧Ty X r dA)) du (isTotal⟦⟧Ty (toCtx (⟦⟧Ty X r dA)) (respectsCtxExt X r A (isTotal⟦⟧Ty X r dA)) dB) , tt))))
isTotal⟦⟧Tm X r {u = app A B f a} (App dA dB df da) =
  (isTotal⟦⟧Ty X r dA ,
  (isTotal⟦⟧Ty (toCtx (⟦⟧Ty X r dA)) (respectsCtxExt X r A (isTotal⟦⟧Ty X r dA)) dB ,
  (isTotal⟦⟧Tm X r df ,
  (isTotal⟦⟧Tm X r da ,
  (getTy⟦⟧ X r df (isTotal⟦⟧Ty X r dA , ((isTotal⟦⟧Ty (toCtx (⟦⟧Ty X r dA)) (respectsCtxExt X r A (isTotal⟦⟧Ty X r dA)) dB) , tt)) ,
  (getTy⟦⟧ X r da (isTotal⟦⟧Ty X r dA) , tt))))))

-- isTotal⟦⟧Mor X Y {Δ = ◇} r r' {◇} tt = tt
-- isTotal⟦⟧Mor X Y {Δ = Δ , B} r r' {δ , u} (dδ , du) =
--   (isTotal⟦⟧Mor X (ft Y) r dδ ,
--   (isTotal⟦⟧Tm X r du ,
--   ({!!} , -- ∂₁⟦⟧Mor X (ft Y) δ dΔ lemma1 dδ
--   ({!!} , tt))))
--   -- (ap toCtx (getTy⟦⟧ X du (SubstTy dB dδ) {!lemma1!} ∙ ⟦subst⟧Ty X (ft Y) dΔ lemma1 dB dδ) ∙ ap2-irr star refl lemma2) , tt))) where

⟦⟧TyEq X r (TySymm dA=) Aᵈ A'ᵈ = ! (⟦⟧TyEq X r dA= A'ᵈ Aᵈ)
⟦⟧TyEq X r (TyTran dB dA= dB=) Aᵈ A'ᵈ = ⟦⟧TyEq X r dA= Aᵈ (isTotal⟦⟧Ty X r dB) ∙ ⟦⟧TyEq X r dB= (isTotal⟦⟧Ty X r dB) A'ᵈ
⟦⟧TyEq X r {A = pi A B} {A' = pi A' B'} (PiCong dA dA= dB=) (Aᵈ , Bᵈ , _) (A'ᵈ , B'ᵈ , _)
  rewrite ! (⟦⟧TyEq X r dA= Aᵈ A'ᵈ) | ⟦⟧TyEq (toCtx (totalify (⟦ A ⟧Ty X) Aᵈ)) (respectsCtxExt X r A Aᵈ) dB= Bᵈ B'ᵈ = refl
⟦⟧TyEq X r UUCong Aᵈ A'ᵈ = refl
⟦⟧TyEq X r (ElCong dv=) (vᵈ , _) (v'ᵈ , _) rewrite ⟦⟧TmEq X r dv= vᵈ v'ᵈ = refl

⟦⟧TmEq X r (VarLastCong dA) tt tt = refl
⟦⟧TmEq X r (VarPrevCong dA dx) tt tt = ap weakenCTm (⟦⟧TmEq (ft X) (fst r) dx tt tt)
⟦⟧TmEq X r (TmSymm du=) uᵈ u'ᵈ = ! (⟦⟧TmEq X r du= u'ᵈ uᵈ)
⟦⟧TmEq X r (TmTran du= du'=) uᵈ u'ᵈ = ⟦⟧TmEq X r du= uᵈ {!!} ∙ ⟦⟧TmEq X r du'= {!!} u'ᵈ
⟦⟧TmEq X r (ConvEq dA' du= dA=) uᵈ u'ᵈ = ⟦⟧TmEq X r du= uᵈ u'ᵈ
⟦⟧TmEq X r {u = lam A B u} (LamCong dA dA= dB= du=) (Aᵈ , Bᵈ , uᵈ , _) (A'ᵈ , B'ᵈ , u'ᵈ , _)
  rewrite ! (⟦⟧TyEq X r dA= Aᵈ A'ᵈ)
        | ⟦⟧TyEq (toCtx (totalify (⟦ A ⟧Ty X) Aᵈ)) (respectsCtxExt X r A Aᵈ) dB= Bᵈ B'ᵈ
        | ⟦⟧TmEq (toCtx (totalify (⟦ A ⟧Ty X) Aᵈ)) (respectsCtxExt X r A Aᵈ) du= uᵈ u'ᵈ = refl
⟦⟧TmEq X r {u = app A B f a} (AppCong dA dA= dB= df= da=) (Aᵈ , Bᵈ , fᵈ , aᵈ , _) (A'ᵈ , B'ᵈ , f'ᵈ , a'ᵈ , _)
  rewrite ! (⟦⟧TyEq X r dA= Aᵈ A'ᵈ)
        | ⟦⟧TyEq (toCtx (totalify (⟦ A ⟧Ty X) Aᵈ)) (respectsCtxExt X r A Aᵈ) dB= Bᵈ B'ᵈ
        | ⟦⟧TmEq X r df= fᵈ f'ᵈ
        | ⟦⟧TmEq X r da= aᵈ a'ᵈ = refl
⟦⟧TmEq X r (Beta dA dB du da) (Aᵈ , Bᵈ , (_ , _ , uᵈ , _) , aᵈ , _) u'ᵈ = betaStr ∙ {!!}


⟦tsubst⟧Tyᵈ X Y (pi A B) {δ = δ} (Aᵈ , Bᵈ , tt) δᵈ =
  (⟦tsubst⟧Tyᵈ X Y A Aᵈ δᵈ ,
  (⟦tsubst⟧Tyᵈ (toCtx (totalify (⟦ A [ δ ]Ty ⟧Ty X) (⟦tsubst⟧Tyᵈ X Y A Aᵈ δᵈ))) (toCtx (totalify (⟦ A ⟧Ty Y) Aᵈ)) B Bᵈ {!!} , tt))
--  (⟦tsubst⟧Tyᵈ (toCtx (totalify (⟦ A [ δ ]Ty ⟧Ty X) (⟦tsubst⟧Tyᵈ {k = k} X Y A Aᵈ δᵈ))) (toCtx (totalify (⟦ A ⟧Ty Y) Aᵈ)) B Bᵈ {!δᵈ!} , tt)) --(⟦tsubst⟧Tyᵈ (toCtx (totalify (⟦ A [ δ ]Ty ⟧Ty X) (⟦tsubst⟧Tyᵈ X Y A r Aᵈ δᵈ))) (toCtx (totalify (⟦ A ⟧Ty Y) Aᵈ)) B {!!} Bᵈ ({!!} , {!!}) , tt))
⟦tsubst⟧Tyᵈ X Y uu tt δᵈ = tt
⟦tsubst⟧Tyᵈ X Y (el v) (vᵈ , vTy , tt) δᵈ = {!!}

⟦substExt⟧Tyᵈ X Y T δᵈ = {!!}

⟦weaken⟧Tyᵈ X (pi A B) (Aᵈ , Bᵈ , tt) = (⟦weaken⟧Tyᵈ X A Aᵈ) , ({!!} , tt)
⟦weaken⟧Tyᵈ X uu Aᵈ = tt
⟦weaken⟧Tyᵈ X (el v) Aᵈ = {!!}

-- isTotal⟦⟧Ctx : {Γ : Ctx n} → ⊢ Γ → isDefined (⟦ Γ ⟧Ctx)
-- isTotal⟦⟧Mor : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} (dΓ : ⊢ Γ) (dΔ : ⊢ Δ) (dδ : Γ ⊢ δ ∷> Δ) → isDefined (⟦ δ ⟧Mor (⟦⟧Ctx dΓ) (⟦⟧Ctx dΔ))

-- ⟦⟧Ctx : {Γ : Ctx n} (dΓ : ⊢ Γ) → Ob n
-- ⟦⟧Ctx {Γ = Γ} dΓ = totalify (⟦ Γ ⟧Ctx) (isTotal⟦⟧Ctx dΓ)

-- ⟦⟧Mor : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} (dΓ : ⊢ Γ) (dΔ : ⊢ Δ) (dδ : Γ ⊢ δ ∷> Δ) → MorC n m
-- ⟦⟧Mor {δ = δ} dΓ dΔ dδ = totalify (⟦ δ ⟧Mor (⟦⟧Ctx dΓ) (⟦⟧Ctx dΔ)) (isTotal⟦⟧Mor dΓ dΔ dδ)

-- ∂₀⟦⟧Mor : {Γ : Ctx n} (X : Ob n) (Y : Ob m) {Δ : Ctx m} (δ : Mor n m) (dΔ : ⊢ Δ) (p : ⟦⟧Ctx Δ dΔ ≡ Y) (dδ : Γ ⊢ δ ∷> Δ) → ∂₀ (⟦⟧Mor X Y δ dΔ p dδ) ≡ X
-- ∂₁⟦⟧Mor : {Γ : Ctx n} (X : Ob n) (Y : Ob m) {Δ : Ctx m} (δ : Mor n m) (dΔ : ⊢ Δ) (p : ⟦⟧Ctx Δ dΔ ≡ Y) (dδ : Γ ⊢ δ ∷> Δ) → ∂₁ (⟦⟧Mor X Y δ dΔ p dδ) ≡ Y

-- isTotal⟦⟧Mor {Δ = ◇} X Y {◇} tt p tt = tt
-- isTotal⟦⟧Mor {Δ = Δ , B} X Y {δ , u} (dΔ , dB) p (dδ , du) =
--   (isTotal⟦⟧Mor X (ft Y) dΔ (! (lemma4 dΔ dB) ∙ ap ft p) dδ ,
--   (isTotal⟦⟧Tm X du ,
--   (∂₁⟦⟧Mor X (ft Y) δ dΔ lemma1 dδ ,
--   (ap toCtx (getTy⟦⟧ X du (SubstTy dB dδ) {!lemma1!} ∙ ⟦subst⟧Ty X (ft Y) dΔ lemma1 dB dδ) ∙ ap2-irr star refl lemma2) , tt))) where

-- ∂₀⟦⟧Mor X Y {◇} ◇ dΔ p dδ = ptmor₀
-- ∂₀⟦⟧Mor X Y {Δ , B} (δ , u) (dΔ , dB) p (dδ , du) = comp₀ ∙ morTm₀ (⟦⟧Tm X u du) ∙ toCtxEq (getTy (⟦⟧Tm X u du))

-- ∂₁⟦⟧Mor X _ {◇} ◇ dΔ refl dδ = ptmor₁
-- ∂₁⟦⟧Mor X Y {Δ , B} (δ , u) (dΔ , dB) p (dδ , du) = comp₁ ∙ qq₁

getTy⟦⟧ X r (VarLast {A = A} dA) Aᵈ = ap-irr _,_ (ap2-irr star refl (! (snd (snd r))) ∙ ! (ap toCtx (⟦weaken⟧Ty= X A (fst (snd r)))))
getTy⟦⟧ X r (VarPrev {B = B} {A = A} dA dx) Aᵈ = ! (⟦weaken⟧Ty= X A (isTotal⟦⟧Ty (ft X) (fst r) dA) ∙ ap weakenCTy (! (getTy⟦⟧ (ft X) (fst r) dx (isTotal⟦⟧Ty (ft X) (fst r) dA))))
getTy⟦⟧ X r (Conv dA du dA=) Aᵈ = getTy⟦⟧ X r du (isTotal⟦⟧Ty X r dA) ∙ ⟦⟧TyEq X r dA= (isTotal⟦⟧Ty X r dA) Aᵈ
getTy⟦⟧ X r (Lam dA dB du) Aᵈ = lamStrTy
getTy⟦⟧ {n = n} {Γ = Γ} X r {u = app A B f a} (App dA dB df da) Aᵈ = appStrTy ∙ aux  where

  [A] : Ty X 0
  [A] = totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA)

  [B] : Ty (toCtx (totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA))) 0
  [B] = totalify (⟦ B ⟧Ty (toCtx (totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA)))) (isTotal⟦⟧Ty (toCtx (totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA))) (respectsCtxExt X r A (isTotal⟦⟧Ty X r dA)) dB)

  ppy : getTy (⟦⟧Tm X r da) ≡ ft' (shift (toCtxEq (totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA))) (totalify (⟦ B ⟧Ty (toCtx (totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA)))) (isTotal⟦⟧Ty (toCtx (totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA))) (respectsCtxExt X r A (isTotal⟦⟧Ty X r dA)) dB)))
  ppy = {!!}

  aux : substCTy X (shift (toCtxEq (totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA))) (totalify (⟦ B ⟧Ty (toCtx (totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA)))) (isTotal⟦⟧Ty (toCtx (totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA))) (respectsCtxExt X r A (isTotal⟦⟧Ty X r dA)) dB))) (⟦⟧Tm X r da) ppy ≡ totalify (⟦ B [ idMor n , a ]Ty ⟧Ty X) _
  aux = ! (⟦subst⟧Ty= X a B (isTotal⟦⟧Tm X r da) aux1 ∙ aux2)  where

    aux1 : isDefined (⟦ B ⟧Ty (toCtx (getTy (totalify (⟦ a ⟧Tm X) (isTotal⟦⟧Tm X r da)))))
    aux1 rewrite getTy⟦⟧ X r da (isTotal⟦⟧Ty X r dA) = isTotal⟦⟧Ty (M.toCtx (totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA))) (respectsCtxExt X r A (isTotal⟦⟧Ty X r dA)) dB

    aux2 : {!!}
    aux2 = {!!}

  aux4 : isDefined (⟦ B ⟧Ty (toCtx (getTy (totalify (⟦ a ⟧Tm X) (isTotal⟦⟧Tm X r da)))))
  aux4 rewrite getTy⟦⟧ X r da (isTotal⟦⟧Ty X r dA) = isTotal⟦⟧Ty (toCtx (totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA))) (respectsCtxExt X r A (isTotal⟦⟧Ty X r dA)) dB

  aux3 : totalify (⟦ B [ idMor n , a ]Ty ⟧Ty X) _ ≡ {!!}
  aux3 = ⟦subst⟧Ty= X a B (isTotal⟦⟧Tm X r da) aux4

  aux5 : _ ≡ _
  aux5 rewrite getTy⟦⟧ X r da (isTotal⟦⟧Ty X r dA) = ⟦subst⟧Ty= X a B (isTotal⟦⟧Tm X r da) aux4
