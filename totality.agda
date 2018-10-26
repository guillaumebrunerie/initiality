{-# OPTIONS --irrelevant-projections --prop #-}

open import common hiding (_≡R_)
open import syntx
open import contextualcat
open import rules

module _ (C : StructuredCCat) where

open StructuredCCat C
open CCat ccat renaming (Mor to MorC)
open M ccat
open import partialinterpretation C

isDefined : {A : Set} → Partial A → Prop
isDefined (makePartial prop inj) = prop

totalify : {A : Set} (x : Partial A) (_ : isDefined x) → A
totalify (makePartial prop inj) a = inj a




isTotal⟦⟧ctx : {Γ : Ctx n} → ⊢ Γ → isDefined (⟦ Γ ⟧ctx)
isTotal⟦⟧ty  : {Γ : Ctx n} (X : Ob n) {A : TyExpr n} (_ : Derivable (Γ ⊢ A)) → isDefined (⟦ A ⟧ty X)
isTotal⟦⟧tm  : {Γ : Ctx n} (X : Ob n) {A : TyExpr n} {u : TmExpr n} → Derivable (Γ ⊢ u :> A) → isDefined (⟦ u ⟧tm X)

⟦⟧ctx : (Γ : Ctx n) → ⊢ Γ → Ob n
⟦⟧ctx Γ dΓ = totalify (⟦ Γ ⟧ctx) (isTotal⟦⟧ctx dΓ)

⟦⟧ty : {Γ : Ctx n} (X : Ob n) (A : TyExpr n) (_ : Derivable (Γ ⊢ A)) → Ty X 0
⟦⟧ty X A dA = totalify (⟦ A ⟧ty X) (isTotal⟦⟧ty X dA)

⟦⟧tm : {Γ : Ctx n} (X : Ob n) {A : TyExpr n} (u : TmExpr n) → Derivable (Γ ⊢ u :> A) → Tm X 0
⟦⟧tm X u du = totalify (⟦ u ⟧tm X) (isTotal⟦⟧tm X du)

⟦⟧mor : {Γ : Ctx n} (X : Ob n) {Δ : Ctx m} (δ : Mor n m) → (Γ ⊢ δ ∷> Δ) → MorC n m
⟦⟧mor X δ dδ = {!!}

.getTy⟦⟧ : {Γ : Ctx n} (X : Ob n) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) (dA : Derivable (Γ ⊢ A)) → getTy (⟦⟧tm X u du) ≡P ⟦⟧ty X A dA


∂₀⟦⟧mor : {Γ : Ctx n} (X : Ob n) {Δ : Ctx m} (δ : Mor n m) (dδ : Γ ⊢ δ ∷> Δ) → ∂₀ (⟦⟧mor X δ dδ) ≡ X

{-
⟦ weaken A ⟧ = …
-}

⟦⟧tyEq : {Γ : Ctx n} (X : Ob n) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A')) (dA : isDefined (⟦ A ⟧ty X)) (dA' : isDefined (⟦ A' ⟧ty X))
        → totalify (⟦ A ⟧ty X) dA ≡P totalify (⟦ A' ⟧ty X) dA'

.⟦subst⟧Ty : (X : Ob n) {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m} (dA : Derivable (Δ ⊢ A)) (dδ : (Γ ⊢ δ ∷> Δ))
          → ⟦⟧ty X (A [ δ ]Ty) (SubstTy dA dδ)
          ≡ star^-with-eqs (⟦⟧mor X δ dδ) refl (∂₀⟦⟧mor X δ dδ) (⟦⟧ty (∂₁ (⟦⟧mor X δ dδ)) A dA)
-- ⟦subst⟧Ty X {δ = δ} UU dδ = helper (∂₀⟦⟧mor X δ dδ) where
--   .helper : {Y : _} {Z : _} (p : ∂₀ (⟦⟧mor Y δ dδ) ≡R Z) → UUStr Z ≡ star^-with-eqs (⟦⟧mor Y δ dδ) refl (toS p) (UUStr (∂₁ (⟦⟧mor Y δ dδ)))
--   helper {Y = Y} reflR = ! (UUStrNat (⟦⟧mor Y δ dδ))
-- ⟦subst⟧Ty X {A = pi A B} {δ = δ} (Pi dA dB) dδ {-rewrite ⟦subst⟧Ty X dA dδ-} = {!!} --! {!PiStrNat (⟦⟧mor X δ dδ) (⟦⟧ty (∂₁ (⟦⟧mor X δ dδ)) A dA) (shift ? (⟦⟧ty (toCtx (⟦⟧ty (∂₁ (⟦⟧mor X δ dδ)) A dA)) B dB)) ?!}
-- ⟦subst⟧Ty X (El dv) dδ = {!!}
-- ⟦subst⟧Ty X (SubstTy dA dδ') dδ = {!!}
-- ⟦subst⟧Ty X (WeakTy dA) dδ = {!!}

isTotal⟦⟧ctx {Γ = ◇} tt = tt
isTotal⟦⟧ctx {Γ = Γ , A} (dΓ , dA) = (isTotal⟦⟧ctx dΓ , (isTotal⟦⟧ty (⟦⟧ctx Γ dΓ) dA , tt))

isTotal⟦⟧ty X UU = tt
isTotal⟦⟧ty X {A = pi A B} (Pi dA dB) = (isTotal⟦⟧ty X dA , (isTotal⟦⟧ty (toCtx (⟦⟧ty X A dA)) dB , tt))
isTotal⟦⟧ty X (El dv) = (isTotal⟦⟧tm X dv , ({!!} , tt))
isTotal⟦⟧ty X (SubstTy _ _) = {!!}
isTotal⟦⟧ty X (WeakTy dA) = {!!}

isTotal⟦⟧tm X (VarRule x∈ dA) = tt
isTotal⟦⟧tm X (Conv du dA= dA) = {!!}
isTotal⟦⟧tm X {u = lam A B u} (Lam dA dB du) =
  (isTotal⟦⟧ty X dA ,
  (isTotal⟦⟧ty (toCtx (⟦⟧ty X A dA)) dB ,
  (isTotal⟦⟧tm (toCtx (⟦⟧ty X A dA)) du ,
  (getTy⟦⟧ (toCtx (⟦⟧ty X A dA)) du dB , tt))))
isTotal⟦⟧tm X {u = app A B f a} (App dA dB df da) =
  (isTotal⟦⟧ty X dA ,
  (isTotal⟦⟧ty (toCtx (⟦⟧ty X A dA)) dB ,
  (isTotal⟦⟧tm X df ,
  (isTotal⟦⟧tm X da ,
  ({!!} ,
  ({!!} , tt))))))
isTotal⟦⟧tm X (SubstTm du dδ) = {!!}
isTotal⟦⟧tm X (WeakTm du) = {!!}

getTy⟦⟧ X (VarRule x∈ dA) dA' = {!!}
getTy⟦⟧ X (Conv du dA= dA) dA' = getTy⟦⟧ X du dA ∙P ⟦⟧tyEq X dA= (isTotal⟦⟧ty X dA) (isTotal⟦⟧ty X dA') -- 
getTy⟦⟧ X (Lam dA dB du) dA' = Setify.inside lamStrTy
getTy⟦⟧ X (App dA dB df da) dA' = {!appStrTy!}
getTy⟦⟧ X (SubstTm du dδ) dA' = {!!}
getTy⟦⟧ X (WeakTm du) dA' = {!!}

⟦⟧tyEq X (TySymm dA=) dA dA' = !P (⟦⟧tyEq X dA= dA' dA)
⟦⟧tyEq X (TyTran dA= dB= dB) dA dA' = ⟦⟧tyEq X dA= dA (isTotal⟦⟧ty X dB) ∙P ⟦⟧tyEq X dB= (isTotal⟦⟧ty X dB) dA'
⟦⟧tyEq X {A = pi A B} {A' = pi A' B'} (PiCong dA= dB=) ([A] , ([B] , tt)) ([A'] , ([B'] , tt)) = {!!}
⟦⟧tyEq X UUCong dA dA' = reflP
⟦⟧tyEq X (ElCong dv=) dA dA' = {!!}
⟦⟧tyEq X (SubstTyEq dA= dδ) dA dA' = {!!}
⟦⟧tyEq X (SubstTySubstEq dA= dδ=) dA dA' = {!!}
⟦⟧tyEq X (WeakTyEq dA=) dA dA' = {!!}

--  rewrite ⟦⟧tyEq X dA= [A] [A'] | ⟦⟧tyEq (toCtx (totalify (⟦ A' ⟧ty X) [A'])) dB= [B] [B'] = reflR

 --= --apP2-irr (PiStr X) (makeSetify (⟦⟧tyEq X dA= [A] [A'])) {!⟦⟧tyEq ? dB= [B] [B']!}


