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

{- Totality of the partial interpretation functions -}

isTotal⟦⟧Ctx : {Γ : Ctx n} → ⊢ Γ → isDefined (⟦ Γ ⟧Ctx)
isTotal⟦⟧Ty  : {Γ : Ctx n} (X : Ob n) {A : TyExpr n} (_ : Derivable (Γ ⊢ A)) → isDefined (⟦ A ⟧Ty X)
isTotal⟦⟧Tm  : {Γ : Ctx n} (X : Ob n) {A : TyExpr n} {u : TmExpr n} → Derivable (Γ ⊢ u :> A) → isDefined (⟦ u ⟧Tm X)
isTotal⟦⟧Mor : {Γ : Ctx n} {Δ : Ctx m} (X : Ob n) (Y : Ob m) {δ : Mor n m} → (Γ ⊢ δ ∷> Δ) → isDefined (⟦ δ ⟧Mor X Y)

{- The total interpretation functions, derived from the totality -}

⟦⟧Ctx : (Γ : Ctx n) (_ : ⊢ Γ) → Ob n
⟦⟧Ctx Γ dΓ = totalify (⟦ Γ ⟧Ctx) (isTotal⟦⟧Ctx dΓ)

⟦⟧Ty : {Γ : Ctx n} (X : Ob n) (A : TyExpr n) (_ : Derivable (Γ ⊢ A)) → Ty X 0
⟦⟧Ty X A dA = totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X dA)

⟦⟧Tm : {Γ : Ctx n} (X : Ob n) {A : TyExpr n} (u : TmExpr n) (_ : Derivable (Γ ⊢ u :> A)) → Tm X 0
⟦⟧Tm X u du = totalify (⟦ u ⟧Tm X) (isTotal⟦⟧Tm X du)

⟦⟧Mor : {Γ : Ctx n} (X : Ob n) (Y : Ob m) {Δ : Ctx m} (δ : Mor n m) (_ : Γ ⊢ δ ∷> Δ) → MorC n m
⟦⟧Mor X Y δ dδ = totalify (⟦ δ ⟧Mor X Y) (isTotal⟦⟧Mor X Y dδ)

{- The type of the interpretation of a term is the interpretation of its type -}

getTy⟦⟧ : {Γ : Ctx n} (X : Ob n) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) (dA : Derivable (Γ ⊢ A)) → getTy (⟦⟧Tm X u du) ≡ ⟦⟧Ty X A dA
∂₀⟦⟧Mor : {Γ : Ctx n} (X : Ob n) (Y : Ob m) {Δ : Ctx m} (δ : Mor n m) (dδ : Γ ⊢ δ ∷> Δ) → ∂₀ (⟦⟧Mor X Y δ dδ) ≡ X
∂₁⟦⟧Mor : {Γ : Ctx n} (X : Ob n) (Y : Ob m) {Δ : Ctx m} (δ : Mor n m) (dδ : Γ ⊢ δ ∷> Δ) → ∂₁ (⟦⟧Mor X Y δ dδ) ≡ Y

{- Interpretation of definitional equalities -}

⟦⟧TyEq : {Γ : Ctx n} (X : Ob n) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A')) (dA : isDefined (⟦ A ⟧Ty X)) (dA' : isDefined (⟦ A' ⟧Ty X))
        → totalify (⟦ A ⟧Ty X) dA ≡ totalify (⟦ A' ⟧Ty X) dA'
⟦⟧TmEq : {Γ : Ctx n} (X : Ob n) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A')) (dA : isDefined (⟦ A ⟧Ty X)) (dA' : isDefined (⟦ A' ⟧Ty X))
        → totalify (⟦ A ⟧Ty X) dA ≡ totalify (⟦ A' ⟧Ty X) dA'

{- Interpretation of substitutions -}

⟦subst⟧Ty : (X : Ob n) (Y : Ob m) {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m} (dA : Derivable (Δ ⊢ A)) (dδ : (Γ ⊢ δ ∷> Δ))
          → ⟦⟧Ty (∂₀ (⟦⟧Mor X Y δ dδ)) (A [ δ ]Ty) (SubstTy dA dδ)
          ≡ star^ (⟦⟧Mor X Y δ dδ) (⟦⟧Ty (∂₁ (⟦⟧Mor X Y δ dδ)) A dA)
⟦subst⟧Tm : (X : Ob n) (Y : Ob m) {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {u : TmExpr m} {δ : Mor n m} (du : Derivable (Δ ⊢ u :> A)) (dδ : (Γ ⊢ δ ∷> Δ))
          → ⟦⟧Tm (∂₀ (⟦⟧Mor X Y δ dδ)) (u [ δ ]Tm) (SubstTm du dδ)
          ≡ star^tm (⟦⟧Mor X Y δ dδ) (⟦⟧Tm (∂₁ (⟦⟧Mor X Y δ dδ)) u du)

{-
⟦ weaken A ⟧ = …
-}

{- Now the definitions of all that -}

⟦subst⟧Ty X Y {δ = δ} UU dδ = ! (UUStrNat (⟦⟧Mor X Y δ dδ))
⟦subst⟧Ty X Y {A = pi A B} {δ = δ} (Pi dA dB) dδ = {!need rewrite!} where --! {!PiStrNat (⟦⟧Mor X δ dδ) (⟦⟧Ty (∂₁ (⟦⟧Mor X δ dδ)) A dA) (shift ? (⟦⟧Ty (toCtx (⟦⟧Ty (∂₁ (⟦⟧Mor X δ dδ)) A dA)) B dB)) ?!}
⟦subst⟧Ty X Y (El dv) dδ = {!need rewrite!}
⟦subst⟧Ty X Y (SubstTy dA dδ') dδ = {!!}
⟦subst⟧Ty X Y (WeakTy dA) dδ = {!!}

⟦subst⟧Tm X Y (VarRule x∈ dA) dδ = {!!}
⟦subst⟧Tm X Y (Conv du dA= dA) dδ = ⟦subst⟧Tm X Y du dδ
⟦subst⟧Tm X Y (Lam dA dB du) dδ = {!!}
⟦subst⟧Tm X Y (App dA dB df da) dδ = {!!}
⟦subst⟧Tm X Y (SubstTm du dδ') dδ = {!!}
⟦subst⟧Tm X Y (WeakTm du) dδ = {!!}

isTotal⟦⟧Ctx {Γ = ◇} tt = tt
isTotal⟦⟧Ctx {Γ = Γ , A} (dΓ , dA) = (isTotal⟦⟧Ctx dΓ , (isTotal⟦⟧Ty (⟦⟧Ctx Γ dΓ) dA , tt))

isTotal⟦⟧Ty X UU = tt
isTotal⟦⟧Ty X {A = pi A B} (Pi dA dB) = (isTotal⟦⟧Ty X dA , (isTotal⟦⟧Ty (toCtx (⟦⟧Ty X A dA)) dB , tt))
isTotal⟦⟧Ty X (El dv) = (isTotal⟦⟧Tm X dv , (getTy⟦⟧ X dv {!UU!} , tt))
isTotal⟦⟧Ty X (SubstTy _ _) = {!!}
isTotal⟦⟧Ty X (WeakTy dA) = {!!}

isTotal⟦⟧Tm X (VarRule x∈ dA) = tt
isTotal⟦⟧Tm X (Conv du dA= dA) = isTotal⟦⟧Tm X du
isTotal⟦⟧Tm X {u = lam A B u} (Lam dA dB du) =
  (isTotal⟦⟧Ty X dA ,
  (isTotal⟦⟧Ty (toCtx (⟦⟧Ty X A dA)) dB ,
  (isTotal⟦⟧Tm (toCtx (⟦⟧Ty X A dA)) du ,
  (getTy⟦⟧ (toCtx (⟦⟧Ty X A dA)) du dB , tt))))
isTotal⟦⟧Tm X {u = app A B f a} (App dA dB df da) =
  (isTotal⟦⟧Ty X dA ,
  (isTotal⟦⟧Ty (toCtx (⟦⟧Ty X A dA)) dB ,
  (isTotal⟦⟧Tm X df ,
  (isTotal⟦⟧Tm X da ,
  (getTy⟦⟧ X df (Pi dA dB) ,
  (getTy⟦⟧ X da dA , tt))))))
isTotal⟦⟧Tm X (SubstTm du dδ) = {!!}
isTotal⟦⟧Tm X (WeakTm du) = {!!}

isTotal⟦⟧Mor {Δ = ◇} X Y {◇} tt = tt
isTotal⟦⟧Mor {Δ = Δ , B} X Y {δ , u} (dδ , du) =
  (isTotal⟦⟧Mor X (ft Y) dδ ,
  (isTotal⟦⟧Tm X du ,
  (∂₁⟦⟧Mor X (ft Y) _ dδ ,
  ((morTm₁ (totalify (⟦ u ⟧Tm X) (isTotal⟦⟧Tm X du)) ∙ ((ap toCtx (getTy⟦⟧ X du {!!}) ∙ {!⟦subst⟧Ty!}) ∙ ! qq₀)) , tt))))

getTy⟦⟧ X (VarRule x∈ dA) dA' = {!!}
getTy⟦⟧ X (Conv du dA= dA) dA' = getTy⟦⟧ X du dA ∙ ⟦⟧TyEq X dA= (isTotal⟦⟧Ty X dA) (isTotal⟦⟧Ty X dA')
getTy⟦⟧ X (Lam dA dB du) dA' = lamStrTy
getTy⟦⟧ X (App dA dB df da) dA' = appStrTy ∙ ! {!!}
getTy⟦⟧ X (SubstTm du dδ) dA' = {!!}
getTy⟦⟧ X (WeakTm du) dA' = {!!}

apB-irr : {A C : Set} {B : A → Prop} (f : (a : A) (b : Box (B a)) → C) {a a' : A} (p : a ≡ a') {b : Box (B a)} {b' : Box (B a')} → f a b ≡ f a' b'
apB-irr f refl = refl

⟦⟧TyEq X (TySymm dA=) dA dA' = ! (⟦⟧TyEq X dA= dA' dA)
⟦⟧TyEq X (TyTran dA= dB= dB) dA dA' = ⟦⟧TyEq X dA= dA (isTotal⟦⟧Ty X dB) ∙ ⟦⟧TyEq X dB= (isTotal⟦⟧Ty X dB) dA'
⟦⟧TyEq X {A = pi A B} {A' = pi A' B'} (PiCong dA= dB=) ([A] , ([B] , tt)) ([A'] , ([B'] , tt)) = {!!}
⟦⟧TyEq X UUCong dA dA' = refl
⟦⟧TyEq X (ElCong dv=) dA dA' = ap-irr (ElStr X) {!⟦⟧TmEq X dv=!}
⟦⟧TyEq X (SubstTyEq dA= dδ) dA dA' = {!!}
⟦⟧TyEq X (SubstTySubstEq dA= dδ=) dA dA' = {!!}
⟦⟧TyEq X (WeakTyEq dA=) dA dA' = {!!}

--  rewrite ⟦⟧TyEq X dA= [A] [A'] | ⟦⟧TyEq (toCtx (totalify (⟦ A' ⟧Ty X) [A'])) dB= [B] [B'] = reflR

 --= --apP2-irr (PiStr X) (makeSetify (⟦⟧TyEq X dA= [A] [A'])) {!⟦⟧TyEq ? dB= [B] [B']!}
