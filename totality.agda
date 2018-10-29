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

isTotal⟦⟧ctx : {Γ : Ctx n} → ⊢ Γ → isDefined (⟦ Γ ⟧ctx)
isTotal⟦⟧ty  : {Γ : Ctx n} (X : Ob n) {A : TyExpr n} (_ : Derivable (Γ ⊢ A)) → isDefined (⟦ A ⟧ty X)
isTotal⟦⟧tm  : {Γ : Ctx n} (X : Ob n) {A : TyExpr n} {u : TmExpr n} → Derivable (Γ ⊢ u :> A) → isDefined (⟦ u ⟧tm X)
isTotal⟦⟧mor : {Γ : Ctx n} {Δ : Ctx m} (X : Ob n) (Y : Ob m) {δ : Mor n m} → (Γ ⊢ δ ∷> Δ) → isDefined (⟦ δ ⟧mor X Y)

{- The total interpretation functions, derived from the totality -}

⟦⟧ctx : (Γ : Ctx n) (_ : ⊢ Γ) → Ob n
⟦⟧ctx Γ dΓ = totalify (⟦ Γ ⟧ctx) (isTotal⟦⟧ctx dΓ)

⟦⟧ty : {Γ : Ctx n} (X : Ob n) (A : TyExpr n) (_ : Derivable (Γ ⊢ A)) → Ty X 0
⟦⟧ty X A dA = totalify (⟦ A ⟧ty X) (isTotal⟦⟧ty X dA)

⟦⟧tm : {Γ : Ctx n} (X : Ob n) {A : TyExpr n} (u : TmExpr n) (_ : Derivable (Γ ⊢ u :> A)) → Tm X 0
⟦⟧tm X u du = totalify (⟦ u ⟧tm X) (isTotal⟦⟧tm X du)

⟦⟧mor : {Γ : Ctx n} (X : Ob n) (Y : Ob m) {Δ : Ctx m} (δ : Mor n m) (_ : Γ ⊢ δ ∷> Δ) → MorC n m
⟦⟧mor X Y δ dδ = totalify (⟦ δ ⟧mor X Y) (isTotal⟦⟧mor X Y dδ)

{- The type of the interpretation of a term is the interpretation of its type -}

getTy⟦⟧ : {Γ : Ctx n} (X : Ob n) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) (dA : Derivable (Γ ⊢ A)) → getTy (⟦⟧tm X u du) ≡ ⟦⟧ty X A dA
∂₀⟦⟧mor : {Γ : Ctx n} (X : Ob n) (Y : Ob m) {Δ : Ctx m} (δ : Mor n m) (dδ : Γ ⊢ δ ∷> Δ) → ∂₀ (⟦⟧mor X Y δ dδ) ≡ X
∂₁⟦⟧mor : {Γ : Ctx n} (X : Ob n) (Y : Ob m) {Δ : Ctx m} (δ : Mor n m) (dδ : Γ ⊢ δ ∷> Δ) → ∂₁ (⟦⟧mor X Y δ dδ) ≡ Y

{- Interpretation of definitional equalities -}

⟦⟧tyEq : {Γ : Ctx n} (X : Ob n) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A')) (dA : isDefined (⟦ A ⟧ty X)) (dA' : isDefined (⟦ A' ⟧ty X))
        → totalify (⟦ A ⟧ty X) dA ≡ totalify (⟦ A' ⟧ty X) dA'

{- Interpretation of substitutions -}

⟦subst⟧Ty : (X : Ob n) (Y : Ob m) {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m} (dA : Derivable (Δ ⊢ A)) (dδ : (Γ ⊢ δ ∷> Δ))
          → ⟦⟧ty (∂₀ (⟦⟧mor X Y δ dδ)) (A [ δ ]Ty) (SubstTy dA dδ)
          ≡ star^ (⟦⟧mor X Y δ dδ) (⟦⟧ty (∂₁ (⟦⟧mor X Y δ dδ)) A dA)
⟦subst⟧Tm : (X : Ob n) (Y : Ob m) {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {u : TmExpr m} {δ : Mor n m} (du : Derivable (Δ ⊢ u :> A)) (dδ : (Γ ⊢ δ ∷> Δ))
          → ⟦⟧tm (∂₀ (⟦⟧mor X Y δ dδ)) (u [ δ ]Tm) (SubstTm du dδ)
          ≡ star^tm (⟦⟧mor X Y δ dδ) (⟦⟧tm (∂₁ (⟦⟧mor X Y δ dδ)) u du)

{-
⟦ weaken A ⟧ = …
-}

{- Now the definitions of all that -}

⟦subst⟧Ty X Y {δ = δ} UU dδ = ! (UUStrNat (⟦⟧mor X Y δ dδ))
⟦subst⟧Ty X Y {A = pi A B} {δ = δ} (Pi dA dB) dδ = {!need rewrite!} where --! {!PiStrNat (⟦⟧mor X δ dδ) (⟦⟧ty (∂₁ (⟦⟧mor X δ dδ)) A dA) (shift ? (⟦⟧ty (toCtx (⟦⟧ty (∂₁ (⟦⟧mor X δ dδ)) A dA)) B dB)) ?!}
⟦subst⟧Ty X Y (El dv) dδ = {!need rewrite!}
⟦subst⟧Ty X Y (SubstTy dA dδ') dδ = {!!}
⟦subst⟧Ty X Y (WeakTy dA) dδ = {!!}

⟦subst⟧Tm X Y (VarRule x∈ dA) dδ = {!!}
⟦subst⟧Tm X Y (Conv du dA= dA) dδ = ⟦subst⟧Tm X Y du dδ
⟦subst⟧Tm X Y (Lam dA dB du) dδ = {!!}
⟦subst⟧Tm X Y (App dA dB df da) dδ = {!!}
⟦subst⟧Tm X Y (SubstTm du dδ') dδ = {!!}
⟦subst⟧Tm X Y (WeakTm du) dδ = {!!}

isTotal⟦⟧ctx {Γ = ◇} tt = tt
isTotal⟦⟧ctx {Γ = Γ , A} (dΓ , dA) = (isTotal⟦⟧ctx dΓ , (isTotal⟦⟧ty (⟦⟧ctx Γ dΓ) dA , tt))

isTotal⟦⟧ty X UU = tt
isTotal⟦⟧ty X {A = pi A B} (Pi dA dB) = (isTotal⟦⟧ty X dA , (isTotal⟦⟧ty (toCtx (⟦⟧ty X A dA)) dB , tt))
isTotal⟦⟧ty X (El dv) = (isTotal⟦⟧tm X dv , (getTy⟦⟧ X dv {!UU!} , tt))
isTotal⟦⟧ty X (SubstTy _ _) = {!!}
isTotal⟦⟧ty X (WeakTy dA) = {!!}

isTotal⟦⟧tm X (VarRule x∈ dA) = tt
isTotal⟦⟧tm X (Conv du dA= dA) = isTotal⟦⟧tm X du
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
  (getTy⟦⟧ X df (Pi dA dB) ,
  (getTy⟦⟧ X da dA , tt))))))
isTotal⟦⟧tm X (SubstTm du dδ) = {!!}
isTotal⟦⟧tm X (WeakTm du) = {!!}

isTotal⟦⟧mor {Δ = ◇} X Y {◇} tt = tt
isTotal⟦⟧mor {Δ = Δ , B} X Y {δ , u} (dδ , du) =
  (isTotal⟦⟧mor X (ft Y) dδ ,
  (isTotal⟦⟧tm X du ,
  (∂₁⟦⟧mor X (ft Y) _ dδ ,
  ((morTm₁ (totalify (⟦ u ⟧tm X) (isTotal⟦⟧tm X du)) ∙ ((ap toCtx (getTy⟦⟧ X du {!!}) ∙ {!⟦subst⟧Ty!}) ∙ ! qq₀)) , tt))))

getTy⟦⟧ X (VarRule x∈ dA) dA' = {!!}
getTy⟦⟧ X (Conv du dA= dA) dA' = getTy⟦⟧ X du dA ∙ ⟦⟧tyEq X dA= (isTotal⟦⟧ty X dA) (isTotal⟦⟧ty X dA')
getTy⟦⟧ X (Lam dA dB du) dA' = lamStrTy
getTy⟦⟧ X (App dA dB df da) dA' = appStrTy ∙ ! {!!}
getTy⟦⟧ X (SubstTm du dδ) dA' = {!!}
getTy⟦⟧ X (WeakTm du) dA' = {!!}

apB-irr : {A C : Set} {B : A → Prop} (f : (a : A) (b : Box (B a)) → C) {a a' : A} (p : a ≡ a') {b : Box (B a)} {b' : Box (B a')} → f a b ≡ f a' b'
apB-irr f refl = refl

⟦⟧tyEq X (TySymm dA=) dA dA' = ! (⟦⟧tyEq X dA= dA' dA)
⟦⟧tyEq X (TyTran dA= dB= dB) dA dA' = ⟦⟧tyEq X dA= dA (isTotal⟦⟧ty X dB) ∙ ⟦⟧tyEq X dB= (isTotal⟦⟧ty X dB) dA'
⟦⟧tyEq X {A = pi A B} {A' = pi A' B'} (PiCong dA= dB=) ([A] , ([B] , tt)) ([A'] , ([B'] , tt)) = {!!}
⟦⟧tyEq X UUCong dA dA' = refl
⟦⟧tyEq X (ElCong dv=) dA dA' = ap-irr (ElStr X) {!⟦⟧tmEq X dv=!}
⟦⟧tyEq X (SubstTyEq dA= dδ) dA dA' = {!!}
⟦⟧tyEq X (SubstTySubstEq dA= dδ=) dA dA' = {!!}
⟦⟧tyEq X (WeakTyEq dA=) dA dA' = {!!}

--  rewrite ⟦⟧tyEq X dA= [A] [A'] | ⟦⟧tyEq (toCtx (totalify (⟦ A' ⟧ty X) [A'])) dB= [B] [B'] = reflR

 --= --apP2-irr (PiStr X) (makeSetify (⟦⟧tyEq X dA= [A] [A'])) {!⟦⟧tyEq ? dB= [B] [B']!}
