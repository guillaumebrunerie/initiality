{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import typetheory
open import syntx
open import rules
open import contextualcat

module _ (sC : StructuredCCat) where

open StructuredCCat sC
open CCat ccat renaming (Mor to MorC; id to idC)

open import partialinterpretation sC

{- Totality of the partial interpretation functions -}

⟦⟧Tyᵈ  : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) → isDefined (⟦ A ⟧Ty (⟦ Γ ⟧Ctx $ Γᵈ))
⟦⟧Tmᵈ  : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → isDefined (⟦ u ⟧Tm (⟦ Γ ⟧Ctx $ Γᵈ))
⟦⟧Morᵈ : {Γ : Ctx n} {Δ : Ctx m} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (Δᵈ : isDefined (⟦ Δ ⟧Ctx)) {δ : Mor n m} (dδ : Γ ⊢ δ ∷> Δ) → isDefined (⟦ δ ⟧Mor (⟦ Γ ⟧Ctx $ Γᵈ) (⟦ Δ ⟧Ctx $ Δᵈ))


{- Interpretation of definitional equalities -}

⟦⟧TyEq : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A')) {Aᵈ : isDefined (⟦ A ⟧Ty X)} {A'ᵈ : isDefined (⟦ A' ⟧Ty X)}
        → ⟦ A ⟧Ty X $ Aᵈ ≡ ⟦ A' ⟧Ty X $ A'ᵈ
⟦⟧TmEq : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A)) {uᵈ : isDefined (⟦ u ⟧Tm X)} {u'ᵈ : isDefined (⟦ u' ⟧Tm X)}
        → ⟦ u ⟧Tm X $ uᵈ ≡ ⟦ u' ⟧Tm X $ u'ᵈ


{- Various lemmas saying that the interpretation functions are well-behaved -}

⟦⟧Tm₁ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {u : TmExpr n} {uᵈ : isDefined (⟦ u ⟧Tm X)} {A : TyExpr n} {Aᵈ : isDefined (⟦ A ⟧Ty X)} (du : Derivable (Γ ⊢ u :> A)) → ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ ⟦ A ⟧Ty X $ Aᵈ

⟦idMor⟧ᵈ : {X Y : Ob n} → Y ≡ X → isDefined (⟦ idMor n ⟧Mor X Y)
⟦idMor⟧= : {X Y : Ob n} (p : Y ≡ X) → ⟦ idMor n ⟧Mor X Y $ ⟦idMor⟧ᵈ p ≡ idC X

⟦weakenTy⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (A : TyExpr n)
            → isDefined (⟦ A ⟧Ty X)
            → (X= : ft X+ ≡ ft^ k X) {Y : Ob (suc n)} (Y= : Y ≡ star^ k X+ X X=)
            → isDefined (⟦ weakenTy' k A ⟧Ty Y)

⟦weakenTm⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (u : TmExpr n)
            → isDefined (⟦ u ⟧Tm X)
            → (X= : ft X+ ≡ ft^ k X) {Y : Ob (suc n)} (Y= : Y ≡ star^ k X+ X X=)
            → isDefined (⟦ weakenTm' k u ⟧Tm Y)

⟦weakenTy⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (A : TyExpr n)
             → (Aᵈ : isDefined (⟦ A ⟧Ty X))
             → (X= : ft X+ ≡ ft^ k X) {Y : Ob (suc n)} (Y= : Y ≡ star^ k X+ X X=)
             → star (qq^ k X=) (⟦ A ⟧Ty X $ Aᵈ) (qq^₁ ∙ ! (⟦⟧Ty-ft A)) ≡ ⟦ weakenTy' k A ⟧Ty Y $ ⟦weakenTy⟧ᵈ' k A Aᵈ X= Y=

⟦weakenTm⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ ft^ k X) {Y : Ob (suc n)} (Y= : Y ≡ star^ k X+ X X=)
            → starTm (qq^ k X=) (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u ∙ ! qq^₁) ≡ ⟦ weakenTm' k u ⟧Tm Y $ ⟦weakenTm⟧ᵈ' k u uᵈ X= Y=

⟦weakenTm⟧₁' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ ft^ k X) {Y : Ob (suc n)} (Y= : Y ≡ star^ k X+ X X=)
            → {Z : Ob (suc n)} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Z)
            → ∂₁ (⟦ weakenTm' k u ⟧Tm Y $ ⟦weakenTm⟧ᵈ' k u uᵈ X= Y=) ≡ star (qq^ k X=) Z (qq^₁ ∙ ! (⟦⟧Tm₁-ft u) ∙ ap ft u₁)


⟦weakenMor⟧ᵈ : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y : Ob m} (δ : Mor n m)
           → isDefined (⟦ δ ⟧Mor X Y)
           → isDefined (⟦ weakenMor δ ⟧Mor X+ Y)
           
⟦weakenMor⟧= : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y : Ob m} (δ : Mor n m)
           → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
           → ⟦ weakenMor δ ⟧Mor X+ Y $ ⟦weakenMor⟧ᵈ X= δ δᵈ ≡ comp (⟦ δ ⟧Mor X Y $ δᵈ) (pp X+) (pp₁ ∙ ! (⟦⟧Mor₀ δ ∙ ! X=))

⟦weakenMor+⟧ᵈ : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y+ : Ob (suc m)} {Y : Ob m} (Y= : ft Y+ ≡ Y) (δ : Mor n m)
           → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
           → (_ : star (⟦ δ ⟧Mor X Y $ δᵈ) Y+ (⟦⟧Mor₁ δ ∙ ! Y=) ≡ X+)
           → isDefined (⟦ weakenMor+ δ ⟧Mor X+ Y+)
⟦weakenMor+⟧= : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y+ : Ob (suc m)} {Y : Ob m} (Y= : ft Y+ ≡ Y) (δ : Mor n m)
           → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
           → (p : star (⟦ δ ⟧Mor X Y $ δᵈ) Y+ (⟦⟧Mor₁ δ ∙ ! Y=) ≡ X+)
           → ⟦ weakenMor+ δ ⟧Mor X+ Y+ $ ⟦weakenMor+⟧ᵈ X= Y= δ δᵈ p ≡ qq (⟦ δ ⟧Mor X Y $ δᵈ) Y+ (⟦⟧Mor₁ δ ∙ ! Y=)


{- Interpretation of total substitutions -}

⟦tsubst⟧Tyᵈ : {X : Ob n} {Y : Ob m} (A : TyExpr m)
            → isDefined (⟦ A ⟧Ty Y)
            → (δ : Mor n m)
            → isDefined (⟦ δ ⟧Mor X Y)
            → isDefined (⟦ A [ δ ]Ty ⟧Ty X)

⟦tsubst⟧Tmᵈ : {X : Ob n} {Y : Ob m} (u : TmExpr m)
            → isDefined (⟦ u ⟧Tm Y)
            → (δ : Mor n m)
            → isDefined (⟦ δ ⟧Mor X Y)
            → isDefined (⟦ u [ δ ]Tm ⟧Tm X)

⟦tsubst⟧Ty= : {X : Ob n} {Y : Ob m} (A : TyExpr m)
              (Aᵈ : isDefined (⟦ A ⟧Ty Y))
              (δ : Mor n m)
              (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            → star (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y $ Aᵈ) (⟦⟧Mor₁ δ ∙ ! (⟦⟧Ty-ft A))
              ≡ ⟦ A [ δ ]Ty ⟧Ty X $ ⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ

⟦tsubst⟧Tm= : {X : Ob n} {Y : Ob m} (u : TmExpr m)
              (uᵈ : isDefined (⟦ u ⟧Tm Y))
              (δ : Mor n m)
              (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
              → starTm (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ u ⟧Tm Y $ uᵈ) (⟦⟧Tm₀ u ∙ ! (⟦⟧Mor₁ δ))
                ≡ ⟦ u [ δ ]Tm ⟧Tm X $ ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ

⟦tsubst⟧Ty+= : {X+ : Ob (suc n)} {X : Ob n} {Y+ : Ob (suc m)} {Y : Ob m} (A : TyExpr (suc m))
               (Aᵈ : isDefined (⟦ A ⟧Ty Y+))
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (X= : ft X+ ≡ X)
               (Y= : ft Y+ ≡ Y)
               (p : star (⟦ δ ⟧Mor X Y $ δᵈ) Y+ (⟦⟧Mor₁ δ ∙ ! Y=) ≡ X+)
             → star+ (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y+ $ Aᵈ) (ap ft (⟦⟧Ty-ft A) ∙ ! (⟦⟧Mor₁ δ ∙ ! Y=))
               ≡ ⟦ A [ weakenMor+ δ ]Ty ⟧Ty X+ $ ⟦tsubst⟧Tyᵈ A Aᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ X= Y= δ δᵈ p)

⟦tsubst⟧Tm+= : {X+ : Ob (suc n)} {X : Ob n} {Y+ : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc m))
               (uᵈ : isDefined (⟦ u ⟧Tm Y+))
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (X= : ft X+ ≡ X)
               (Y= : ft Y+ ≡ Y)
               (p : star (⟦ δ ⟧Mor X Y $ δᵈ) Y+ (⟦⟧Mor₁ δ ∙ ! Y=) ≡ X+)
             → starTm+ (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ u ⟧Tm Y+ $ uᵈ) (ap ft (⟦⟧Tm₀ u) ∙ Y= ∙ ! (⟦⟧Mor₁ δ))
               ≡ ⟦ u [ weakenMor+ δ ]Tm ⟧Tm X+ $ ⟦tsubst⟧Tmᵈ u uᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ X= Y= δ δᵈ p)

⟦tsubst⟧Tm₁ : {X : Ob n} {Y : Ob m} (u : TmExpr m)
            (uᵈ : isDefined (⟦ u ⟧Tm Y))
            (δ : Mor n m)
            (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            {Z : Ob (suc m)}
            (u₁ : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ Z)
            → ∂₁ (⟦ u [ δ ]Tm ⟧Tm X $ ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ)
              ≡ star (⟦ δ ⟧Mor X Y $ δᵈ) Z (⟦⟧Mor₁ δ ∙ ! (⟦⟧Tm₁-ft u) ∙ ap ft u₁)


{- Interpretation of simple substitutions -}

⟦subst⟧Tyᵈ : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (B : TyExpr (suc n))
            → isDefined (⟦ B ⟧Ty X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm Y))
            → (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → isDefined (⟦ substTy B u ⟧Ty Y)

⟦subst⟧Tmᵈ : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (v : TmExpr (suc n))
            → isDefined (⟦ v ⟧Tm X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm Y))
            → (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → isDefined (⟦ substTm v u ⟧Tm Y)

⟦subst⟧Ty= : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (B : TyExpr (suc n))
             (Bᵈ : isDefined (⟦ B ⟧Ty X))
             (u : TmExpr n)
             (uᵈ : isDefined (⟦ u ⟧Tm Y))
             (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → ⟦ substTy B u ⟧Ty Y $ ⟦subst⟧Tyᵈ p B Bᵈ u uᵈ q ≡ star (⟦ u ⟧Tm Y $ uᵈ) (⟦ B ⟧Ty X $ Bᵈ) (q ∙ ! (⟦⟧Ty-ft B))

⟦subst⟧Tm= : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (v : TmExpr (suc n))
             (vᵈ : isDefined (⟦ v ⟧Tm X))
             (u : TmExpr n)
             (uᵈ : isDefined (⟦ u ⟧Tm Y))
             (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → ⟦ substTm v u ⟧Tm Y $ ⟦subst⟧Tmᵈ p v vᵈ u uᵈ q ≡ starTm (⟦ u ⟧Tm Y $ uᵈ) (⟦ v ⟧Tm X $ vᵈ) (⟦⟧Tm₀ v ∙ ! q)

⟦idMor+⟧ᵈ : {X : Ob n} {Y : Ob (suc n)} (p : ft Y ≡ X) (u : TmExpr n)
            (uᵈ : isDefined (⟦ u ⟧Tm X)) (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Y)
            → isDefined (⟦ idMor n , u ⟧Mor X Y)

⟦idMor+⟧= : {X : Ob n} {Y : Ob (suc n)} (p : ft Y ≡ X) (u : TmExpr n)
            (uᵈ : isDefined (⟦ u ⟧Tm X)) (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Y)
            → ⟦ idMor n , u ⟧Mor X Y $ ⟦idMor+⟧ᵈ p u uᵈ u₁ ≡ ⟦ u ⟧Tm X $ uᵈ

{- Auxiliary definitions -}

cong⟦⟧Ty : {X Y : Ob n} {A : TyExpr n} → X ≡ Y → isDefined (⟦ A ⟧Ty X) → isDefined (⟦ A ⟧Ty Y)
cong⟦⟧Ty refl Aᵈ = Aᵈ

cong⟦⟧Tm : {X Y : Ob n} {u : TmExpr n} → X ≡ Y → isDefined (⟦ u ⟧Tm X) → isDefined (⟦ u ⟧Tm Y)
cong⟦⟧Tm refl uᵈ = uᵈ

⟦weakenTy+⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc n))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
              → (X= : ft X+ ≡ ft^ k X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X=) X' (qq^₁ ∙ ! p) ≡ Y)
              → isDefined (⟦ weakenTy' (prev k) A ⟧Ty Y)
⟦weakenTy+⟧ᵈ' k A Aᵈ X= p Y= = ⟦weakenTy⟧ᵈ' (prev k) A Aᵈ (X= ∙ ap (ft^ k) (! p)) (! Y= ∙ ap2-irr star (qq^=p (! p)) refl)

⟦weakenTm+⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X= : ft X+ ≡ ft^ k X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X=) X' (qq^₁ ∙ ! p) ≡ Y)
              → isDefined (⟦ weakenTm' (prev k) u ⟧Tm Y)
⟦weakenTm+⟧ᵈ' k u uᵈ X= p Y= = ⟦weakenTm⟧ᵈ' (prev k) u uᵈ (X= ∙ ap (ft^ k) (! p)) (! Y= ∙ ap2-irr star (qq^=p (! p)) refl)

⟦weakenTy+⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc n))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
              → (X= : ft X+ ≡ ft^ k X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X=) X' (qq^₁ ∙ ! p) ≡ Y)
              → star+ (qq^ k X=) (⟦ A ⟧Ty X' $ Aᵈ) (ap ft (⟦⟧Ty-ft A) ∙ p ∙ ! qq^₁) ≡ ⟦ weakenTy' (prev k) A ⟧Ty Y $ ⟦weakenTy+⟧ᵈ' k A Aᵈ X= p Y=
⟦weakenTy+⟧=' k A Aᵈ X= p Y= = {!TODO!}

⟦weakenTm+⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X= : ft X+ ≡ ft^ k X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X=) X' (qq^₁ ∙ ! p) ≡ Y)
              → starTm+ (qq^ k X=) (⟦ u ⟧Tm X' $ uᵈ) (ap ft (⟦⟧Tm₀ u) ∙ p ∙ ! qq^₁) ≡ ⟦ weakenTm' (prev k) u ⟧Tm Y $ ⟦weakenTm+⟧ᵈ' k u uᵈ X= p Y=
⟦weakenTm+⟧=' k u uᵈ X= p Y= = {!TODO!}

⟦weakenTm+⟧₁' : (k : Fin (suc n)) {X+ : Ob (suc (suc n -F' (prev k)))} {X : Ob (suc n)} {X' : Ob n} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X))
              → (X= : ft X+ ≡ ft^ k X') {Y : Ob (suc (suc n))}
              → (p : ft X ≡ X')
              → (Y= : star (qq^ k X=) X (qq^₁ ∙ ! p) ≡ Y)
              → {Z : Ob (suc (suc n))} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Z)
              → ∂₁ (⟦ weakenTm' (prev k) u ⟧Tm Y $ ⟦weakenTm+⟧ᵈ' k u uᵈ X= p Y=) ≡ star (qq (qq^ k X=) (ft Z) (qq^₁ ∙ ! p ∙ ap ft (! (⟦⟧Tm₁-ft u) ∙ ap ft u₁) )) Z qq₁
⟦weakenTm+⟧₁' k u uᵈ X= p Y= u₁ = ⟦weakenTm⟧₁' (prev k) u uᵈ (X= ∙ ap (ft^ k) (! p)) (! (ap2-irr star (qq^=p p) refl ∙ Y=)) u₁ ∙ ap2-irr star (qq^prev ∙ ap2-irr qq (qq^=p p) (! (⟦⟧Tm₁-ft u) ∙ ap ft u₁)) refl

⟦weakenTy+⟧= : {X+ : Ob (suc n)} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc n))
             → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
             → (X= : ft X+ ≡ X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (pp X+) X' (pp₁ ∙ X= ∙ ! p) ≡ Y)
             → star (qq (pp X+) X' (pp₁ ∙ X= ∙ ! p)) (⟦ A ⟧Ty X' $ Aᵈ) (qq₁ ∙ ! (⟦⟧Ty-ft A)) ≡ ⟦ weakenTy' (prev last) A ⟧Ty Y $ ⟦weakenTy+⟧ᵈ' last A Aᵈ X= p (ap2-irr star qq^last refl ∙ Y=)
⟦weakenTy+⟧= A Aᵈ X= p Y= = ap2-irr star (ap2-irr qq (! qq^last) (! (⟦⟧Ty-ft A))) refl ∙ ⟦weakenTy+⟧=' last A Aᵈ X= p (ap2-irr star qq^last refl ∙ Y=)

⟦weakenTy⟧= : {X+ : Ob (suc n)} {X : Ob n} (A : TyExpr n)
            → (Aᵈ : isDefined (⟦ A ⟧Ty X))
            → (X= : ft X+ ≡ X) {Y : Ob (suc n)} (Y= : Y ≡ X+)
            → star (pp X+) (⟦ A ⟧Ty X $ Aᵈ) (pp₁ ∙ X= ∙ ! (⟦⟧Ty-ft A)) ≡ ⟦ weakenTy A ⟧Ty Y $ ⟦weakenTy⟧ᵈ' last A Aᵈ X= Y=
⟦weakenTy⟧= A Aᵈ X= Y= = {!TODO!}

⟦weakenTm⟧= : {X+ : Ob (suc n)} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ X) {Y : Ob (suc n)} (Y= : Y ≡ X+)
            → starTm (pp X+) (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u ∙ ! (pp₁ ∙ X=)) ≡ ⟦ weakenTm u ⟧Tm Y $ ⟦weakenTm⟧ᵈ' last u uᵈ X= Y=
⟦weakenTm⟧= u uᵈ X= Y= = {!TODO!}

{- Definitions -}

⟦⟧Tyᵈ Γᵈ UU = tt
⟦⟧Tyᵈ Γᵈ {A = el i v} (El dv) =
  (⟦⟧Tmᵈ Γᵈ dv ,
   ⟦⟧Tmₛ v ,
   (⟦⟧Tm₁ Γᵈ dv ∙ ap (UUStr i) (! (⟦⟧Tm₀ v))) , tt)
⟦⟧Tyᵈ Γᵈ {A = pi A B} (Pi dA dB) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA in
  (Aᵈ ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB , tt)
⟦⟧Tyᵈ Γᵈ {A = sig A B} (Sig dA dB) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA in
  (Aᵈ ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB , tt)
⟦⟧Tyᵈ Γᵈ Nat = tt
⟦⟧Tyᵈ Γᵈ {A = id A a b} (Id dA da db) =
  (⟦⟧Tyᵈ Γᵈ dA ,
   ⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da ,
   ⟦⟧Tmᵈ Γᵈ db ,
   ⟦⟧Tmₛ b ,
   ⟦⟧Tm₁ Γᵈ db , tt)

⟦⟧Tmᵈ Γᵈ (VarLast dA) = tt
⟦⟧Tmᵈ (Γᵈ , _) {u = var (prev x)} (VarPrev dA dx) = tt
⟦⟧Tmᵈ Γᵈ (Conv dA du dA=) = ⟦⟧Tmᵈ Γᵈ du

⟦⟧Tmᵈ Γᵈ {u = uu i} UUUU = tt

⟦⟧Tmᵈ Γᵈ {u = pi i a b} (PiUU da db) =
  let aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))
      bᵈ = ⟦⟧Tmᵈ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
  in
  (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)
⟦⟧Tmᵈ Γᵈ {u = lam A B u} (Lam dA dB du) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
  in
  (Aᵈ ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt ) dB ,
   ⟦⟧Tmᵈ (Γᵈ , Aᵈ , tt) du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ (Γᵈ , Aᵈ , tt) du , tt)
⟦⟧Tmᵈ Γᵈ {u = app A B f a} (App dA dB df da) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
  in
  (Aᵈ ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB ,
   ⟦⟧Tmᵈ Γᵈ df ,
   ⟦⟧Tmₛ f ,
   ⟦⟧Tm₁ Γᵈ df ,
   ⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   (⟦⟧Tm₁ Γᵈ da ∙ ! (⟦⟧Ty-ft B)) , tt)

⟦⟧Tmᵈ Γᵈ {u = sig i a b} (SigUU da db) =
  let aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))
      bᵈ = ⟦⟧Tmᵈ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
  in (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)
⟦⟧Tmᵈ Γᵈ {u = pair A B a b} (Pair dA dB da db) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
  in
  (Aᵈ ,
   Bᵈ ,
   aᵈ ,
   ⟦⟧Tmₛ a ,
   (⟦⟧Tm₁ Γᵈ da ∙ ! (⟦⟧Ty-ft B)) ,
   ⟦⟧Tmᵈ Γᵈ db ,
   ⟦⟧Tmₛ b ,
   (⟦⟧Tm₁ Γᵈ db ∙ ⟦subst⟧Ty= (⟦⟧Ty-ft A) B Bᵈ a aᵈ (⟦⟧Tm₁ Γᵈ da)) , tt)
⟦⟧Tmᵈ Γᵈ {u = pr1 A B u} (Pr1 dA dB du) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA in
  (Aᵈ ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ du , tt)
⟦⟧Tmᵈ Γᵈ {u = pr2 A B u} (Pr2 dA dB du) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA in
  (Aᵈ ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ du , tt)

⟦⟧Tmᵈ Γᵈ {u = nat i} NatUU = tt
⟦⟧Tmᵈ Γᵈ {u = zero} Zero = tt
⟦⟧Tmᵈ Γᵈ {u = suc u} (Suc du) =
  (⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   (⟦⟧Tm₁ Γᵈ du ∙ ap NatStr (! (⟦⟧Tm₀ u))) , tt)
⟦⟧Tmᵈ Γᵈ {u = natelim P dO dS u} (Natelim dP ddO ddS du) =
  let Pᵈ  = ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP
      P=  = ⟦⟧Ty-ft P
      dOᵈ = ⟦⟧Tmᵈ Γᵈ ddO
      dOₛ = ⟦⟧Tmₛ dO
      dO₁ = ⟦⟧Tm₁ Γᵈ ddO
            ∙ ⟦subst⟧Ty= NatStr= P Pᵈ zero tt zeroStr₁
      dSᵈ = ⟦⟧Tmᵈ ((Γᵈ , (tt , tt)) , Pᵈ , tt) ddS
      dSₛ = ⟦⟧Tmₛ dS
      natthing = NatStrNat _ (! (pp₁ ∙ NatStr=)) ∙ ap NatStr (pp₀ ∙ ! (varC₀ last _))
      auxauxᵈ = ⟦weakenTy⟧ᵈ' (prev last) P Pᵈ refl (! natthing ∙ ap2-irr star (! qq^last) refl)
      auxᵈ = ⟦subst⟧Tyᵈ (NatStr= ∙ varC₀ last _) (weakenTy' (prev last) P) auxauxᵈ (suc (var last)) (tt , (ssₛ , (varCL₁ _ ∙ natthing) , tt)) sucStr₁
      dS₁ = ⟦⟧Tm₁ ((Γᵈ , (tt , tt)) , Pᵈ , tt) ddS
            ∙ ! (⟦weakenTy⟧= (substTy (weakenTy' (prev last) P) (suc (var last))) auxᵈ (⟦⟧Ty-ft P) refl)
            ∙ ap2-irr star refl (⟦subst⟧Ty= (NatStr= ∙ varC₀ last _) (weakenTy' (prev last) P) auxauxᵈ (suc (var last)) (tt , (ssₛ , (varCL₁ _ ∙ natthing) , tt)) sucStr₁
              ∙ ap2-irr star refl (! (⟦weakenTy+⟧= P Pᵈ NatStr= NatStr= natthing)))
      uᵈ  = ⟦⟧Tmᵈ Γᵈ du
      uₛ  = ⟦⟧Tmₛ u
      u₁  = ⟦⟧Tm₁ Γᵈ du ∙ ! (⟦⟧Ty-ft P)
  in (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt)

⟦⟧Tmᵈ Γᵈ {u = id i a u v} (IdUU da du dv) =
  (⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   (⟦⟧Tm₁ Γᵈ da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))) ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ {A = el i a} {Aᵈ = ⟦⟧Tmᵈ Γᵈ da , ⟦⟧Tmₛ a , (⟦⟧Tm₁ Γᵈ da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))) , tt} du ,
   ⟦⟧Tmᵈ Γᵈ dv ,
   ⟦⟧Tmₛ v ,
   ⟦⟧Tm₁ Γᵈ {A = el i a} {Aᵈ = ⟦⟧Tmᵈ Γᵈ da , ⟦⟧Tmₛ a , (⟦⟧Tm₁ Γᵈ da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))) , tt} dv , tt)
⟦⟧Tmᵈ Γᵈ {u = refl A a} (Refl dA da) =
  (⟦⟧Tyᵈ Γᵈ dA ,
   ⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da , tt)
⟦⟧Tmᵈ Γᵈ {u = jj A P d a b p} (JJ dA dP dd da db dp) = {!TODO!}
--   let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
--       Pᵈ = {!⟦⟧Tyᵈ ? dP!}
--       P= = {!!}
--       dᵈ = ⟦⟧Tmᵈ (Γᵈ , Aᵈ , tt) dd
--       dₛ = ⟦⟧Tmₛ d
--       d₁ = {!⟦⟧Tm₁ (respectsCtxExt r A) {Aᵈ = ⟦tsubst⟧Tyᵈ P Pᵈ (((weakenMor' last (idMor _) , var last) , var last) , refl (weakenTy' last A) (var last)) {!!}} dd
--      ∙ {!! (⟦tsubst⟧Ty= P Pᵈ ((idMor _ , var last) , refl (weakenTy A) (var last)) {!!}) ∙ {!ap2-irr star (ap2-irr comp (ap2-irr qq (⟦idMor+⟧= (ap ft (IdStr= ∙ ft-star ∙ pp₀ ∙ AA=) ∙ ⟦⟧Ty-ft (weakenTy A)) (var last) tt  {!ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl ∙ ! (IdStr= ∙ ft-star ∙ pp₀)!}) refl) (ap-irr-reflStr (! AA=) refl)) refl!}!}!}
--       aᵈ = ⟦⟧Tmᵈ Γᵈ da
--       aₛ = ⟦⟧Tmₛ a
--       a₁ = ⟦⟧Tm₁ Γᵈ da
--       bᵈ = ⟦⟧Tmᵈ Γᵈ db
--       bₛ = ⟦⟧Tmₛ b
--       b₁ = ⟦⟧Tm₁ Γᵈ db
--       pᵈ = ⟦⟧Tmᵈ Γᵈ dp
--       pₛ = ⟦⟧Tmₛ p
--       p₁ = ⟦⟧Tm₁ Γᵈ dp
--   in (Aᵈ , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt)

--      abstract
--       Aᵈ : isDefined (⟦ A ⟧Ty X)
--       Aᵈ = ⟦⟧Tyᵈ r dA

--       AAᵈ : isDefined (⟦ weakenTy A ⟧Ty (⟦ A ⟧Ty X $ Aᵈ))
--       AAᵈ = ⟦weakenTy⟧ᵈ' last A Aᵈ (⟦⟧Ty-ft A) refl

--       AA= : star (pp (⟦ A ⟧Ty X $ Aᵈ)) (⟦ A ⟧Ty X $ Aᵈ) pp₁ ≡ ⟦ weakenTy A ⟧Ty (⟦ A ⟧Ty X $ Aᵈ) $ AAᵈ
--       AA= = ⟦weakenTy⟧= A Aᵈ (⟦⟧Ty-ft A) refl

--       AAAᵈ : isDefined (⟦ weakenTy (weakenTy A) ⟧Ty (⟦ weakenTy A ⟧Ty (⟦ A ⟧Ty X $ Aᵈ) $ AAᵈ))
--       AAAᵈ = ⟦weakenTy⟧ᵈ' last (weakenTy A) AAᵈ (⟦⟧Ty-ft (weakenTy A)) refl

--       AAA= : _ ≡ ⟦ weakenTy (weakenTy A) ⟧Ty (⟦ weakenTy A ⟧Ty (⟦ A ⟧Ty X $ Aᵈ) $ AAᵈ) $ AAAᵈ
--       AAA= = ⟦weakenTy⟧= (weakenTy A) AAᵈ (⟦⟧Ty-ft (weakenTy A)) refl

--       AAidᵈ : isDefined (⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty (⟦ weakenTy A ⟧Ty (⟦ A ⟧Ty X $ Aᵈ) $ AAᵈ))
--       AAidᵈ = (AAAᵈ ,
--                tt ,
--                ssₛ ,
--                {!(ss₁' (comp₁ ∙ ss₁' (id₁ ∙ ⟦⟧Ty-ft (weakenTy A)) ∙ ap2-irr star (id-left' (pp₀ ∙ ! (⟦⟧Ty-ft (weakenTy A)))) refl ∙ AA=) ∙ ap2-irr star (! (assoc {q = ss-id₁ ∙ ap2-irr star (ap pp (⟦⟧Ty-ft (weakenTy A))) (⟦⟧Ty-ft (weakenTy A)) ∙ AA= ∙ ! pp₀}) ∙ ap2-irr comp (ap2-irr comp (ap pp (! AA= ∙ ap2-irr star (! (id-left' (pp₀ ∙ id₁) ∙ ap pp id₁)) (! id₁))) (ap ss (ap idC (⟦⟧Ty-ft (weakenTy A)))) ∙ ss-pp) refl ∙ id-right' (pp₁ ∙ ⟦⟧Ty-ft (weakenTy A) ∙ ! id₀)) refl ∙ AAA=)!} ,
--                tt ,
--                ssₛ ,
--                (ss-id₁ ∙ AAA=) , tt)

--       Pᵈ' : isDefined (⟦ P ⟧Ty (⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty (⟦ weakenTy A ⟧Ty (⟦ A ⟧Ty X $ Aᵈ) $ AAᵈ) $ AAidᵈ))
--       Pᵈ' = ⟦⟧Tyᵈ {Γ = ((Γ , A) , weakenTy A) , id (weakenTy (weakenTy A)) (var (prev last)) (var last)} (respectsCtxExt {Γ = (Γ , A) , weakenTy A} (respectsCtxExt {Γ = Γ , A} (respectsCtxExt {Γ = Γ} r A {Aᵈ = Aᵈ}) (weakenTy A) {Aᵈ = AAᵈ}) (id (weakenTy (weakenTy A)) (var (prev last)) (var last)) {Aᵈ = AAidᵈ}) {A = P} dP

--       Pᵈ : isDefined (⟦ P ⟧Ty (IdStr (star (pp (star (pp (⟦ A ⟧Ty X $ Aᵈ)) (⟦ A ⟧Ty X $ Aᵈ) pp₁)) (star (pp (⟦ A ⟧Ty X $ Aᵈ)) (⟦ A ⟧Ty X $ ⟦⟧Tyᵈ r dA) pp₁) pp₁) (ss (pp (star (pp (⟦ A ⟧Ty X $ Aᵈ)) (⟦ A ⟧Ty X $ Aᵈ) pp₁))) ssₛ (ss₁' (pp₁ ∙ ft-star ∙ pp₀) ∙ star-comp pp₁) (ss (idC (star (pp (⟦ A ⟧Ty X $ Aᵈ)) (⟦ A ⟧Ty X $ Aᵈ) pp₁))) ssₛ ss-id₁))
--       Pᵈ = cong⟦⟧Ty {A = P} (ap-irr-IdStr (! (ap2-irr star (ap pp AA=) AA= ∙ AAA=)) (ap ss (ap pp (! AA=))) (ap ss (ap idC (! AA=)))) Pᵈ'


⟦⟧Morᵈ {Δ = ◇} _ _ {◇} tt = tt
⟦⟧Morᵈ {Δ = Δ , B} Γᵈ (Δᵈ , Bᵈ , tt) {δ , u} (dδ , du) =
  let δᵈ' = ⟦⟧Morᵈ Γᵈ Δᵈ dδ
      δᵈ = {!TODO (some weird transport)!}
      uᵈ = ⟦⟧Tmᵈ Γᵈ du
      δ₁ = ⟦⟧Mor₁ δ
      u₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = ⟦tsubst⟧Tyᵈ B Bᵈ δ δᵈ'} du ∙ ! (⟦tsubst⟧Ty= B Bᵈ δ δᵈ') ∙ ap2-irr star (ap-irr (λ x z → ⟦ δ ⟧Mor _ x $ z) (! (⟦⟧Ty-ft B))) refl
  in (δᵈ , uᵈ , δ₁ , u₁ , tt)

⟦⟧Tm₁ {Γ = Γ , _} (Γᵈ , Aᵈ , tt) (VarLast {A = A} dA) = varCL₁ (⟦ A ⟧Ty (⟦ Γ ⟧Ctx $ Γᵈ) $ Aᵈ) ∙ ⟦weakenTy⟧= A Aᵈ (⟦⟧Ty-ft A) refl
⟦⟧Tm₁ {Γ = Γ , _} (Γᵈ , Bᵈ , tt) {u = var (prev k)} (VarPrev {B = B} {A = A} dA dk) = (varC+₁ k (⟦ B ⟧Ty (⟦ Γ ⟧Ctx $ Γᵈ) $ Bᵈ) (⟦⟧Ty-ft B) (⟦⟧Tm₁-ft (var k)) ∙ ap2-irr star refl (⟦⟧Tm₁ Γᵈ dk)) ∙ ⟦weakenTy⟧= A (⟦⟧Tyᵈ Γᵈ dA) (⟦⟧Ty-ft B) refl
⟦⟧Tm₁ Γᵈ (Conv dA du dA=) = ⟦⟧Tm₁ Γᵈ du ∙ ⟦⟧TyEq Γᵈ dA= {Aᵈ = ⟦⟧Tyᵈ Γᵈ dA}

⟦⟧Tm₁ Γᵈ {u = uu i} UUUU = uuStr₁

⟦⟧Tm₁ Γᵈ {u = pi i a b} (PiUU da db) = piStr₁ ∙ ap (UUStr i) (⟦⟧Tm₀ a)
⟦⟧Tm₁ Γᵈ {u = lam A B u} (Lam dA dB du) = lamStr₁
⟦⟧Tm₁ Γᵈ {u = app A B f a} (App dA dB df da) = appStr₁ ∙ ! (⟦subst⟧Ty= (⟦⟧Ty-ft A) B (⟦⟧Tyᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))

⟦⟧Tm₁ Γᵈ {u = sig i a b} (SigUU da db) = sigStr₁ ∙ ap (UUStr i) (⟦⟧Tm₀ a)
⟦⟧Tm₁ Γᵈ {u = pair A B a b} (Pair dA dB da db) = pairStr₁
⟦⟧Tm₁ Γᵈ {u = pr1 A B u} (Pr1 dA dB du) = pr1Str₁ ∙ ⟦⟧Ty-ft B
⟦⟧Tm₁ Γᵈ {u = pr2 A B u} (Pr2 dA dB du) = pr2Str₁ ∙ ! (⟦subst⟧Ty= (⟦⟧Ty-ft A) B (⟦⟧Tyᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB) (pr1 A B u) (⟦⟧Tyᵈ Γᵈ dA , ⟦⟧Tyᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB , ⟦⟧Tmᵈ Γᵈ du , ⟦⟧Tmₛ u , ⟦⟧Tm₁ Γᵈ du , tt) (pr1Str₁ ∙ ⟦⟧Ty-ft B))

⟦⟧Tm₁ Γᵈ {u = nat i} NatUU = natStr₁
⟦⟧Tm₁ Γᵈ {u = zero} Zero = zeroStr₁
⟦⟧Tm₁ Γᵈ {u = suc u} (Suc du) = sucStr₁ ∙ ap NatStr (⟦⟧Tm₀ u)
⟦⟧Tm₁ Γᵈ {u = natelim P dO dS u} (Natelim dP ddO ddS du) = natelimStr₁ ∙ ! (⟦subst⟧Ty= NatStr= P (⟦⟧Tyᵈ (Γᵈ , tt , tt) dP) u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ du))

⟦⟧Tm₁ Γᵈ {u = id i a u v} (IdUU da du dv) = idStr₁ ∙ ap (UUStr i) (⟦⟧Tm₀ a)
⟦⟧Tm₁ Γᵈ {u = refl A a} (Refl dA da) = reflStr₁
⟦⟧Tm₁ Γᵈ {u = jj A P d a b p} (JJ dA dP dd da db dp) = {!!}

⟦idMor⟧ᵈ {zero} refl = tt
⟦idMor⟧ᵈ {suc n} {Y = Y} refl = ⟦weakenMor+⟧ᵈ refl refl (idMor n) (⟦idMor⟧ᵈ {n = n} refl) (ap2-irr star (⟦idMor⟧= refl) refl ∙ star-id)

⟦idMor⟧= {zero} refl = ! (ptmor-unique _ (idC _) id₀ (id₁ ∙ pt-unique _))
⟦idMor⟧= {suc n} {Y = Y} refl = ⟦weakenMor+⟧= {X = ft Y} refl {Y+ = Y} refl (idMor n) (⟦idMor⟧ᵈ{n = n} refl) (ap2-irr star (⟦idMor⟧= refl) refl ∙ star-id) ∙ ap2-irr qq (⟦idMor⟧= refl) refl ∙ qq-id


⟦weakenTy⟧ᵈ' k (uu i) Aᵈ _ _ = tt
⟦weakenTy⟧ᵈ' k (el i v) (vᵈ , vₛ , v₁ , tt) X= Y= =
  (⟦weakenTm⟧ᵈ' k v vᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weakenTm⟧₁' k v vᵈ X= Y= v₁ ∙ UUStrNat _ (⟦⟧Tm₀ v ∙ ! qq^₁) ∙ ap (UUStr i) (qq^₀ ∙ ! Y= ∙ ! (⟦⟧Tm₀ (weakenTm' k v)))) , tt)
⟦weakenTy⟧ᵈ' k (pi A B) (Aᵈ , Bᵈ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=) , tt)
⟦weakenTy⟧ᵈ' k (sig A B) (Aᵈ , Bᵈ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=) , tt)
⟦weakenTy⟧ᵈ' k nat Aᵈ _ _ = tt
⟦weakenTy⟧ᵈ' k (id A u v) (Aᵈ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X= Y= u₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X= Y=) ,
   ⟦weakenTm⟧ᵈ' k v vᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weakenTm⟧₁' k v vᵈ X= Y= v₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X= Y=) , tt)

⟦weakenTm⟧ᵈ' k (var x) tt X= Y= = tt

⟦weakenTm⟧ᵈ' k (uu i) tt X= Y= = tt

⟦weakenTm⟧ᵈ' k (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X= Y= =
  (⟦weakenTm⟧ᵈ' k a aᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X= Y= a₁ ∙ UUStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! qq^₁) ∙ ap (UUStr i) (qq^₀ ∙ ! (⟦⟧Tm₀ (weakenTm' k a) ∙ Y=))) ,
   ⟦weakenTm+⟧ᵈ' k b bᵈ X= (ElStr= ∙ ⟦⟧Tm₀ a) (ElStrNat _ (⟦⟧Tm₀ a ∙ ! qq^₁) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) b) ,
   (⟦weakenTm+⟧₁' k b bᵈ X= (ElStr= ∙ ⟦⟧Tm₀ a) (ElStrNat _ (⟦⟧Tm₀ a ∙ ! qq^₁) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)) b₁ ∙ UUStrNat _ (! UUStr= ∙ ! qq₁) ∙ ap (UUStr i) (qq₀ ∙ ap2-irr star refl UUStr= ∙ ElStrNat _ (⟦⟧Tm₀ a ∙ ! qq^₁) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=))) , tt)
⟦weakenTm⟧ᵈ' k (lam A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy⟧ᵈ' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=p (! (⟦⟧Ty-ft A))) refl) ,
   ⟦weakenTm+⟧ᵈ' k u uᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) u) ,
   (⟦weakenTm+⟧₁' k u uᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=) u₁ ∙ ⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=)) , tt)
⟦weakenTm⟧ᵈ' k (app A B f a) (Aᵈ , Bᵈ , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=) ,
   ⟦weakenTm⟧ᵈ' k f fᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k f) ,
   (⟦weakenTm⟧₁' k f fᵈ X= Y= f₁ ∙ PiStrNat _ (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! qq^₁) ∙ ap PiStr (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=))) ,
   ⟦weakenTm⟧ᵈ' k a aᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X= Y= a₁ ∙ ! qq₀ ∙ ! ft-star ∙ ap ft (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=))) , tt)

⟦weakenTm⟧ᵈ' k (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X= Y= =
  (⟦weakenTm⟧ᵈ' k a aᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X= Y= a₁ ∙ UUStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! qq^₁) ∙ ap (UUStr i) (qq^₀ ∙ ! (⟦⟧Tm₀ (weakenTm' k a) ∙ Y=))) ,
   ⟦weakenTm+⟧ᵈ' k b bᵈ X= (ElStr= ∙ ⟦⟧Tm₀ a) (ElStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! qq^₁) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) b) ,
   (⟦weakenTm+⟧₁' k b bᵈ X= (ElStr= ∙ ⟦⟧Tm₀ a) (ElStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! qq^₁) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)) b₁ ∙ UUStrNat (qq (qq^ k X=) _ (qq^₁ ∙ ! (ap ft UUStr= ∙ ElStr= ∙ ⟦⟧Tm₀ a))) (! UUStr= ∙ ! qq₁) ∙ ap (UUStr i) (qq₀ ∙ ap2-irr star refl UUStr= ∙ ElStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! qq^₁) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=))) , tt)
⟦weakenTm⟧ᵈ' k (pair A B a b) (Aᵈ , Bᵈ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=) ,
   ⟦weakenTm⟧ᵈ' k a aᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X= Y= (a₁ ∙ ⟦⟧Ty-ft B) ∙ ⟦weakenTy⟧=' k A Aᵈ X= Y= ∙ ! (⟦⟧Ty-ft (weakenTy' (prev k) B))) ,
   ⟦weakenTm⟧ᵈ' k b bᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k b) ,
   (⟦weakenTm⟧₁' k b bᵈ X= Y= b₁ ∙ starstar (⟦⟧Tmₛ a) (⟦⟧Tm₀ a ∙ ! qq^₁) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! qq^₁) refl ∙ ap2-irr star (⟦weakenTm⟧=' k a aᵈ X= Y=) (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=))) , tt)
⟦weakenTm⟧ᵈ' k (pr1 A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X= Y= u₁ ∙ SigStrNat _ (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! qq^₁) ∙ ap SigStr (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=))) , tt)
⟦weakenTm⟧ᵈ' k (pr2 A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X= Y= u₁ ∙ SigStrNat _ (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! qq^₁) ∙ ap SigStr (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=))) , tt)

⟦weakenTm⟧ᵈ' k (nat i) tt X= Y= = tt
⟦weakenTm⟧ᵈ' k zero tt X= Y= = tt
⟦weakenTm⟧ᵈ' k (suc u) (uᵈ , uₛ , u₁ , tt) X= Y= =
  (⟦weakenTm⟧ᵈ' k u uᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X= Y= u₁ ∙ NatStrNat _ (⟦⟧Tm₀ u ∙ ! qq^₁) ∙ ap NatStr (qq^₀ ∙ ! Y= ∙ ! (⟦⟧Tm₀ (weakenTm' k u)))) , tt)

⟦weakenTm⟧ᵈ' k (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) X= Y= = {!TODO!}
--   (a1 ,
--    a2 ,
--    a3 ,
--    a4 ,
--    a5 ,
--    a6 ,
--    a7 ,
--    a8 ,
--    a9 ,
--    a10 ,
--    a11 , tt)  where
  
--     abstract
--       naturalityNat : star^ (prev k) _ (NatStr _) (X= ∙ ap (ft^ k) (! NatStr=)) ≡
--                         NatStr (star^ k _ _ X=)
--       naturalityNat = ap2-irr star (qq^=p NatStr=) refl ∙ NatStrNat _ (! (qq^₁ k X=)) ∙ ap NatStr (qq^₀ k X=)

--       wP= : _
--       wP= = ⟦weakenTy+⟧=' k P Pᵈ (X= ∙ ap (ft^ k) (! NatStr=)) refl (! naturalityNat)

--       a1 : isDefined (⟦ weakenTy' (prev k) P ⟧Ty (NatStr (star^ k _ _ X=)))
--       a1 = ⟦weakenTy⟧ᵈ' (prev k) P Pᵈ (X= ∙ ap (ft^ k) (! NatStr=)) (! naturalityNat)

--       a2 : ft (⟦ weakenTy' (prev k) P ⟧Ty (NatStr (star^ k _ _ X=)) $ a1) ≡ NatStr (star^ k _ _ X=)
--       a2 = ⟦⟧Ty-ft (weakenTy' (prev k) P)

--       a3 : isDefined (⟦ weakenTm' k dO ⟧Tm (star^ k _ _ X=))
--       a3 = ⟦weakenTm⟧ᵈ' k dO dOᵈ X= refl

--       a4 : is-section (⟦ weakenTm' k dO ⟧Tm (star^ k _ _ X=) $ a3)
--       a4 = ⟦⟧Tmₛ (weakenTm' k dO)

--       a5 : ∂₁ (⟦ weakenTm' k dO ⟧Tm (star^ k _ _ X=) $ a3) ≡ _
--       a5 = ⟦weakenTm⟧₁' k dO dOᵈ X= refl dO₁ ∙ starstar zeroStrₛ (zeroStr₀ _ ∙ ! (qq^₁ k X=)) (ap ft (⟦⟧Ty-ft P) ∙ NatStr= ∙ ! (qq^₁ k X=)) (⟦⟧Ty-ft P) ∙ ap2-irr star (zeroStrNat _ (! (qq^₁ k X=)) ∙ ap zeroStr (qq^₀ k X=)) {!! wP=!}

--       a6 : isDefined
--              (⟦ weakenTm' (prev (prev k)) dS ⟧Tm
--               (⟦ weakenTy' (prev k) P ⟧Ty (NatStr (star^ k _ _ X=)) $ a1))
--       a6 = ⟦weakenTm⟧ᵈ'prev (prev k) dS dSᵈ (X= ∙ ap (ft^ k) (! (ap ft (⟦⟧Ty-ft P) ∙ NatStr=))) refl {!wP=!}
-- -- {!ap2-irr star (ap2-irr qq (qq^=p NatStr= ∙ ! (qq^=p (ap ft (⟦⟧Ty-ft P) ∙ NatStr=))) (! (⟦⟧Ty-ft P))) refl!}
--       a7 : is-section (⟦ weakenTm' (prev (prev k)) dS ⟧Tm
--               (⟦ weakenTy' (prev k) P ⟧Ty (NatStr (star^ k _ _ X=)) $ a1) $ a6)
--       a7 = ⟦⟧Tmₛ (weakenTm' (prev (prev k)) dS)

--       a8 : ∂₁ (⟦ weakenTm' (prev (prev k)) dS ⟧Tm
--               (⟦ weakenTy' (prev k) P ⟧Ty (NatStr (star^ k _ _ X=)) $ a1) $ a6) ≡ _
--       a8 = ⟦weakenTm⟧₁' (prev (prev k)) dS dSᵈ (X= ∙ ap (ft^ k) (! (ap ft (⟦⟧Ty-ft P) ∙ NatStr=))) (! wP= ∙ ! (ap2-irr star (qq^=p (⟦⟧Ty-ft P)) refl)) dS₁
--            ∙ ap2-irr star qq^prev refl ∙ star-pp {!!} {!!}
--            ∙ ap2-irr star (ap pp (ap2-irr star qq^prev refl)) (ap2-irr star qq^prev refl) ∙ ap2-irr star {!!} (starstar {!!} {!!} {!!} {!!}
--            ∙ ap2-irr star {!!} {!!})
--       {-
-- ⟦weakenTm⟧₁' (prev (prev k)) dS dSᵈ (X= ∙ ap (ft^ k) (! (ap ft (⟦⟧Ty-ft P) ∙ NatStr=))) (! wP= ∙ ! (ap2-irr star (qq^=p (⟦⟧Ty-ft P)) refl)) dS₁
--            ∙ starqq^-pp _ _ (! id₀ ∙ ! ss₀ ∙ ! (sucStr₀ _) ∙ ! ft-star)
--            ∙ ap2-irr star (ap pp (ap2-irr star (qq^=p (⟦⟧Ty-ft P)) refl ∙ wP=))
--              (starqq^-term _ _ _ sucStrₛ (sucStr₀ _ ∙ ss₀ ∙ id₀) _
--              ∙ ap2-irr star (sucStrNat _ (ss₀ ∙ id₀ ∙ ! qq^₁) ∙ ap-irr2 sucStr (starqq^-ssid _ _ ∙ ap ss (ap idC (star^=p (! (⟦⟧Ty-ft P)) ∙ ! qq^₀ ∙ ! ft-star ∙ ap ft wP=))))
--                (ap2-irr star (qq^=p (ft-star ∙ qq₀)) refl ∙ starqq^-qqpp k (X= ∙ ap (ft^ k) (! NatStr=)) refl (⟦⟧Ty-ft P) ∙ ap2-irr star (ap2-irr qq (ap pp naturalityNat) naturalityNat) (ap2-irr star (qq^=p (⟦⟧Ty-ft P)) refl ∙ wP=)))
-- -}

--       a9 : isDefined (⟦ weakenTm' k u ⟧Tm (star^ k _ _ X=))
--       a9 = ⟦weakenTm⟧ᵈ' k u uᵈ X= refl

--       a10 : is-section (⟦ weakenTm' k u ⟧Tm (star^ k _ _ X=) $ a9) 
--       a10 = ⟦⟧Tmₛ (weakenTm' k u)

--       a11 : ∂₁ (⟦ weakenTm' k u ⟧Tm (star^ k _ _ X=) $ a9) ≡ _
--       a11 = ⟦weakenTm⟧₁' k u uᵈ X= refl u₁ ∙ ap-irr (star _) (⟦⟧Ty-ft P) ∙ NatStrNat _ (! (qq^₁ k X=)) ∙ ap NatStr (qq^₀ k X=) ∙ ! (⟦⟧Ty-ft (weakenTy' (prev k) P))

⟦weakenTm⟧ᵈ' k (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X= Y= =
  (⟦weakenTm⟧ᵈ' k a aᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X= Y= a₁ ∙ UUStrNat _ (⟦⟧Tm₀ a ∙ ! qq^₁) ∙ ap (UUStr i) (qq^₀ ∙ ! Y= ∙ ! (⟦⟧Tm₀ (weakenTm' k a)))) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X= Y= u₁ ∙ ElStrNat _ (⟦⟧Tm₀ a ∙ ! qq^₁) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)) ,
   ⟦weakenTm⟧ᵈ' k v vᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weakenTm⟧₁' k v vᵈ X= Y= v₁ ∙ ElStrNat _ (⟦⟧Tm₀ a ∙ ! qq^₁) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)) , tt)
⟦weakenTm⟧ᵈ' k (refl A u) (Aᵈ , uᵈ , uₛ , u₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X= Y= u₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X= Y=) , tt)
⟦weakenTm⟧ᵈ' k (jj A P d a b p) uᵈ X= Y= =
  {!!}

⟦weakenTy⟧=' k (uu i) _ X= Y= =
  UUStrNat _ (! qq^₁)
  ∙ ap (UUStr i) (qq^₀ ∙ ! Y=)
⟦weakenTy⟧=' k (el i v) (vᵈ , vₛ , v₁ , tt) X= Y= =
  ElStrNat _ (⟦⟧Tm₀ v ∙ ! qq^₁)
  ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k v vᵈ X= Y=)
⟦weakenTy⟧=' k (pi A B) (Aᵈ , Bᵈ , tt) X= Y= =
  PiStrNat _ (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! qq^₁)
  ∙ ap PiStr (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=))
⟦weakenTy⟧=' k (sig A B) (Aᵈ , Bᵈ , tt) X= Y= =
  SigStrNat _ (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! qq^₁)
  ∙ ap SigStr (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=))
⟦weakenTy⟧=' k nat _ X= Y= =
  NatStrNat _ (! qq^₁)
  ∙ ap NatStr (qq^₀ ∙ ! Y=)
⟦weakenTy⟧=' k (id A u v) (Aᵈ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X= Y= =
  IdStrNat _ (⟦⟧Ty-ft A ∙ ! qq^₁)
  ∙ ap-irr-IdStr (⟦weakenTy⟧=' k A Aᵈ X= Y=) (⟦weakenTm⟧=' k u uᵈ X= Y=) (⟦weakenTm⟧=' k v vᵈ X= Y=)


-- ⟦weakenTm⟧=' last (var last) tt X= refl = ! (ap ss (ap2-irr comp (ap ss (ap idC X=)) refl))
-- ⟦weakenTm⟧=' (prev k) (var last) tt X= refl = ! (ss-comp {f₁ = id₁} ∙ ap ss (ap2-irr comp refl (ap idC (! qq₀)) ∙ id-left) ∙ ! (ss-comp {f₁ = comp₁ ∙ ss₁} ∙ ap ss (! assoc) ∙ ap ss (ap2-irr comp (! ss-qq ∙ ap idC (! qq₁)) refl) ∙ ap ss (id-right)))
-- ⟦weakenTm⟧=' last (var (prev x)) (xᵈ , x₀ , tt) X= refl = ! (ap ss (ap2-irr comp (ap ss (ap2-irr comp (ap-irr (λ z p → ⟦ var x ⟧Tm z $ p) (ap ft X=)) (ap pp X=))) refl))
-- ⟦weakenTm⟧=' (prev k) (var (prev x)) (xᵈ , x₀ , tt) X= refl = ! (ap ss (ap2-irr comp (ap-irr (λ z p → ⟦ var (weakenVar' k x) ⟧Tm z $ p) (ft-star ∙ qq^₀ k X=) ∙ ! (⟦weakenTm⟧=' k (var x) xᵈ X= refl)) refl {b' = pp₁ ∙ ft-star ∙ ! (ss₀ ∙ comp₀)}) ∙ ss-comp {f₁ = comp₁ ∙ ss₁} ∙ ap ss (! assoc) ∙ ap ss (ap2-irr comp (! ss-qq) refl) ∙ ap ss assoc ∙ ! (ss-comp {f₁ = comp₁ ∙ ss₁}∙ ap ss (! assoc) ∙ ap ss (ap2-irr comp (! ss-qq) refl) ∙ ap ss assoc ∙ ap ss (ap2-irr comp refl pp-qq)))
⟦weakenTm⟧=' last (var x) tt X= Y= = {!TODO(var)!}
⟦weakenTm⟧=' (prev k) (var x) tt X= Y= = {!TODO(var)!}

⟦weakenTm⟧=' k (uu i) tt X= Y= =
  uuStrNat _ (! qq^₁)
  ∙ ap (uuStr i) (qq^₀ ∙ ! Y=)

⟦weakenTm⟧=' k (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X= Y= =
  piStrNat _ (⟦⟧Tm₀ a ∙ ! qq^₁)
  ∙ ap-irr-piStr (⟦weakenTm⟧=' k a aᵈ X= Y=)
                 (⟦weakenTm+⟧=' k b bᵈ X= (ElStr= ∙ ⟦⟧Tm₀ a) (ElStrNat _ (⟦⟧Tm₀ a ∙ ! qq^₁) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)))
⟦weakenTm⟧=' k (lam A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) X= Y= =
  lamStrNat _ (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! qq^₁)
  ∙ ap-irr-lamStr (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=))
                  (⟦weakenTm+⟧=' k u uᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=))
⟦weakenTm⟧=' k (app A B f a) (Aᵈ , Bᵈ , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) X= Y= =
  appStrNat _ (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! qq^₁)
  ∙ ap-irr-appStr (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=))
                  (⟦weakenTm⟧=' k f fᵈ X= Y=)
                  (⟦weakenTm⟧=' k a aᵈ X= Y=)

⟦weakenTm⟧=' k (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X= Y= =
  sigStrNat _ (⟦⟧Tm₀ a ∙ ! qq^₁)
  ∙ ap-irr-sigStr (⟦weakenTm⟧=' k a aᵈ X= Y=)
                  (⟦weakenTm+⟧=' k b bᵈ X= (ElStr= ∙ ⟦⟧Tm₀ a) (ElStrNat _ (⟦⟧Tm₀ a ∙ ! qq^₁)
                                                              ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)))
⟦weakenTm⟧=' k (pair A B a b) (Aᵈ , Bᵈ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X= Y= =
  pairStrNat _ (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! qq^₁)
  ∙ ap-irr-pairStr (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=))
                   (⟦weakenTm⟧=' k a aᵈ X= Y=)
                   (⟦weakenTm⟧=' k b bᵈ X= Y=)
⟦weakenTm⟧=' k (pr1 A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) X= Y= =
  pr1StrNat _ (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! qq^₁)
  ∙ ap-irr-pr1Str (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=))
                  (⟦weakenTm⟧=' k u uᵈ X= Y=)
⟦weakenTm⟧=' k (pr2 A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) X= Y= =
  pr2StrNat _ (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! qq^₁)
  ∙ ap-irr-pr2Str (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=))
                  (⟦weakenTm⟧=' k u uᵈ X= Y=)

⟦weakenTm⟧=' k (nat i) tt X= Y= =
  natStrNat _ (! qq^₁)
  ∙ ap (natStr i) (qq^₀ ∙ ! Y=)
⟦weakenTm⟧=' k zero tt X= Y= =
  zeroStrNat _ (! qq^₁)
  ∙ ap zeroStr (qq^₀ ∙ ! Y=)
⟦weakenTm⟧=' k (suc u) (uᵈ , uₛ , u₁ , tt) X= Y= =
  sucStrNat _ (⟦⟧Tm₀ u ∙ ! qq^₁)
  ∙ ap-irr2 sucStr (⟦weakenTm⟧=' k u uᵈ X= Y=)
⟦weakenTm⟧=' k (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , duᵈ , duₛ , du₁ , tt) X= Y= =
  {!!}

⟦weakenTm⟧=' k (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X= Y= =
  idStrNat _ (⟦⟧Tm₀ a ∙ ! qq^₁)
  ∙ ap-irr-idStr (⟦weakenTm⟧=' k a aᵈ X= Y=)
                 (⟦weakenTm⟧=' k u uᵈ X= Y=)
                 (⟦weakenTm⟧=' k v vᵈ X= Y=)
⟦weakenTm⟧=' k (refl A u) (Aᵈ , uᵈ , uₛ , u₁ , tt) X= Y= =
  reflStrNat _ (⟦⟧Ty-ft A ∙ ! qq^₁)
  ∙ ap-irr-reflStr (⟦weakenTy⟧=' k A Aᵈ X= Y=)
                   (⟦weakenTm⟧=' k u uᵈ X= Y=)
⟦weakenTm⟧=' k (jj A P d a b p) uᵈ X= Y= =
  {!!}

-- ⟦weakenTy+⟧=' k A Aᵈ X= p Y= = ap2-irr star (ap2-irr qq (ap-irr (λ X → qq^ k {X = X}) (! p) {b = X=} {b' = X= ∙ ap (ft^ k) (! p)}) (⟦⟧Ty-ft A)) refl ∙ ⟦weakenTy⟧=' (prev k) A Aᵈ (X= ∙ ap (ft^ k) (! p)) Y=

-- ⟦weakenTm+⟧=' k u uᵈ X= p Y= = ap ss (ap2-irr comp refl (ap2-irr qq (ap-irr (λ X → qq^ k {X = X}) (! p) {b = X=} {b' = X= ∙ ap (ft^ k) (! p)}) (⟦⟧Tm₀ u))) ∙ ⟦weakenTm⟧=' (prev k) u uᵈ (X= ∙ ap (ft^ k) (! p)) Y=

⟦weakenTm⟧₁' k u uᵈ X= refl refl = ap ∂₁ (! (⟦weakenTm⟧=' k u uᵈ X= refl)) ∙ ss₁ ∙  ap2-irr star (! (assoc {q = ! (pp₀ ∙ comp₁)})) refl ∙ star-comp (comp₁ ∙ pp₁) ∙ (ap2-irr star refl (ap2-irr star (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! (ap ft comp₁ ∙ ⟦⟧Tm₁-ft u))) refl ∙ star-id ∙ comp₁))


⟦weakenMor⟧ᵈ refl ◇ tt = tt
⟦weakenMor⟧ᵈ {X+ = X+} refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = (⟦weakenMor⟧ᵈ refl δ δᵈ , ⟦weakenTm⟧ᵈ' last u uᵈ refl refl , ⟦⟧Mor₁ (weakenMor δ) , (⟦weakenTm⟧₁' last u uᵈ refl refl refl ∙ ap2-irr star refl u₁ ∙ ! (star-comp δ₁) ∙ ! (ap2-irr star (⟦weakenMor⟧= refl δ δᵈ ∙ ap2-irr comp refl (! qq^last)) refl)) , tt) 

⟦weakenMor⟧= refl ◇ tt = ! (ptmor-unique _ _ (comp₀ ∙ pp₀) (comp₁ ∙ pt-unique _))

⟦weakenMor⟧= refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = {!ap2-irr comp (ap2-irr qq (⟦weakenMor⟧= refl δ δᵈ) refl ∙ qq-comp (⟦⟧Mor₁ δ)) (! (⟦weakenTm⟧=' last u uᵈ refl refl)) ∙ assoc {p = ss₁ ∙ ! (qq₀ ∙ ap2-irr star (! (! (assoc {q = ! pp₀ ∙ ap ∂₀ (ap pp (! comp₁))}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! pp₁)) refl ∙ id-right)) (! (comp₁ ∙ u₁)))} {q = qq₁ ∙ ! qq₀} ∙ ap2-irr comp refl (ap2-irr comp (ap2-irr qq (! (! (assoc {q = ! pp₀ ∙ ap ∂₀ (ap pp (! comp₁))}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! pp₁)) refl ∙ id-right)) (! (comp₁ ∙ u₁))) refl ∙ ! ss-qq) ∙ ! assoc!}

⟦weakenMor+⟧ᵈ refl refl δ δᵈ p = (⟦weakenMor⟧ᵈ refl δ δᵈ , (tt , (⟦⟧Mor₁ (weakenMor δ) , ((ss₁ ∙ ap2-irr star (ap2-irr comp (ap pp (id₁ ∙ ! p)) (ap idC (! p ∙ ! pp₀)) ∙ id-left) (id₁ ∙ ! p) ∙ ! (star-comp {p = pp₁ ∙ ! (⟦⟧Mor₀ δ ∙ ap ft (! p))} (⟦⟧Mor₁ δ)) ∙ ap2-irr star (ap2-irr comp refl (ap pp p) ∙ ! (⟦weakenMor⟧= refl δ δᵈ)) refl) , tt))))


⟦weakenMor+⟧= refl refl δ δᵈ p = ap2-irr comp (ap2-irr qq (⟦weakenMor⟧= refl δ δᵈ) refl) refl {b' = ss₁ ∙ ! (qq₀ ∙ star-comp (⟦⟧Mor₁ δ) ∙ ap2-irr star (! (ap2-irr comp (ap pp id₁) (ap idC (! pp₀)) ∙ id-left)) (p ∙ ! id₁))} ∙ ap2-irr comp (qq-comp (⟦⟧Mor₁ δ)) refl ∙ (assoc {p = ss₁ ∙ ! (qq₀ ∙ ap2-irr star (! (ap2-irr comp (ap pp id₁) (ap idC (! pp₀)) ∙ id-left)) (p ∙ ! id₁))}) ∙ ap2-irr comp refl (ap2-irr comp (ap2-irr qq (! id-left ∙ ap2-irr comp (ap pp (! id₁)) (ap idC pp₀)) (p ∙ ! id₁)) refl ∙ (! ss-qq) ∙ ap idC (! (qq₀ ∙ p))) ∙ id-left

⟦⟧TyEq+ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {X' : Ob n} {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A'))
          {Aᵈ : isDefined (⟦ A ⟧Ty X)} {A'ᵈ : isDefined (⟦ A' ⟧Ty X')} → X ≡ X' → ⟦ A ⟧Ty X $ Aᵈ ≡ ⟦ A' ⟧Ty X' $ A'ᵈ
⟦⟧TyEq+ r dA= refl = ⟦⟧TyEq r dA=

⟦⟧TmEq+ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {X' : Ob n} {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A))
          {uᵈ : isDefined (⟦ u ⟧Tm X)} {u'ᵈ : isDefined (⟦ u' ⟧Tm X')} → X ≡ X' → ⟦ u ⟧Tm X $ uᵈ ≡ ⟦ u' ⟧Tm X' $ u'ᵈ
⟦⟧TmEq+ r du= refl = ⟦⟧TmEq r du=

⟦⟧TyEq Γᵈ (TySymm dA=) = ! (⟦⟧TyEq Γᵈ dA=)
⟦⟧TyEq Γᵈ (TyTran dB dA= dB=) = ⟦⟧TyEq Γᵈ dA= {A'ᵈ = ⟦⟧Tyᵈ Γᵈ dB} ∙ ⟦⟧TyEq Γᵈ dB=

⟦⟧TyEq Γᵈ UUCong = refl
⟦⟧TyEq Γᵈ (ElCong dv=) = ap-irr2 (ElStr _) (⟦⟧TmEq Γᵈ dv=)
⟦⟧TyEq Γᵈ {A = sig A B} (SigCong dA dA= dB=) = ap SigStr (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TyEq Γᵈ {A = pi A B} (PiCong dA dA= dB=) = ap PiStr (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TyEq Γᵈ NatCong = refl
⟦⟧TyEq Γᵈ (IdCong dA du dv) = ap-irr-IdStr (⟦⟧TyEq Γᵈ dA) (⟦⟧TmEq Γᵈ du) (⟦⟧TmEq Γᵈ dv)

⟦⟧TyEq Γᵈ ElUU= = eluuStr
⟦⟧TyEq Γᵈ (ElPi= da db) = elpiStr
⟦⟧TyEq Γᵈ (ElSig= da db) = elsigStr
⟦⟧TyEq Γᵈ ElNat= = elnatStr
⟦⟧TyEq Γᵈ (ElId= da du dv) = elidStr

⟦⟧TmEq Γᵈ (VarLastCong dA) = refl
⟦⟧TmEq (Γᵈ , Bᵈ , tt) (VarPrevCong {k = k} {k' = k'} dA dx) = {!TODO(var) use ss-comp?!}
⟦⟧TmEq Γᵈ (TmSymm du=) = ! (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq Γᵈ (TmTran dv du= du'=) = ⟦⟧TmEq Γᵈ du= {u'ᵈ = ⟦⟧Tmᵈ Γᵈ dv} ∙ ⟦⟧TmEq Γᵈ du'=
⟦⟧TmEq Γᵈ (ConvEq dA' du= dA=) = ⟦⟧TmEq Γᵈ du=

⟦⟧TmEq Γᵈ UUUUCong = refl

⟦⟧TmEq Γᵈ {u = pi i a b} (PiUUCong da da= db=) {uᵈ = (aᵈ , aₛ , a₁ , _)} = ap-irr-piStr (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq+ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db= (ap-irr2 (ElStr _) (⟦⟧TmEq Γᵈ da=)) )
⟦⟧TmEq Γᵈ {u = lam A B u} (LamCong dA dA= dB= du=) = ap-irr-lamStr (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) du= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TmEq Γᵈ {u = app A B f a} (AppCong dA dA= dB= df= da=) = ap-irr-appStr (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ df=) (⟦⟧TmEq Γᵈ da=)

⟦⟧TmEq Γᵈ {u = sig i a b} (SigUUCong da da= db=) {uᵈ = (aᵈ , aₛ , a₁ , bᵈ , _)} {u'ᵈ = (a'ᵈ , _ , _ , b'ᵈ , _)} = ap-irr-sigStr (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq+ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db= (ap-irr2 (ElStr i) (⟦⟧TmEq Γᵈ da=)))
⟦⟧TmEq Γᵈ {u = pair A B a b} (PairCong dA dA= dB= da= db=) = ap-irr-pairStr (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq Γᵈ db=)
⟦⟧TmEq Γᵈ {u = pr1 A B u} (Pr1Cong dA dA= dB= du=) = ap-irr-pr1Str (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq Γᵈ {u = pr2 A B u} (Pr2Cong dA dA= dB= du=) = ap-irr-pr2Str (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ du=)

⟦⟧TmEq Γᵈ NatUUCong = refl
⟦⟧TmEq Γᵈ ZeroCong = refl
⟦⟧TmEq Γᵈ (SucCong du) = ap-irr2 sucStr (⟦⟧TmEq Γᵈ du)
⟦⟧TmEq Γᵈ {u = natelim P dO dS u} (NatelimCong dP dP= ddO= ddS= du=) = {!!}

⟦⟧TmEq Γᵈ (IdUUCong da= du= dv=) = ap-irr-idStr (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq Γᵈ du=) (⟦⟧TmEq Γᵈ dv=)
⟦⟧TmEq Γᵈ (ReflCong dA= du=) = ap-irr-reflStr (⟦⟧TyEq Γᵈ dA=) (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq Γᵈ {u = jj A P d a b p} (JJCong dA dA= dP= dd= da= db= dp=) = {!!}

⟦⟧TmEq Γᵈ {u = app A B (lam A B u) a} (BetaPi dA dB du da) = betaPiStr ∙ ! (⟦subst⟧Tm= (⟦⟧Ty-ft A) u _ a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))
⟦⟧TmEq Γᵈ (BetaSig1 dA dB da db) = betaSig1Str
⟦⟧TmEq Γᵈ (BetaSig2 dA dB da db) = betaSig2Str

⟦tsubst⟧Tyᵈ (uu i) tt δ δᵈ = tt
⟦tsubst⟧Tyᵈ (el i v) (vᵈ , vₛ , v₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ v vᵈ δ δᵈ ,
   ⟦⟧Tmₛ (v [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ v vᵈ δ δᵈ v₁ ∙ UUStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (⟦⟧Tm₀ v ∙ ! (⟦⟧Mor₁ δ)) ∙ ap (UUStr i) (⟦⟧Mor₀ δ ∙ ! (⟦⟧Tm₀ (v [ δ ]Tm)))) , tt)
⟦tsubst⟧Tyᵈ (pi A B) (Aᵈ , Bᵈ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) , tt)
⟦tsubst⟧Tyᵈ (sig A B) (Aᵈ , Bᵈ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) , tt)
⟦tsubst⟧Tyᵈ nat tt δ δᵈ = tt
⟦tsubst⟧Tyᵈ (id A u v) (Aᵈ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦tsubst⟧Tmᵈ v vᵈ δ δᵈ ,
   ⟦⟧Tmₛ (v [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ v vᵈ δ δᵈ v₁ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) , tt)

⟦tsubst⟧Tmᵈ (var ()) uᵈ ◇ δᵈ
⟦tsubst⟧Tmᵈ (var last) _ (δ , u) (_ , uᵈ , _) = uᵈ
⟦tsubst⟧Tmᵈ (var (prev x)) tt (δ , u) (δᵈ , _) = ⟦tsubst⟧Tmᵈ (var x) tt δ δᵈ

⟦tsubst⟧Tmᵈ (uu i) tt δ δᵈ = tt

⟦tsubst⟧Tmᵈ (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  let δ+ᵈ = ⟦weakenMor+⟧ᵈ (ElStr= ∙ ⟦⟧Tm₀ (a [ δ ]Tm)) (ElStr= ∙ ⟦⟧Tm₀ a) δ δᵈ (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ) in
 (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ δ δᵈ a₁ ∙ ap2-irr star refl (ap (UUStr i) (⟦⟧Tm₀ a)) ∙ ⟦tsubst⟧Ty= (uu i) (tt) δ δᵈ ∙ ap (UUStr i) (! (⟦⟧Tm₀ (a [ δ ]Tm)))) ,
  ⟦tsubst⟧Tmᵈ b bᵈ (weakenMor+ δ) δ+ᵈ ,
  ⟦⟧Tmₛ (b [ weakenMor+ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ b bᵈ (weakenMor+ δ) δ+ᵈ b₁ ∙ UUStrNat _ (! (⟦⟧Mor₁ (weakenMor+ δ) {δᵈ = δ+ᵈ})) ∙ ap (UUStr i) (⟦⟧Mor₀ (weakenMor+ δ) {δᵈ = δ+ᵈ})) , tt)
⟦tsubst⟧Tmᵈ (lam A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
   ⟦tsubst⟧Tmᵈ u uᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
   ⟦⟧Tmₛ (u [ weakenMor+ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) u₁
     ∙ ⟦tsubst⟧Ty= B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) , tt)
⟦tsubst⟧Tmᵈ (app A B f a) (Aᵈ , Bᵈ , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
   ⟦tsubst⟧Tmᵈ f fᵈ δ δᵈ ,
   ⟦⟧Tmₛ (f [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ f fᵈ δ δᵈ f₁ ∙ ⟦tsubst⟧Ty= (pi A B) (Aᵈ , Bᵈ , tt) δ δᵈ) ,
   ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
   ⟦⟧Tmₛ (a [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ a aᵈ δ δᵈ a₁ ∙ ap2-irr star refl (⟦⟧Ty-ft B) ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ ∙ ! (⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty))) , tt)

⟦tsubst⟧Tmᵈ (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  let δ+ᵈ = ⟦weakenMor+⟧ᵈ (ElStr= ∙ ⟦⟧Tm₀ (a [ δ ]Tm)) (ElStr= ∙ ⟦⟧Tm₀ a) δ δᵈ (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ) in
 (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ δ δᵈ a₁ ∙ ap2-irr star refl (ap (UUStr i) (⟦⟧Tm₀ a)) ∙ ⟦tsubst⟧Ty= (uu i) (tt) δ δᵈ ∙ ap (UUStr i) (! (⟦⟧Tm₀ (a [ δ ]Tm)))) ,
  ⟦tsubst⟧Tmᵈ b bᵈ (weakenMor+ δ) δ+ᵈ ,
  ⟦⟧Tmₛ (b [ weakenMor+ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ b bᵈ (weakenMor+ δ) δ+ᵈ b₁ ∙ UUStrNat _ (! (⟦⟧Mor₁ (weakenMor+ δ) {δᵈ = δ+ᵈ})) ∙ ap (UUStr i) (⟦⟧Mor₀ (weakenMor+ δ) {δᵈ = δ+ᵈ})) , tt)
⟦tsubst⟧Tmᵈ (pair A B a b) (Aᵈ , Bᵈ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
  ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ δ δᵈ a₁ ∙ ap2-irr star refl (⟦⟧Ty-ft B) ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ ∙ ! (⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty))) ,
  ⟦tsubst⟧Tmᵈ b bᵈ δ δᵈ ,
  ⟦⟧Tmₛ (b [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ b bᵈ δ δᵈ b₁ ∙ starstar aₛ (is-section₀ aₛ a₁ ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ)) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ)) refl ∙ ap2-irr star (⟦tsubst⟧Tm= a aᵈ δ δᵈ) (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) , tt)
⟦tsubst⟧Tmᵈ (pr1 A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
  ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
  ⟦⟧Tmₛ (u [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ ∙ ⟦tsubst⟧Ty= (sig A B) (Aᵈ , Bᵈ , tt) δ δᵈ) , tt)
⟦tsubst⟧Tmᵈ (pr2 A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
  ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
  ⟦⟧Tmₛ (u [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ ∙ ⟦tsubst⟧Ty= (sig A B) (Aᵈ , Bᵈ , tt) δ δᵈ) , tt)

⟦tsubst⟧Tmᵈ (nat i) tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ zero tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ (suc u) (uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ ∙ ap2-irr star refl (ap NatStr (⟦⟧Tm₀ u)) ∙ ⟦tsubst⟧Ty= nat tt δ δᵈ ∙ ap NatStr (! (⟦⟧Tm₀ (u [ δ ]Tm)))) , tt)
⟦tsubst⟧Tmᵈ (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , duᵈ , duₛ , du₁ , tt) X= Y= =
  {!!}

⟦tsubst⟧Tmᵈ (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
   ⟦⟧Tmₛ (a [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ a aᵈ δ δᵈ a₁ ∙ ap2-irr star refl (ap (UUStr i) (⟦⟧Tm₀ a)) ∙ ⟦tsubst⟧Ty= (uu i) tt δ δᵈ ∙ ap (UUStr i) (! (⟦⟧Tm₀ (a [ δ ]Tm)))) ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ ∙ ⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ) ,
   ⟦tsubst⟧Tmᵈ v vᵈ δ δᵈ ,
   ⟦⟧Tmₛ (v [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ v vᵈ δ δᵈ v₁ ∙ ⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ) , tt)
⟦tsubst⟧Tmᵈ (refl A u) (Aᵈ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) , tt)
⟦tsubst⟧Tmᵈ (jj A P d a b p) uᵈ X= Y= =
  {!!}

⟦tsubst⟧Ty= (uu i) Aᵈ δ δᵈ =
  UUStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (! (⟦⟧Mor₁ δ))
  ∙ ap (UUStr i) (⟦⟧Mor₀ δ)
⟦tsubst⟧Ty= (el i v) (vᵈ , _) δ δᵈ =
  ElStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (⟦⟧Tm₀ v ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr2 (ElStr i) (⟦tsubst⟧Tm= v vᵈ δ δᵈ)
⟦tsubst⟧Ty= (pi A B) (Aᵈ , Bᵈ , tt) δ δᵈ =
  PiStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) ((ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A) ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap PiStr (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
⟦tsubst⟧Ty= (sig A B) (Aᵈ , Bᵈ , tt) δ δᵈ =
  SigStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) ((ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A) ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap SigStr (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
⟦tsubst⟧Ty= nat Aᵈ δ δᵈ =
  NatStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (! (⟦⟧Mor₁ δ))
  ∙ ap NatStr (⟦⟧Mor₀ δ)
⟦tsubst⟧Ty= (id A u v) (Aᵈ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  IdStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr-IdStr (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                 (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
                 (⟦tsubst⟧Tm= v vᵈ δ δᵈ)

-- ⟦tsubst⟧Tm= (var ()) _ ◇ δᵈ
-- ⟦tsubst⟧Tm= (var last) tt (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = ! (! (ss-of-section (⟦ u ⟧Tm _ $ uᵈ) (⟦⟧Tmₛ u)) ∙ ss-comp {f₁ = u₁} ∙ ap ss ((! id-right ∙ ap2-irr comp (ap idC (comp₁ ∙ qq₁) ∙ ss-qq) refl) ∙ assoc {q = ss₁ ∙ ! qq₀}) ∙ ! (ss-comp {f₁ = comp₁ ∙ ss₁}))
-- ⟦tsubst⟧Tm= (var (prev x)) (xᵈ , _) (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = ss-comp {f₁ = comp₁ ∙ ss₁} ∙ ap ss (! (assoc {q = ss₁ ∙ ! qq₀}) ∙ ap2-irr comp (! ss-qq) refl ∙ assoc ∙ ap2-irr comp refl (! assoc ∙ ap2-irr comp pp-qq refl ∙ assoc {p = u₁ ∙ ! pp₀} {q = pp₁ ∙ ft-star} ∙ ap2-irr comp refl (ap2-irr comp (ap pp (! u₁)) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! (⟦⟧Mor₀ δ))) ∙ id-left)) ∙ ⟦tsubst⟧Tm= (var x) xᵈ δ δᵈ

⟦tsubst⟧Tm= (var k) tt δ δᵈ = ?

⟦tsubst⟧Tm= (uu i) tt δ δᵈ =
  uuStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (! (⟦⟧Mor₁ δ))
  ∙ ap (uuStr i) (⟦⟧Mor₀ δ)

⟦tsubst⟧Tm= (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  piStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (⟦⟧Tm₀ a ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr-piStr (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                 (⟦tsubst⟧Tm+= b bᵈ δ δᵈ (ElStr= ∙ ⟦⟧Tm₀ (a [ δ ]Tm)) (ElStr= ∙ ⟦⟧Tm₀ a) (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ))
⟦tsubst⟧Tm= (lam A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  lamStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr-lamStr (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                  (⟦tsubst⟧Tm+= u uᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
⟦tsubst⟧Tm= (app A B f a) (Aᵈ , Bᵈ , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) δ δᵈ =
  appStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr-appStr (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                  (⟦tsubst⟧Tm= f fᵈ δ δᵈ)
                  (⟦tsubst⟧Tm= a aᵈ δ δᵈ)

⟦tsubst⟧Tm= (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  sigStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (⟦⟧Tm₀ a ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr-sigStr (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                  (⟦tsubst⟧Tm+= b bᵈ δ δᵈ (ElStr= ∙ ⟦⟧Tm₀ (a [ δ ]Tm)) (ElStr= ∙ ⟦⟧Tm₀ a) (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ))
⟦tsubst⟧Tm= (pair A B a b) (Aᵈ , Bᵈ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  pairStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr-pairStr (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                   (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                   (⟦tsubst⟧Tm= b bᵈ δ δᵈ)
⟦tsubst⟧Tm= (pr1 A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  pr1StrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr-pr1Str (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                   (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
⟦tsubst⟧Tm= (pr2 A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  pr2StrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr-pr2Str (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                   (⟦tsubst⟧Tm= u uᵈ δ δᵈ)

⟦tsubst⟧Tm= (nat i) tt δ δᵈ =
  natStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (! (⟦⟧Mor₁ δ))
  ∙ ap (natStr i) (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= zero tt δ δᵈ =
  zeroStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (! (⟦⟧Mor₁ δ))
  ∙ ap zeroStr (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= (suc u) (uᵈ , uₛ , u₁ , tt) δ δᵈ =
  sucStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (⟦⟧Tm₀ u ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr2 sucStr (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
⟦tsubst⟧Tm= (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , duᵈ , duₛ , du₁ , tt) X= Y= =
  {!!}

⟦tsubst⟧Tm= (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  idStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (⟦⟧Tm₀ a ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr-idStr (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                 (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
                 (⟦tsubst⟧Tm= v vᵈ δ δᵈ)
⟦tsubst⟧Tm= (refl A u) (Aᵈ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  reflStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr-reflStr (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                  (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
⟦tsubst⟧Tm= (jj A P d a b p) uᵈ X= Y= =
  {!!}




⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ = ap ∂₁ (! (⟦tsubst⟧Tm= u uᵈ δ δᵈ)) ∙ ss₁ ∙ ap2-irr star (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! (⟦⟧Mor₁ δ))) refl ∙ id-right) (comp₁ ∙ u₁)

⟦tsubst⟧Ty+= A Aᵈ δ δᵈ X= Y= p =
  ap2-irr star (! (⟦weakenMor+⟧= X= (ap ft (⟦⟧Ty-ft A) ∙ Y=) δ δᵈ (ap2-irr star refl (⟦⟧Ty-ft A) ∙ p))
                ∙ ap-irr (λ x z → ⟦ weakenMor+ δ ⟧Mor _ x $ z) (⟦⟧Ty-ft A) {b = ⟦weakenMor+⟧ᵈ X= (ap ft (⟦⟧Ty-ft A) ∙ Y=) δ δᵈ (ap2-irr star refl (⟦⟧Ty-ft A) ∙ p)} {b' = ⟦weakenMor+⟧ᵈ X= Y= δ δᵈ p}) refl
  ∙ ⟦tsubst⟧Ty= A Aᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ X= Y= δ δᵈ p)

⟦tsubst⟧Tm+= u uᵈ δ δᵈ X= Y= p =
  ap ss (ap2-irr comp refl (! (⟦weakenMor+⟧= X= (ap ft (⟦⟧Tm₀ u) ∙ Y=) δ δᵈ (ap2-irr star refl (⟦⟧Tm₀ u) ∙ p))
                            ∙ ap-irr (λ x z → ⟦ weakenMor+ δ ⟧Mor _ x $ z) (⟦⟧Tm₀ u) {b = ⟦weakenMor+⟧ᵈ X= (ap ft (⟦⟧Tm₀ u) ∙ Y=) δ δᵈ (ap2-irr star refl (⟦⟧Tm₀ u) ∙ p)} {b' = ⟦weakenMor+⟧ᵈ X= Y= δ δᵈ p}))
  ∙ ⟦tsubst⟧Tm= u uᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ X= Y= δ δᵈ p)

⟦subst⟧Tyᵈ refl B Bᵈ u uᵈ q = ⟦tsubst⟧Tyᵈ B Bᵈ _ (⟦idMor+⟧ᵈ refl u uᵈ q)

⟦subst⟧Tmᵈ refl v vᵈ u uᵈ q = ⟦tsubst⟧Tmᵈ v vᵈ _ (⟦idMor+⟧ᵈ refl u uᵈ q)

⟦subst⟧Ty= refl B Bᵈ u uᵈ q = ! (⟦tsubst⟧Ty= B Bᵈ _ (⟦idMor+⟧ᵈ refl u uᵈ q)) ∙ ap2-irr star (⟦idMor+⟧= refl u uᵈ q) refl

⟦subst⟧Tm= refl v vᵈ u uᵈ q = ! (⟦tsubst⟧Tm= v vᵈ _ (⟦idMor+⟧ᵈ refl u uᵈ q)) ∙ ap2-irr starTm (⟦idMor+⟧= refl u uᵈ q) refl {b = ⟦⟧Tm₀ v ∙ ! (comp₁ ∙ qq₁)} {b' = ⟦⟧Tm₀ v ∙ ! q}


⟦idMor+⟧ᵈ {X = X} refl u uᵈ u₁ =
  (⟦idMor⟧ᵈ {X = X} refl ,
   uᵈ ,
   ⟦⟧Mor₁ (idMor _) ,
   (u₁ ∙ ! (ap2-irr star (⟦idMor⟧= refl) refl ∙ star-id)) , tt)

⟦idMor+⟧= refl u uᵈ u₁ =
  ap2-irr comp (ap2-irr qq (⟦idMor⟧= refl) refl ∙ qq-id ∙ ap idC (! u₁)) refl ∙ id-right

{- Totality of the interpretation function on derivable contexts -}

⟦⟧Ctxᵈ : {Γ : Ctx n} (dΓ : ⊢ Γ) → isDefined (⟦ Γ ⟧Ctx)
⟦⟧Ctxᵈ {Γ = ◇} tt = tt
⟦⟧Ctxᵈ {Γ = Γ , A} (dΓ , dA) = let Γᵈ = ⟦⟧Ctxᵈ dΓ in (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt)

{- Interpretation of context equalities -}

⟦⟧CtxEq : {Γ Γ' : Ctx n} (dΓ= : ⊢ Γ == Γ') {Γᵈ : isDefined (⟦ Γ ⟧Ctx)} {Γ'ᵈ : isDefined (⟦ Γ' ⟧Ctx)}
        → ⟦ Γ ⟧Ctx $ Γᵈ ≡ ⟦ Γ' ⟧Ctx $ Γ'ᵈ
⟦⟧CtxEq {Γ = ◇} {◇} _ = refl
⟦⟧CtxEq {Γ = Γ , A} {Γ' , A'} (dΓ= , _ , _ , dA= , _) {Γᵈ = Γᵈ , Aᵈ , tt}
  = ⟦⟧TyEq+ Γᵈ dA= (⟦⟧CtxEq dΓ=)

{- Interpretation of morphism equalities -}

⟦⟧MorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {Y : Ob m} (dδ= : Γ ⊢ δ == δ' ∷> Δ) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} {δ'ᵈ : isDefined (⟦ δ' ⟧Mor X Y)}
        → ⟦ δ ⟧Mor X Y $ δᵈ ≡ ⟦ δ' ⟧Mor X Y $ δ'ᵈ
⟦⟧MorEq {Δ = ◇} {δ = ◇} {◇} r tt = refl
⟦⟧MorEq {Γ' = Γ'} {Δ = Δ , B} {δ = δ , u} {δ' , u'} r (dδ= , du=) = ap2-irr comp (ap2-irr qq (⟦⟧MorEq {Γ' = Γ'} {Δ' = Δ} r dδ=) refl) (⟦⟧TmEq r du=)

{- Interpretation of morphism substitution -}

⟦tsubst⟧Morᵈ : {X : Ob n} {Y Y' : Ob m} {Z : Ob k} (Y= : Y ≡ Y') (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (θ : Mor m k) (θᵈ : isDefined (⟦ θ ⟧Mor Y' Z)) → isDefined (⟦ θ [ δ ]Mor ⟧Mor X Z)
⟦tsubst⟧Mor= : {X : Ob n} {Y Y' : Ob m} {Z : Ob k} (Y= : Y ≡ Y') (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (θ : Mor m k) (θᵈ : isDefined (⟦ θ ⟧Mor Y' Z))
             → ⟦ θ [ δ ]Mor ⟧Mor X Z $ (⟦tsubst⟧Morᵈ Y= δ δᵈ θ θᵈ) ≡ comp (⟦ θ ⟧Mor Y' Z $ θᵈ) (⟦ δ ⟧Mor X Y $ δᵈ) (⟦⟧Mor₁ δ ∙ Y= ∙ ! (⟦⟧Mor₀ θ))

⟦tsubst⟧Morᵈ refl δ δᵈ ◇ tt = tt
⟦tsubst⟧Morᵈ refl δ δᵈ (θ , u) (θᵈ , uᵈ , θ₁ , u₁ , tt) = (⟦tsubst⟧Morᵈ refl δ δᵈ θ θᵈ , ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ , ⟦⟧Mor₁ (θ [ δ ]Mor) , (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ refl ∙ ! (ap2-irr star (⟦tsubst⟧Mor= refl δ δᵈ θ θᵈ) refl ∙ star-comp (⟦⟧Mor₁ θ) ∙ ap2-irr star refl (! u₁))) , tt)

⟦tsubst⟧Mor= refl δ δᵈ ◇ θᵈ = ! (ptmor-unique _ _ (comp₀ ∙ ⟦⟧Mor₀ δ) (comp₁ ∙ ptmor₁))
⟦tsubst⟧Mor= refl δ δᵈ (θ , u) (θᵈ , uᵈ , θ₁ , u₁ , tt) =
  let thing = (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! (⟦⟧Mor₁ δ))) refl ∙ id-right) in
  ap2-irr comp (ap2-irr qq (⟦tsubst⟧Mor= refl δ δᵈ θ θᵈ) refl) (! (⟦tsubst⟧Tm= u uᵈ δ δᵈ)) {b' = ss₁ ∙ (ap2-irr star thing (comp₁ ∙ u₁) ∙ ! (star-comp (⟦⟧Mor₁ θ))) ∙ ! qq₀}
  ∙ ap2-irr comp (qq-comp _) refl ∙ assoc {p = ss₁ ∙ ap2-irr star thing (comp₁ ∙ u₁) ∙ ! qq₀} {q = qq₁ ∙ ! qq₀}
  ∙ ! (assoc ∙ ap2-irr comp refl (ss-qq ∙ ap2-irr comp (ap2-irr qq thing (comp₁ ∙ u₁)) refl))
