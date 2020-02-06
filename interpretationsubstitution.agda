{-# OPTIONS --rewriting --prop #-}

open import common
open import typetheory
open import syntx
open import rules
open import contextualcat

module _ (sC : StructuredCCat) where

open StructuredCCat sC
open CCat+ ccat renaming (Mor to MorC; id to idC)

open import partialinterpretation sC
open import interpretationweakening sC

{-
In this file we prove that substitution commutes with the partial interpretation function in the
appropriate sense. The main mutually inductive lemmas are about total substitutions.
-}

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
            → star (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y $ Aᵈ) (⟦⟧Ty-ft A) (⟦⟧Mor₁ δ)
              ≡ ⟦ A [ δ ]Ty ⟧Ty X $ ⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ

⟦tsubst⟧Tm= : {X : Ob n} {Y : Ob m} (u : TmExpr m)
              (uᵈ : isDefined (⟦ u ⟧Tm Y))
              (δ : Mor n m)
              (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            → starTm (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ u ⟧Tm Y $ uᵈ) (⟦⟧Tm₀ u) (⟦⟧Mor₁ δ)
              ≡ ⟦ u [ δ ]Tm ⟧Tm X $ ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ

{- Codomain of the interpretation of a substitution -}

⟦tsubst⟧Tm₁ : {Z : Ob (suc m)} {X : Ob n} {Y : Ob m} (u : TmExpr m)
            → (uᵈ : isDefined (⟦ u ⟧Tm Y)) (u₁ : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ Z)
            → (δ : Mor n m)
            → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))            
            → ∂₁ (⟦ u [ δ ]Tm ⟧Tm X $ ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ)
              ≡ star (⟦ δ ⟧Mor X Y $ δᵈ) Z (⟦⟧Tm₁-ft u u₁) (⟦⟧Mor₁ δ)
⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ = ap ∂₁ (! (⟦tsubst⟧Tm= u uᵈ δ δᵈ)) ∙ starTm₁ _ (⟦⟧Tm₁-ft u u₁) _ (⟦⟧Tmₛ u) u₁ (⟦⟧Mor₁ δ)


{- We prove first a bunch of special cases, using the lemmas above -}

⟦tsubst⟧Ty+ᵈ : {Z : Ob (suc n)} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} (A : TyExpr (suc m)) (Aᵈ : isDefined (⟦ A ⟧Ty Y'))
               (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'= : ft Y' ≡ Y)
               (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
             → isDefined (⟦ A [ weakenMor+ δ ]Ty ⟧Ty Z)
⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ Y'= Z= = ⟦tsubst⟧Tyᵈ A Aᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= Z=)

⟦tsubst⟧Ty+= : {Z : Ob (suc n)} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} (A : TyExpr (suc m)) (Aᵈ : isDefined (⟦ A ⟧Ty Y'))
               (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'= : ft Y' ≡ Y)
               (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
             → star+ (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y' $ Aᵈ) (⟦⟧Ty-ft A) Y'= (⟦⟧Mor₁ δ)
               ≡ ⟦ A [ weakenMor+ δ ]Ty ⟧Ty Z $ ⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ Y'= Z=
⟦tsubst⟧Ty+= A Aᵈ δ δᵈ Y'= Z= = ap-irr-star (! (⟦weaken⟧Mor+= δ δᵈ Y'= Z=)) refl ∙ ⟦tsubst⟧Ty= A Aᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= Z=)

⟦tsubst⟧Tm+ᵈ : {Z : Ob (suc n)} {X : Ob n} {Y' : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc m))
               (uᵈ : isDefined (⟦ u ⟧Tm Y'))
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (Y'= : ft Y' ≡ Y)
               (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → isDefined (⟦ u [ weakenMor+ δ ]Tm ⟧Tm Z)
⟦tsubst⟧Tm+ᵈ u uᵈ δ δᵈ Y'= Z= = ⟦tsubst⟧Tmᵈ u uᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= Z=)

⟦tsubst⟧Tm+= : {Z : Ob (suc n)} {X : Ob n} {Y' : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc m))
               (uᵈ : isDefined (⟦ u ⟧Tm Y'))
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (Y'= : ft Y' ≡ Y)
               (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
             → starTm+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'= (⟦ u ⟧Tm Y' $ uᵈ) (⟦⟧Tm₀ u) (⟦⟧Mor₁ δ)
               ≡ ⟦ u [ weakenMor+ δ ]Tm ⟧Tm Z $ ⟦tsubst⟧Tm+ᵈ u uᵈ δ δᵈ Y'= Z=
⟦tsubst⟧Tm+= u uᵈ δ δᵈ Y'= Z= =
  ap ss (ap-irr-comp refl (! (⟦weaken⟧Mor+= δ δᵈ Y'= Z=)))
  ∙ ⟦tsubst⟧Tm= u uᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= Z=)

⟦tsubst⟧Tm+₁ : {Z : Ob (suc n)} {X : Ob n} {Y'' : Ob (suc (suc m))} {Y' : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc m))
               (uᵈ : isDefined (⟦ u ⟧Tm Y')) (u₁ : ∂₁ (⟦ u ⟧Tm Y' $ uᵈ) ≡ Y'')               
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
               (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)            
               → ∂₁ (⟦ u [ weakenMor+ δ ]Tm ⟧Tm Z $ ⟦tsubst⟧Tm+ᵈ u uᵈ δ δᵈ Y'= Z=) ≡ star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ)
⟦tsubst⟧Tm+₁ u uᵈ u₁ δ δᵈ Y''= Y'= Z= = ! (ap ∂₁ (⟦tsubst⟧Tm+= u uᵈ δ δᵈ Y'= Z=)) ∙ starTm+₁ (⟦ δ ⟧Mor _ _ $ δᵈ) Y''= Y'= (⟦ u ⟧Tm _ $ uᵈ) (⟦⟧Tmₛ u) u₁ (⟦⟧Mor₁ δ)

{- Substitution by a weakenMor+ ^2 -}

⟦tsubst⟧Ty++ᵈ : {Z : Ob (suc (suc n))} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} {Y'' : Ob (suc (suc m))} (A : TyExpr (suc (suc m))) (Aᵈ : isDefined (⟦ A ⟧Ty Y''))
                (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
                (Z= : star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → isDefined (⟦ A [ weakenMor+ (weakenMor+ δ) ]Ty ⟧Ty Z)
⟦tsubst⟧Ty++ᵈ A Aᵈ δ δᵈ Y''= Y'= Z= = ⟦tsubst⟧Ty+ᵈ A Aᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) Y''= ((ap-irr-star (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) refl) ∙ Z=)

⟦tsubst⟧Ty++= : {Z : Ob (suc (suc n))} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} {Y'' : Ob (suc (suc m))} (A : TyExpr (suc (suc m))) (Aᵈ : isDefined (⟦ A ⟧Ty Y''))
               (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
               (Z= : star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
               → star++ (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y'' $ Aᵈ) (⟦⟧Ty-ft A) Y''= Y'= (⟦⟧Mor₁ δ)
                 ≡ ⟦ A [ weakenMor+ (weakenMor+ δ) ]Ty ⟧Ty Z $ ⟦tsubst⟧Ty++ᵈ A Aᵈ δ δᵈ Y''= Y'= Z=
⟦tsubst⟧Ty++= A Aᵈ δ δᵈ Y''= Y'= Z= = ap-irr-star (ap-irr-qq (! (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=))) refl) refl ∙ ⟦tsubst⟧Ty+= A Aᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) Y''= (ap-irr-star (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) refl ∙ Z=) 

⟦tsubst⟧Tm++ᵈ : {Z : Ob (suc (suc n))} {X : Ob n} {Y'' : Ob (suc (suc m))} {Y' : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc (suc m)))
               (uᵈ : isDefined (⟦ u ⟧Tm Y''))
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
               (Z= : star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → isDefined (⟦ u [ weakenMor+ (weakenMor+ δ) ]Tm ⟧Tm Z)             
⟦tsubst⟧Tm++ᵈ u uᵈ δ δᵈ Y''= Y'= Z= = ⟦tsubst⟧Tm+ᵈ u uᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) Y''= (ap-irr-star (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) refl ∙ Z=)  

-- TODO : make something prettier
⟦tsubst⟧Tm++= : {Z : Ob (suc (suc n))} {X : Ob n} {Y'' : Ob (suc (suc m))} {Y' : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc (suc m)))
                (uᵈ : isDefined (⟦ u ⟧Tm Y''))
                (δ : Mor n m)
                (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
                (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
                (Z= : star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
                → starTm++ (⟦ δ ⟧Mor X Y $ δᵈ) Y''= Y'= (⟦ u ⟧Tm Y'' $ uᵈ) (⟦⟧Tm₀ u) (⟦⟧Mor₁ δ)
                  ≡ ⟦ u [ weakenMor+ (weakenMor+ δ) ]Tm ⟧Tm Z $ ⟦tsubst⟧Tm++ᵈ u uᵈ δ δᵈ Y''= Y'= Z=
⟦tsubst⟧Tm++= u uᵈ δ δᵈ Y''= Y'= Z= = ap-irr-starTm (ap-irr-qq (! (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=))) refl) refl ∙ ⟦tsubst⟧Tm+= u uᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) Y''= (ap-irr-star (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) refl ∙ Z=) 

⟦tsubst⟧Tm++₁ : {Z : Ob (suc (suc n))} {X : Ob n} {Y''' : Ob (suc (suc (suc m)))} {Y'' : Ob (suc (suc m))} {Y' : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc (suc m)))
                (uᵈ : isDefined (⟦ u ⟧Tm Y'')) (u₁ : ∂₁ (⟦ u ⟧Tm Y'' $ uᵈ) ≡ Y''')
                (δ : Mor n m)
                (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
                (Y'''= : ft Y''' ≡ Y'') (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
                (Z= : star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → ∂₁ (⟦ u [ weakenMor+ (weakenMor+ δ) ]Tm ⟧Tm Z $ ⟦tsubst⟧Tm++ᵈ u uᵈ δ δᵈ Y''= Y'= Z=) ≡ star++ (⟦ δ ⟧Mor X Y $ δᵈ) Y''' Y'''= Y''= Y'= (⟦⟧Mor₁ δ)
⟦tsubst⟧Tm++₁ u uᵈ u₁ δ δᵈ Y'''= Y''= Y'= Z= = ap ∂₁ (! (⟦tsubst⟧Tm++= u uᵈ δ δᵈ Y''= Y'= Z=)) ∙ starTm++₁ (⟦ δ ⟧Mor _ _ $ δᵈ) Y'''= Y''= Y'= (⟦ u ⟧Tm _ $ uᵈ) (⟦⟧Tmₛ u) u₁ (⟦⟧Mor₁ δ) 

{- Substitution by a weakenMor+ ^3 -}

⟦tsubst⟧Ty+++ᵈ : {Z : Ob (suc (suc (suc n)))} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} {Y'' : Ob (suc (suc m))} {Y''' : Ob (suc (suc (suc m)))} (A : TyExpr (suc (suc (suc m)))) (Aᵈ : isDefined (⟦ A ⟧Ty Y'''))
                 (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'''= : ft Y''' ≡ Y'') (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
                 (Z= : star++ (⟦ δ ⟧Mor X Y $ δᵈ) Y''' Y'''= Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
               → isDefined (⟦ A [ weakenMor+ (weakenMor+ (weakenMor+ δ)) ]Ty ⟧Ty Z)
⟦tsubst⟧Ty+++ᵈ A Aᵈ δ δᵈ Y'''= Y''= Y'= Z= = ⟦tsubst⟧Ty++ᵈ A Aᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=))) Y'''= Y''= (ap-irr-star (ap-irr-qq (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=))) refl) refl ∙ Z=)


⟦tsubst⟧Ty+++= : {Z : Ob (suc (suc (suc n)))} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} {Y'' : Ob (suc (suc m))} {Y''' : Ob (suc (suc (suc m)))} (A : TyExpr (suc (suc (suc m)))) (Aᵈ : isDefined (⟦ A ⟧Ty Y'''))
                 (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'''= : ft Y''' ≡ Y'') (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
                 (Z= : star++ (⟦ δ ⟧Mor X Y $ δᵈ) Y''' Y'''= Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
                 → star+++ (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y''' $ Aᵈ) (⟦⟧Ty-ft A) Y'''= Y''= Y'= (⟦⟧Mor₁ δ)
                   ≡ ⟦ A [ weakenMor+ (weakenMor+ (weakenMor+ δ)) ]Ty ⟧Ty Z $ ⟦tsubst⟧Ty+++ᵈ A Aᵈ δ δᵈ Y'''= Y''= Y'= Z=
⟦tsubst⟧Ty+++= A Aᵈ δ δᵈ Y'''= Y''= Y'= Z= = ap-irr-star (ap-irr-qq (ap-irr-qq (! (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=)))) refl) refl) refl ∙ ⟦tsubst⟧Ty++= A Aᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=))) Y'''= Y''= (ap-irr-star (ap-irr-qq (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=))) refl) refl ∙ Z=)


{- We can now prove the main lemmas -} 

⟦tsubst⟧Tyᵈ (uu i) tt δ δᵈ = tt
⟦tsubst⟧Tyᵈ (el i v) (vᵈ , vₛ , v₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ v vᵈ δ δᵈ ,
   ⟦⟧Tmₛ (v [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ v vᵈ v₁ δ δᵈ ∙ UUStrNat (⟦⟧Mor₀ δ)) , tt)

⟦tsubst⟧Tyᵈ (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ
  , ⟦⟧Ty-ft (A [ δ ]Ty)
  , ⟦tsubst⟧Tyᵈ B Bᵈ δ δᵈ
  , ⟦⟧Ty-ft (B [ δ ]Ty)
  , tt)

⟦tsubst⟧Tyᵈ (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) , tt)

⟦tsubst⟧Tyᵈ (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) , tt)

⟦tsubst⟧Tyᵈ empty tt δ δᵈ = tt

⟦tsubst⟧Tyᵈ unit tt δ δᵈ = tt

⟦tsubst⟧Tyᵈ nat tt δ δᵈ = tt

⟦tsubst⟧Tyᵈ (id A u v) (Aᵈ , A= , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦tsubst⟧Tmᵈ v vᵈ δ δᵈ ,
   ⟦⟧Tmₛ (v [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ v vᵈ v₁ δ δᵈ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) , tt)
 
⟦tsubst⟧Tmᵈ (var ()) uᵈ ◇ δᵈ
⟦tsubst⟧Tmᵈ (var last) _ (δ , u) (_ , uᵈ , _) = uᵈ
⟦tsubst⟧Tmᵈ (var (prev x)) tt (δ , u) (δᵈ , _) = ⟦tsubst⟧Tmᵈ (var x) tt δ δᵈ

⟦tsubst⟧Tmᵈ (uu i) tt δ δᵈ = tt

⟦tsubst⟧Tmᵈ (sum i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ
  , ⟦⟧Tmₛ (a [ δ ]Tm)
  , (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (uu i) tt δ δᵈ)
  , ⟦tsubst⟧Tmᵈ b bᵈ δ δᵈ
  , ⟦⟧Tmₛ (b [ δ ]Tm)
  , (⟦tsubst⟧Tm₁ b bᵈ b₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (uu i) tt δ δᵈ)
  , tt)
⟦tsubst⟧Tmᵈ (inl A B a) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ
  , ⟦⟧Ty-ft (A [ δ ]Ty)
  , ⟦tsubst⟧Tyᵈ B Bᵈ δ δᵈ
  , ⟦⟧Ty-ft (B [ δ ]Ty)
  , ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ
  , ⟦⟧Tmₛ (a [ δ ]Tm)
  , (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
  , tt)
⟦tsubst⟧Tmᵈ (inr A B b) (Aᵈ , A= , Bᵈ , B= , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ
  , ⟦⟧Ty-ft (A [ δ ]Ty)
  , ⟦tsubst⟧Tyᵈ B Bᵈ δ δᵈ
  , ⟦⟧Ty-ft (B [ δ ]Ty)
  , ⟦tsubst⟧Tmᵈ b bᵈ δ δᵈ
  , ⟦⟧Tmₛ (b [ δ ]Tm)
  , (⟦tsubst⟧Tm₁ b bᵈ b₁ δ δᵈ ∙ ⟦tsubst⟧Ty= B Bᵈ δ δᵈ)
  , tt)
⟦tsubst⟧Tmᵈ (match A B C da db u) (Aᵈ , A= , Bᵈ , B= , Cᵈ , C= , daᵈ , daₛ , da₁ , dbᵈ , dbₛ , db₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =  
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ
  , ⟦⟧Ty-ft (A [ δ ]Ty)
  , ⟦tsubst⟧Tyᵈ B Bᵈ δ δᵈ
  , ⟦⟧Ty-ft (B [ δ ]Ty)
  , ⟦tsubst⟧Ty+ᵈ C Cᵈ δ δᵈ SumStr= (⟦tsubst⟧Ty= (sum A B) SumABᵈ δ δᵈ) -- using SumAB[δ] gives termination error
  , ⟦⟧Ty-ft (C [ weakenMor+ δ ]Ty)
  , ⟦tsubst⟧Tm+ᵈ da daᵈ δ δᵈ A= A[δ]=
  , ⟦⟧Tmₛ (da [ weakenMor+ δ ]Tm)
  , (⟦tsubst⟧Tm+₁ da daᵈ da₁ δ δᵈ T-da₁= A= A[δ]=
    ∙ T-da₁Nat (⟦⟧Mor₀ δ)
    ∙ ap-irr-T-da₁ refl  A[δ]= B[δ]= (⟦tsubst⟧Ty+= C Cᵈ δ δᵈ SumStr= (⟦tsubst⟧Ty= (sum A B) SumABᵈ δ δᵈ))) -- when using SumAB[δ]= and C[δ]= gives termination error
  , ⟦tsubst⟧Tm+ᵈ db dbᵈ δ δᵈ B= (⟦tsubst⟧Ty= B Bᵈ δ δᵈ)
  , ⟦⟧Tmₛ (db [ weakenMor+ δ ]Tm)
  , (⟦tsubst⟧Tm+₁ db dbᵈ db₁ δ δᵈ T-db₁= B= B[δ]=
    ∙ T-db₁Nat (⟦⟧Mor₀ δ)
    ∙ ap-irr-T-db₁ refl A[δ]= B[δ]= (⟦tsubst⟧Ty+= C Cᵈ δ δᵈ SumStr= (⟦tsubst⟧Ty= (sum A B) SumABᵈ δ δᵈ))) -- when using SumAB[δ]= and C[δ]= gives termination error
  , ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ
  , ⟦⟧Tmₛ (u [ δ ]Tm)
  , (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (sum A B) SumABᵈ δ δᵈ) -- using SumAB[δ] gives termination error
  , tt)
    where A[δ]= = ⟦tsubst⟧Ty= A Aᵈ δ δᵈ
          B[δ]= = ⟦tsubst⟧Ty= B Bᵈ δ δᵈ
        
          SumABᵈ : isDefined (⟦ sum A B ⟧Ty _)
          SumABᵈ = (Aᵈ , A= , Bᵈ , B= , tt)
          --SumAB[δ]= = ⟦tsubst⟧Ty= (sum A B) SumABᵈ δ δᵈ

          --C[δ]= = ⟦tsubst⟧Ty+= C Cᵈ δ δᵈ SumStr= SumAB[δ]=

⟦tsubst⟧Tmᵈ (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (uu i) tt δ δᵈ) ,
  ⟦tsubst⟧Tm+ᵈ b bᵈ δ δᵈ ElStr= (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ) ,
  ⟦⟧Tmₛ (b [ weakenMor+ δ ]Tm) ,
  (⟦tsubst⟧Tm+₁ b bᵈ b₁ δ δᵈ UUStr= ElStr= (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ)
  ∙ UUStrNat (qq₀ ∙ (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ))) ,
  tt)  
⟦tsubst⟧Tmᵈ (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= A[δ]= ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tm+ᵈ u uᵈ δ δᵈ A= A[δ]= ,
   ⟦⟧Tmₛ (u [ weakenMor+ δ ]Tm) ,
   (⟦tsubst⟧Tm+₁ u uᵈ u₁ δ δᵈ B= A= A[δ]= ∙ ⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= A[δ]=) ,
   tt)
                 where A[δ]= = (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
⟦tsubst⟧Tmᵈ (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ f fᵈ δ δᵈ ,
   ⟦⟧Tmₛ (f [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ f fᵈ f₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ) ,
   ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
   ⟦⟧Tmₛ (a [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) , tt)

⟦tsubst⟧Tmᵈ (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (uu i) tt δ δᵈ) ,
  ⟦tsubst⟧Tm+ᵈ b bᵈ δ δᵈ ElStr= (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ) ,
  ⟦⟧Tmₛ (b [ weakenMor+ δ ]Tm) ,
  (⟦tsubst⟧Tm+₁ b bᵈ b₁ δ δᵈ UUStr= ElStr= (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ) ∙ UUStrNat (qq₀ ∙ (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ))) , tt)
⟦tsubst⟧Tmᵈ (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦⟧Ty-ft (A [ δ ]Ty) ,
  ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= A[δ]= ,
  ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
  ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ A[δ]=) ,
  ⟦tsubst⟧Tmᵈ b bᵈ δ δᵈ ,
  ⟦⟧Tmₛ (b [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ b bᵈ b₁ δ δᵈ ∙ starstar A= aₛ ∙ ap-irr-star (⟦tsubst⟧Tm= a aᵈ δ δᵈ) (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) , tt ) 
    where A[δ]= = ⟦tsubst⟧Ty= A Aᵈ δ δᵈ
⟦tsubst⟧Tmᵈ (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦⟧Ty-ft (A [ δ ]Ty) ,
  ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
  ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
  ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
  ⟦⟧Tmₛ (u [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ) ,
  tt)    
⟦tsubst⟧Tmᵈ (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦⟧Ty-ft (A [ δ ]Ty) ,
  ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
  ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
  ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
  ⟦⟧Tmₛ (u [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ) ,
  tt)

⟦tsubst⟧Tmᵈ (empty i) tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ (emptyelim A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ EmptyStr= (⟦tsubst⟧Ty= empty tt δ δᵈ) ,
   ⟦⟧Ty-ft (A [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ⟦tsubst⟧Ty= empty tt δ δᵈ) ,
   tt)

⟦tsubst⟧Tmᵈ (unit i) tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ tt tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ (unitelim A dtt u) (Aᵈ , A= , dttᵈ , dttₛ , dtt₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ UnitStr= (⟦tsubst⟧Ty= unit tt δ δᵈ) ,
   ⟦⟧Ty-ft (A [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ dtt dttᵈ δ δᵈ ,
   ⟦⟧Tmₛ (dtt [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ dtt dttᵈ dtt₁ δ δᵈ ∙ starstar UnitStr= ttStrₛ ∙ ap-irr-star (ttStrNat (⟦⟧Mor₀ δ)) (⟦tsubst⟧Ty+= A Aᵈ δ δᵈ UnitStr= (⟦tsubst⟧Ty= unit tt δ δᵈ))) , -- using (⟦tsubst⟧Tm= tt tt δ δᵈ) gives termination error
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ⟦tsubst⟧Ty= unit tt δ δᵈ) , tt)

⟦tsubst⟧Tmᵈ (nat i) tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ zero tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ (suc u) (uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ NatStrNat (⟦⟧Mor₀ δ)) , tt)
⟦tsubst⟧Tmᵈ {X = X} (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (P[δ]ᵈ , P[δ]-ft , dO[δ]ᵈ , dO[δ]ₛ , dO[δ]₁ , dS[δ]ᵈ , dS[δ]ₛ , dS[δ]₁ , u[δ]ᵈ , u[δ]ₛ , u[δ]₁ , tt)
    where
      nat[δ]= = NatStrNat (⟦⟧Mor₀ δ)      
      P[δ]= = ⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= nat[δ]=
      P[δ]ᵈ = ⟦tsubst⟧Ty+ᵈ P Pᵈ δ δᵈ NatStr= nat[δ]=
      P[δ]-ft = ⟦⟧Ty-ft (P [ weakenMor+ δ ]Ty)
      dO[δ]ᵈ = ⟦tsubst⟧Tmᵈ dO dOᵈ δ δᵈ
      dO[δ]ₛ = ⟦⟧Tmₛ (dO [ δ ]Tm)
      dO[δ]₁ = ⟦tsubst⟧Tm₁ dO dOᵈ dO₁ δ δᵈ ∙ starstar NatStr= zeroStrₛ ∙ ap-irr-star (zeroStrNat (⟦⟧Mor₀ δ)) P[δ]= 
      dS[δ]ᵈ = ⟦tsubst⟧Tm++ᵈ dS dSᵈ δ δᵈ P= NatStr= P[δ]=
      dS[δ]ₛ = ⟦⟧Tmₛ (dS [ weakenMor+ (weakenMor+ δ) ]Tm)
      dS[δ]₁ = ⟦tsubst⟧Tm++₁ dS dSᵈ dS₁ δ δᵈ T-dS₁= P= NatStr= P[δ]=
               ∙ T-dS₁Nat (⟦⟧Mor₀ δ) ∙ ap-irr-T-dS₁ refl P[δ]=
      u[δ]ᵈ = ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ
      u[δ]ₛ = ⟦⟧Tmₛ (u [ δ ]Tm)
      u[δ]₁ = ⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ nat[δ]=

⟦tsubst⟧Tmᵈ (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
   ⟦⟧Tmₛ (a [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (uu i) tt δ δᵈ) , 
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ) ,
   ⟦tsubst⟧Tmᵈ v vᵈ δ δᵈ ,
   ⟦⟧Tmₛ (v [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ v vᵈ v₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ) , tt)
⟦tsubst⟧Tmᵈ (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) , tt)
⟦tsubst⟧Tmᵈ (jj A P d a b p) (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt) δ δᵈ =
  (A[δ]ᵈ , A[δ]-ft , P[δ]ᵈ , P[δ]-ft , d[δ]ᵈ , d[δ]ₛ , d[δ]₁ , a[δ]ᵈ , a[δ]ₛ , a[δ]₁ , b[δ]ᵈ , b[δ]ₛ , b[δ]₁ , p[δ]ᵈ , p[δ]ₛ , p[δ]₁ , tt)
    where
      A[δ]ᵈ = ⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ
      A[δ]-ft = ⟦⟧Ty-ft (A [ δ ]Ty)
      A[δ]= = ⟦tsubst⟧Ty= A Aᵈ δ δᵈ
      P[δ]ᵈ = ⟦tsubst⟧Ty+++ᵈ P Pᵈ δ δᵈ T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (⟦⟧Mor₀ δ) ∙ ap-irr-T-ftP refl A[δ]=)
      P[δ]-ft = ⟦⟧Ty-ft (P [ weakenMor+ (weakenMor+ (weakenMor+ δ)) ]Ty)
      P[δ]= = ⟦tsubst⟧Ty+++= P Pᵈ δ δᵈ T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (⟦⟧Mor₀ δ) ∙ ap-irr-T-ftP refl A[δ]=)
      d[δ]ᵈ = ⟦tsubst⟧Tm+ᵈ d dᵈ δ δᵈ A= A[δ]=
      d[δ]ₛ = ⟦⟧Tmₛ (d [ weakenMor+ δ ]Tm)
      d[δ]₁ = ⟦tsubst⟧Tm+₁ d dᵈ d₁ δ δᵈ T-d₁= A= A[δ]= ∙ T-d₁Nat (⟦⟧Mor₀ δ) ∙ ap-irr-T-d₁ refl A[δ]= P[δ]= 
      a[δ]ᵈ = ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ
      a[δ]ₛ = ⟦⟧Tmₛ (a [ δ ]Tm)
      a[δ]₁ = ⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ A[δ]=
      b[δ]ᵈ = ⟦tsubst⟧Tmᵈ b bᵈ δ δᵈ
      b[δ]ₛ = ⟦⟧Tmₛ (b [ δ ]Tm)
      b[δ]₁ = ⟦tsubst⟧Tm₁ b bᵈ b₁ δ δᵈ ∙ A[δ]=
      p[δ]ᵈ = ⟦tsubst⟧Tmᵈ p pᵈ δ δᵈ
      p[δ]ₛ = ⟦⟧Tmₛ (p [ δ ]Tm)
      p[δ]₁ = ⟦tsubst⟧Tm₁ p pᵈ p₁ δ δᵈ ∙ IdStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-IdStr refl A[δ]= (⟦tsubst⟧Tm= a aᵈ δ δᵈ) (⟦tsubst⟧Tm= b bᵈ δ δᵈ) -- using ⟦tsubst⟧Ty= (id A a b) (Aᵈ , A= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ gives termination error
      

⟦tsubst⟧Ty= (uu i) Aᵈ δ δᵈ =
  UUStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Ty= (el i v) (vᵈ , _) δ δᵈ =
  ElStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-ElStr refl
                 (⟦tsubst⟧Tm= v vᵈ δ δᵈ)
⟦tsubst⟧Ty= (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  SumStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-SumStr refl
                  (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                  (⟦tsubst⟧Ty= B Bᵈ δ δᵈ)
⟦tsubst⟧Ty= (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  PiStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-PiStr refl
                 (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                 (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
⟦tsubst⟧Ty= (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  SigStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-SigStr refl
                  (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                  (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
⟦tsubst⟧Ty= empty Aᵈ δ δᵈ =
  EmptyStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Ty= unit Aᵈ δ δᵈ =
  UnitStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Ty= nat Aᵈ δ δᵈ =
  NatStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Ty= (id A u v) (Aᵈ , A= , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  IdStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-IdStr refl
                 (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                 (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
                 (⟦tsubst⟧Tm= v vᵈ δ δᵈ)

⟦tsubst⟧Tm= (var ()) _ ◇
⟦tsubst⟧Tm= (var last) _ (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) =
  star-varCL'' {g₀ = id₀} ∙ ap ss (id-right (comp₁ ∙ qq₁)) ∙ ! ss-comp ∙ ss-of-section (⟦ u ⟧Tm _ $ _) (⟦⟧Tmₛ u)
⟦tsubst⟧Tm= (var (prev k)) _ (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) =
  (star-varCL'' {g₀ = pp^₀ (prev k) _} ∙ ap ss (ap-irr-comp (pp^prev refl) refl ∙ ! assoc ∙ ap-irr-comp (assoc ∙ ap-irr-comp refl pp-qq ∙ ! assoc) refl ∙ assoc ∙ ap-irr-comp refl (refl ∙ is-section= (ft-star ∙ ⟦⟧Mor₀ δ) (⟦⟧Tmₛ u) u₁) ∙ id-left (comp₀ ∙ ⟦⟧Mor₀ δ)) ∙ ! (star-varCL'' {g₀ = pp^₀ k _})) ∙ ⟦tsubst⟧Tm= (var k) tt δ δᵈ

⟦tsubst⟧Tm= (uu i) tt δ δᵈ =
  uuStrNat (⟦⟧Mor₀ δ)

⟦tsubst⟧Tm= (sum i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  sumStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-sumStr refl
                  (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                  (⟦tsubst⟧Tm= b bᵈ δ δᵈ)
⟦tsubst⟧Tm= (inl A B a) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , tt) δ δᵈ =
  inlStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-inlStr refl
                  (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                  (⟦tsubst⟧Ty= B Bᵈ δ δᵈ)
                  (⟦tsubst⟧Tm= a aᵈ δ δᵈ)            
⟦tsubst⟧Tm= (inr A B b) (Aᵈ , A= , Bᵈ , B= , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  inrStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-inrStr refl
                  (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                  (⟦tsubst⟧Ty= B Bᵈ δ δᵈ)
                  (⟦tsubst⟧Tm= b bᵈ δ δᵈ)
⟦tsubst⟧Tm= (match A B C da db u) (Aᵈ , A= , Bᵈ , B= , Cᵈ , C= , daᵈ , daₛ , da₁ , dbᵈ , dbₛ , db₁ , uᵈ , uₛ , u₁) δ δᵈ =
  matchStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-matchStr refl
                    (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                    (⟦tsubst⟧Ty= B Bᵈ δ δᵈ)
                    (⟦tsubst⟧Ty+= C Cᵈ δ δᵈ SumStr= (⟦tsubst⟧Ty= (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ))
                    (⟦tsubst⟧Tm+= da daᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                    (⟦tsubst⟧Tm+= db dbᵈ δ δᵈ B= (⟦tsubst⟧Ty= B Bᵈ δ δᵈ))
                    (⟦tsubst⟧Tm= u uᵈ δ δᵈ)

⟦tsubst⟧Tm= (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  piStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-piStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                      (⟦tsubst⟧Tm+= b bᵈ δ δᵈ ElStr= (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ))                      
⟦tsubst⟧Tm= (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  lamStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-lamStr refl A[δ]=
                       (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= A[δ]=)
                       (⟦tsubst⟧Tm+= u uᵈ δ δᵈ A= A[δ]=)
    where A[δ]= = ⟦tsubst⟧Ty= A Aᵈ δ δᵈ
⟦tsubst⟧Tm= (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) δ δᵈ =
  appStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-appStr refl A[δ]=
                       (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= A[δ]=)
                       (⟦tsubst⟧Tm= f fᵈ δ δᵈ)
                       (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
    where A[δ]= = ⟦tsubst⟧Ty= A Aᵈ δ δᵈ
    
⟦tsubst⟧Tm= (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  sigStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-sigStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                       (⟦tsubst⟧Tm+= b bᵈ δ δᵈ ElStr= (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ))
⟦tsubst⟧Tm= (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  pairStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-pairStr refl A[δ]=
                        (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= A[δ]=)
                        (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                        (⟦tsubst⟧Tm= b bᵈ δ δᵈ)
    where A[δ]= = ⟦tsubst⟧Ty= A Aᵈ δ δᵈ    
⟦tsubst⟧Tm= (pr1 A B u) (Aᵈ , A= , Bᵈ  , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  pr1StrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-pr1Str refl A[δ]=
                       (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= A[δ]=)
                       (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
    where A[δ]= = ⟦tsubst⟧Ty= A Aᵈ δ δᵈ    
⟦tsubst⟧Tm= (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  pr2StrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-pr2Str refl  A[δ]=
                       (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A=  A[δ]=)
                       (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
    where A[δ]= = ⟦tsubst⟧Ty= A Aᵈ δ δᵈ
    
⟦tsubst⟧Tm= (empty i) tt δ δᵈ =
  emptyStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= (emptyelim A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  emptyelimStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-emptyelimStr refl
                        (⟦tsubst⟧Ty+= A Aᵈ δ δᵈ EmptyStr= (⟦tsubst⟧Ty= empty tt δ δᵈ)) (⟦tsubst⟧Tm= u uᵈ δ δᵈ)

⟦tsubst⟧Tm= (unit i) tt δ δᵈ =
  unitStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= tt tt δ δᵈ =
  ttStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= (unitelim A dtt u) (Aᵈ , A= , dttᵈ , dttₛ , dtt₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  unitelimStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-unitelimStr refl
                       (⟦tsubst⟧Ty+= A Aᵈ δ δᵈ UnitStr= (⟦tsubst⟧Ty= unit tt δ δᵈ)) (⟦tsubst⟧Tm= dtt dttᵈ δ δᵈ) (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
  
⟦tsubst⟧Tm= (nat i) tt δ δᵈ =
  natStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= zero tt δ δᵈ =
  zeroStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= (suc u) (uᵈ , uₛ , u₁ , tt) δ δᵈ =
  sucStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-sucStr refl (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
⟦tsubst⟧Tm= (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  natelimStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-natelimStr refl (⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= (⟦tsubst⟧Ty= nat tt δ δᵈ))
                           (⟦tsubst⟧Tm= dO dOᵈ δ δᵈ)
                           (⟦tsubst⟧Tm++= dS dSᵈ δ δᵈ P= NatStr= (⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= (⟦tsubst⟧Ty= nat tt δ δᵈ)))
                           (⟦tsubst⟧Tm= u uᵈ δ δᵈ)

⟦tsubst⟧Tm= (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  idStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-idStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                      (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
                      (⟦tsubst⟧Tm= v vᵈ δ δᵈ)
⟦tsubst⟧Tm= (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  reflStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-reflStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                        (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
⟦tsubst⟧Tm= (jj A P d a b p) (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt) δ δᵈ =
  jjStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-jjStr refl A[δ]=
                      (⟦tsubst⟧Ty+++= P Pᵈ δ δᵈ T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (⟦⟧Mor₀ δ)
                       ∙ ap-irr-T-ftP refl A[δ]=))
                      (⟦tsubst⟧Tm+= d dᵈ δ δᵈ A= A[δ]=)
                      (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                      (⟦tsubst⟧Tm= b bᵈ δ δᵈ)
                      (⟦tsubst⟧Tm= p pᵈ δ δᵈ)
    where A[δ]= = (⟦tsubst⟧Ty= A Aᵈ δ δᵈ )



{- We are done with the main induction in this file, here are a few additional lemmas needed later. -}


{- Interpretation of the identity morphism -}

⟦idMor⟧ᵈ : {X Y : Ob n} → Y ≡ X → isDefined (⟦ idMor n ⟧Mor X Y)
⟦idMor⟧= : {X Y : Ob n} (p : Y ≡ X) → ⟦ idMor n ⟧Mor X Y $ ⟦idMor⟧ᵈ p ≡ idC X

⟦idMor⟧ᵈ {zero} Y= = tt
⟦idMor⟧ᵈ {suc n} {Y = Y} Y= = ⟦weaken⟧Mor+ᵈ (idMor n) (⟦idMor⟧ᵈ {n = n} (ap ft Y=)) refl (ap-irr-star (⟦idMor⟧= (ap ft Y=)) Y= ∙ star-id {p = refl})

⟦idMor⟧= {zero} Y= = ! (ptmor-unique _ (idC _) id₀ (id₁ ∙ pt-unique _))
⟦idMor⟧= {suc n} {Y = Y} Y= = ⟦weaken⟧Mor+= (idMor n) (⟦idMor⟧ᵈ {n = n} (ap ft Y=)) refl (ap-irr-star (⟦idMor⟧= (ap ft Y=)) Y= ∙ star-id {p = refl}) ∙ ap-irr-qq (⟦idMor⟧= (ap ft Y=)) Y= ∙ qq-id {p = refl}

{- Simple substitutions -}

⟦idMor+⟧ᵈ : {X : Ob n} {Y : Ob (suc n)} (p : ft Y ≡ X) (u : TmExpr n)
            (uᵈ : isDefined (⟦ u ⟧Tm X)) (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Y)
            → isDefined (⟦ idMor n , u ⟧Mor X Y)
⟦idMor+⟧ᵈ p u uᵈ u₁ =
  (⟦idMor⟧ᵈ p ,
   uᵈ ,
   ⟦⟧Mor₁ (idMor _) ,
   (u₁ ∙ ! (ap-irr-star (⟦idMor⟧= p) refl ∙ star-id {p = p})) , tt)

⟦idMor+⟧= : {X : Ob n} {Y : Ob (suc n)} (p : ft Y ≡ X) (u : TmExpr n)
            (uᵈ : isDefined (⟦ u ⟧Tm X)) (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Y)
            → ⟦ idMor n , u ⟧Mor X Y $ ⟦idMor+⟧ᵈ p u uᵈ u₁ ≡ ⟦ u ⟧Tm X $ uᵈ
⟦idMor+⟧= refl u uᵈ u₁ =
  ap-irr-comp (ap-irr-qq (⟦idMor⟧= refl) refl ∙ qq-id {p = refl}) refl ∙ id-right u₁

⟦subst⟧Tyᵈ : {X : Ob (suc n)} {Y : Ob n} (B : TyExpr (suc n))
           → isDefined (⟦ B ⟧Ty X)
           → (u : TmExpr n)
           → (uᵈ : isDefined (⟦ u ⟧Tm Y))
           → (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
           → isDefined (⟦ substTy B u ⟧Ty Y)
⟦subst⟧Tyᵈ B Bᵈ u uᵈ q = ⟦tsubst⟧Tyᵈ B Bᵈ _ (⟦idMor+⟧ᵈ (ap ft (! q) ∙ ⟦⟧Tm₁-ft u refl) u uᵈ q)

⟦subst⟧Tmᵈ : {X : Ob (suc n)} {Y : Ob n} (v : TmExpr (suc n))
            → isDefined (⟦ v ⟧Tm X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm Y))
            → (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → isDefined (⟦ substTm v u ⟧Tm Y)
⟦subst⟧Tmᵈ v vᵈ u uᵈ q = ⟦tsubst⟧Tmᵈ v vᵈ _ (⟦idMor+⟧ᵈ (ap ft (! q) ∙ ⟦⟧Tm₁-ft u refl) u uᵈ q)

⟦subst⟧Ty= : {X : Ob (suc n)} {Y : Ob n} (B : TyExpr (suc n))
             (Bᵈ : isDefined (⟦ B ⟧Ty X))
             (u : TmExpr n)
             (uᵈ : isDefined (⟦ u ⟧Tm Y))
             (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → ⟦ substTy B u ⟧Ty Y $ ⟦subst⟧Tyᵈ B Bᵈ u uᵈ q ≡ star (⟦ u ⟧Tm Y $ uᵈ) (⟦ B ⟧Ty X $ Bᵈ) (⟦⟧Ty-ft B) q
⟦subst⟧Ty= B Bᵈ u uᵈ q = ! (⟦tsubst⟧Ty= B Bᵈ _ (⟦idMor+⟧ᵈ (ap ft (! q) ∙ ⟦⟧Tm₁-ft u refl) u uᵈ q)) ∙ ap-irr-star (⟦idMor+⟧= (ap ft (! q) ∙ ⟦⟧Tm₁-ft u refl) u uᵈ q) refl

⟦subst⟧Tm= : {X : Ob (suc n)} {Y : Ob n} (v : TmExpr (suc n))
             (vᵈ : isDefined (⟦ v ⟧Tm X))
             (u : TmExpr n)
             (uᵈ : isDefined (⟦ u ⟧Tm Y))
             (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → ⟦ substTm v u ⟧Tm Y $ ⟦subst⟧Tmᵈ v vᵈ u uᵈ q ≡ starTm (⟦ u ⟧Tm Y $ uᵈ) (⟦ v ⟧Tm X $ vᵈ) (⟦⟧Tm₀ v) q
⟦subst⟧Tm= v vᵈ u uᵈ q = ! (⟦tsubst⟧Tm= v vᵈ _ (⟦idMor+⟧ᵈ (ap ft (! q) ∙ ⟦⟧Tm₁-ft u refl) u uᵈ q)) ∙ ap-irr-starTm (⟦idMor+⟧= (ap ft (! q) ∙ ⟦⟧Tm₁-ft u refl) u uᵈ q) refl

{- Double substitutions -}

⟦idMor++⟧ᵈ : {X : Ob (suc (suc n))} {X' : Ob (suc n)} (X= : ft X ≡ X') {X'' : Ob n} (X'= : ft X' ≡ X'')
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X'' $ uᵈ) ≡ X')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X'' $ vᵈ) ≡ star (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁)
            → isDefined (⟦ (idMor n , u) , v ⟧Mor X'' X)
⟦idMor++⟧ᵈ X= X'= u uᵈ u₁ v vᵈ v₁ =
  (⟦idMor+⟧ᵈ (ap ft X= ∙ X'=) u uᵈ (u₁ ∙ ! X=) ,
   vᵈ ,
   (comp₁ ∙ qq₁) ,
   (v₁ ∙ ap-irr-star (! (⟦idMor+⟧= (ap ft X= ∙ X'=) u uᵈ (u₁ ∙ ! X=))) refl) , tt)

⟦idMor++⟧= : {X : Ob (suc (suc n))} {X' : Ob (suc n)} (X= : ft X ≡ X') {X'' : Ob n} (X'= : ft X' ≡ X'')
           → (u : TmExpr n)
           → (uᵈ : isDefined (⟦ u ⟧Tm X''))
           → (u₁ : ∂₁ (⟦ u ⟧Tm X'' $ uᵈ) ≡ X')
           → (v : TmExpr n)
           → (vᵈ : isDefined (⟦ v ⟧Tm X''))
           → (v₁ : ∂₁ (⟦ v ⟧Tm X'' $ vᵈ) ≡ star (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁)
           → ⟦ (idMor n , u) , v ⟧Mor X'' X $ ⟦idMor++⟧ᵈ X= X'= u uᵈ u₁ v vᵈ v₁ ≡ comp (qq (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁) (⟦ v ⟧Tm X'' $ vᵈ) qq₀ v₁
⟦idMor++⟧= X= X'= u uᵈ u₁ v vᵈ v₁ = ap-irr-comp (ap-irr-qq (⟦idMor+⟧= (ap ft X= ∙ X'=) u uᵈ (u₁ ∙ ! X=)) refl) refl

⟦subst2⟧Tyᵈ : {X : Ob (suc (suc n))} {X' : Ob (suc n)} (X= : ft X ≡ X') {X'' : Ob n} (X'= : ft X' ≡ X'') (B : TyExpr (suc (suc n)))
            → isDefined (⟦ B ⟧Ty X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X'' $ uᵈ) ≡ X')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X'' $ vᵈ) ≡ star (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁)
            → isDefined (⟦ subst2Ty B u v ⟧Ty X'')
⟦subst2⟧Tyᵈ X= X'= B Bᵈ u uᵈ u₁ v vᵈ v₁ = ⟦tsubst⟧Tyᵈ B Bᵈ _ (⟦idMor++⟧ᵈ X= X'= u uᵈ u₁ v vᵈ v₁)


⟦subst2⟧Ty= : {X : Ob (suc (suc n))} {X' : Ob (suc n)} (X= : ft X ≡ X') {X'' : Ob n} (X'= : ft X' ≡ X'') (B : TyExpr (suc (suc n)))
            → (Bᵈ : isDefined (⟦ B ⟧Ty X))
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X'' $ uᵈ) ≡ X')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X'' $ vᵈ) ≡ star (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁)
            → ⟦ subst2Ty B u v ⟧Ty X'' $ ⟦subst2⟧Tyᵈ X= X'= B Bᵈ u uᵈ u₁ v vᵈ v₁ ≡ star (⟦ v ⟧Tm X'' $ vᵈ) (star (qq (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁) (⟦ B ⟧Ty X $ Bᵈ) (⟦⟧Ty-ft B) qq₁) (ft-star ∙ qq₀) v₁
⟦subst2⟧Ty= X= X'= B Bᵈ u uᵈ u₁ v vᵈ v₁ = ! (⟦tsubst⟧Ty= B Bᵈ _ (⟦idMor++⟧ᵈ X= X'= u uᵈ u₁ v vᵈ v₁)) ∙ ap-irr-star (⟦idMor++⟧= X= X'= u uᵈ u₁ v vᵈ v₁) refl ∙ star-comp

⟦subst2⟧Tmᵈ : {X : Ob (suc (suc n))} {X' : Ob (suc n)} (X= : ft X ≡ X') {X'' : Ob n} (X'= : ft X' ≡ X'') (t : TmExpr (suc (suc n)))
            → isDefined (⟦ t ⟧Tm X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X'' $ uᵈ) ≡ X')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X'' $ vᵈ) ≡ star (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁)
            → isDefined (⟦ subst2Tm t u v ⟧Tm X'')
⟦subst2⟧Tmᵈ X= X'= t tᵈ u uᵈ u₁ v vᵈ v₁ = ⟦tsubst⟧Tmᵈ t tᵈ _ (⟦idMor++⟧ᵈ X= X'= u uᵈ u₁ v vᵈ v₁)

⟦subst2⟧Tm= : {X : Ob (suc (suc n))} {X' : Ob (suc n)} (X= : ft X ≡ X') {X'' : Ob n} (X'= : ft X' ≡ X'') (t : TmExpr (suc (suc n)))
            → (tᵈ : isDefined (⟦ t ⟧Tm X))
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X'' $ uᵈ) ≡ X')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X'' $ vᵈ) ≡ star (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁)
            → ⟦ subst2Tm t u v ⟧Tm X'' $ ⟦subst2⟧Tmᵈ X= X'= t tᵈ u uᵈ u₁ v vᵈ v₁ ≡ starTm (⟦ v ⟧Tm X'' $ vᵈ) (starTm (qq (⟦ u ⟧Tm X'' $ uᵈ) X X= u₁) (⟦ t ⟧Tm X $ tᵈ) (⟦⟧Tm₀ t) qq₁) (ss₀ ∙ comp₀ ∙ qq₀) v₁
⟦subst2⟧Tm= X= X'= t tᵈ u uᵈ u₁ v vᵈ v₁ = ! (⟦tsubst⟧Tm= t tᵈ _ (⟦idMor++⟧ᵈ X= X'= u uᵈ u₁ v vᵈ v₁)) ∙ ap-irr-starTm (⟦idMor++⟧= X= X'= u uᵈ u₁ v vᵈ v₁) refl ∙ starTm-comp qq₀

{- Triple substitutions -}

⟦idMor+++⟧ᵈ : {X : Ob (suc (suc (suc n)))} {X' : Ob (suc (suc n))} (X= : ft X ≡ X') {X'' : Ob (suc n)} (X'= : ft X' ≡ X'') {X''' : Ob n} (X''= : ft X'' ≡ X''')
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X'''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X''' $ uᵈ) ≡ X'')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X'''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X''' $ vᵈ) ≡ star (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁)
            → (w : TmExpr n)
            → (wᵈ : isDefined (⟦ w ⟧Tm X'''))
            → (w₁ : ∂₁ (⟦ w ⟧Tm X''' $ wᵈ) ≡ star (⟦ v ⟧Tm X''' $ vᵈ) (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁) X X= qq₁) (ft-star ∙ qq₀) v₁)
            → isDefined (⟦ ((idMor n , u) , v) , w ⟧Mor X''' X)
⟦idMor+++⟧ᵈ refl X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ =
  (⟦idMor++⟧ᵈ X'= X''= u uᵈ u₁ v vᵈ v₁ ,
   wᵈ ,
   (comp₁ ∙ qq₁) ,
   (w₁ ∙ ! star-comp ∙ ap-irr-star (! (⟦idMor++⟧= X'= X''= u uᵈ u₁ v vᵈ v₁)) refl) , tt)

⟦idMor+++⟧= : {X : Ob (suc (suc (suc n)))} {X' : Ob (suc (suc n))} (X= : ft X ≡ X') {X'' : Ob (suc n)} (X'= : ft X' ≡ X'') {X''' : Ob n} (X''= : ft X'' ≡ X''')
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X'''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X''' $ uᵈ) ≡ X'')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X'''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X''' $ vᵈ) ≡ star (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁)
            → (w : TmExpr n)
            → (wᵈ : isDefined (⟦ w ⟧Tm X'''))
            → (w₁ : ∂₁ (⟦ w ⟧Tm X''' $ wᵈ) ≡ star (⟦ v ⟧Tm X''' $ vᵈ) (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁) X X= qq₁) (ft-star ∙ qq₀) v₁)
            → ⟦ ((idMor n , u) , v) , w ⟧Mor X''' X $ ⟦idMor+++⟧ᵈ X= X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ ≡
              comp (comp (qq (qq (⟦ u ⟧Tm X''' $ uᵈ)
                                 (ft X)
                                 (ap ft X= ∙ X'=)
                                 u₁)
                             X
                             refl
                             qq₁)
                         (qq (⟦ v ⟧Tm X''' $ vᵈ)
                             (star (qq (⟦ u ⟧Tm X''' $ uᵈ)
                                       X'
                                       X'=
                                       u₁)
                                   X
                                   X=
                                   qq₁)
                             (ft-star ∙ qq₀)
                             v₁)
                         (qq₀ ∙ ap-irr-star (ap-irr-qq refl X=) refl)
                         qq₁)
                   (⟦ w ⟧Tm X''' $ wᵈ)
                   (comp₀ ∙ qq₀)
                   w₁
⟦idMor+++⟧= refl X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ = ap-irr-comp (ap-irr-qq (⟦idMor++⟧= X'= X''= u uᵈ u₁ v vᵈ v₁) refl ∙ qq-comp) refl

⟦subst3⟧Tyᵈ : {X : Ob (suc (suc (suc n)))} {X' : Ob (suc (suc n))} (X= : ft X ≡ X') {X'' : Ob (suc n)} (X'= : ft X' ≡ X'') {X''' : Ob n} (X''= : ft X'' ≡ X''') (A : TyExpr (suc (suc (suc n))))
            → isDefined (⟦ A ⟧Ty X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X'''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X''' $ uᵈ) ≡ X'')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X'''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X''' $ vᵈ) ≡ star (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁)
            → (w : TmExpr n)
            → (wᵈ : isDefined (⟦ w ⟧Tm X'''))
            → (w₁ : ∂₁ (⟦ w ⟧Tm X''' $ wᵈ) ≡ star (⟦ v ⟧Tm X''' $ vᵈ)
                                               (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁)
                                                  X
                                                  X=
                                                  qq₁)
                                               (ft-star ∙ qq₀)
                                               v₁)
            → isDefined (⟦ subst3Ty A u v w ⟧Ty X''')
⟦subst3⟧Tyᵈ X= X'= X''= A Aᵈ u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ = ⟦tsubst⟧Tyᵈ A Aᵈ _ (⟦idMor+++⟧ᵈ X= X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁)

⟦subst3⟧Ty= : {X : Ob (suc (suc (suc n)))} {X' : Ob (suc (suc n))} (X= : ft X ≡ X') {X'' : Ob (suc n)} (X'= : ft X' ≡ X'') {X''' : Ob n} (X''= : ft X'' ≡ X''') (A : TyExpr (suc (suc (suc n))))
            → (Aᵈ : isDefined (⟦ A ⟧Ty X))
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X'''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X''' $ uᵈ) ≡ X'')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X'''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X''' $ vᵈ) ≡ star (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁)
            → (w : TmExpr n)
            → (wᵈ : isDefined (⟦ w ⟧Tm X'''))
            → (w₁ : ∂₁ (⟦ w ⟧Tm X''' $ wᵈ) ≡ star (⟦ v ⟧Tm X''' $ vᵈ)
                                                  (star+ (⟦ u ⟧Tm X''' $ uᵈ)
                                                         X
                                                         X=
                                                         X'=
                                                         u₁)
                                                  (ft-star ∙ qq₀)
                                                  v₁)
            → ⟦ subst3Ty A u v w ⟧Ty X''' $ ⟦subst3⟧Tyᵈ X= X'= X''= A Aᵈ u uᵈ u₁ v vᵈ v₁ w wᵈ w₁
              ≡ star
                  (⟦ w ⟧Tm X''' $ wᵈ)
                  (star
                     (qq (⟦ v ⟧Tm X''' $ vᵈ) (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁) X X= qq₁) (ft-star ∙ qq₀) v₁)
                     (star
                       (qq (qq (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁) X X= qq₁)
                       (⟦ A ⟧Ty X $ Aᵈ)
                       (⟦⟧Ty-ft A)
                       qq₁)
                     (ft-star ∙ qq₀)
                     qq₁)
                   (ft-star ∙ qq₀)
                   w₁
⟦subst3⟧Ty= refl X'= X''= A Aᵈ u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ = ! (⟦tsubst⟧Ty= A Aᵈ (((idMor _ , u) , v) , w) (⟦idMor+++⟧ᵈ refl X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁)) ∙ ap-irr-star (⟦idMor+++⟧= refl X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁) refl ∙ star-comp ∙ ap-irr-star refl star-comp

{-
Unused
⟦subst3⟧Tmᵈ : {X : Ob (suc (suc (suc n)))} {X' : Ob (suc (suc n))} (X= : ft X ≡ X') {X'' : Ob (suc n)} (X'= : ft X' ≡ X'') {X''' : Ob n} (X''= : ft X'' ≡ X''') (t : TmExpr (suc (suc (suc n))))
            → isDefined (⟦ t ⟧Tm X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X'''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X''' $ uᵈ) ≡ X'')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X'''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X''' $ vᵈ) ≡ star (⟦ u ⟧Tm X''' $ uᵈ) X' (u₁ ∙ ! X'=))
            → (w : TmExpr n)
            → (wᵈ : isDefined (⟦ w ⟧Tm X'''))
            → (w₁ : ∂₁ (⟦ w ⟧Tm X''' $ wᵈ) ≡ star (⟦ v ⟧Tm X''' $ vᵈ)
                                               (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' (u₁ ∙ ! X'=))
                                                  X
                                                  (qq₁ ∙ ! X=))
                                               (v₁ ∙ ! qq₀ ∙ ! ft-star))
            → isDefined (⟦ t [ ((idMor _ , u) , v) , w ]Tm ⟧Tm X''')
⟦subst3⟧Tmᵈ X= X'= X''= t tᵈ u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ = ⟦tsubst⟧Tmᵈ t tᵈ _ (⟦idMor+++⟧ᵈ X= X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁)

⟦subst3⟧Tm= : {X : Ob (suc (suc (suc n)))} {X' : Ob (suc (suc n))} (X= : ft X ≡ X') {X'' : Ob (suc n)} (X'= : ft X' ≡ X'') {X''' : Ob n} (X''= : ft X'' ≡ X''') (t : TmExpr (suc (suc (suc n))))
            → (tᵈ : isDefined (⟦ t ⟧Tm X))
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X'''))
            → (u₁ : ∂₁ (⟦ u ⟧Tm X''' $ uᵈ) ≡ X'')
            → (v : TmExpr n)
            → (vᵈ : isDefined (⟦ v ⟧Tm X'''))
            → (v₁ : ∂₁ (⟦ v ⟧Tm X''' $ vᵈ) ≡ star (⟦ u ⟧Tm X''' $ uᵈ) X' (u₁ ∙ ! X'=))
            → (w : TmExpr n)
            → (wᵈ : isDefined (⟦ w ⟧Tm X'''))
            → (w₁ : ∂₁ (⟦ w ⟧Tm X''' $ wᵈ) ≡ star (⟦ v ⟧Tm X''' $ vᵈ)
                                               (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' (u₁ ∙ ! X'=))
                                                  X
                                                  (qq₁ ∙ ! X=))
                                               (v₁ ∙ ! qq₀ ∙ ! ft-star))
            → ⟦ t [ ((idMor _ , u) , v) , w ]Tm ⟧Tm X''' $ ⟦subst3⟧Tmᵈ X= X'= X''= t tᵈ u uᵈ u₁ v vᵈ v₁ w wᵈ w₁
              ≡ starTm
                  (⟦ w ⟧Tm X''' $ wᵈ)
                  (starTm
                     (qq (⟦ v ⟧Tm X''' $ vᵈ) (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' (u₁ ∙ ! X'=)) X (qq₁ ∙ ! X=)) (v₁ ∙ ! qq₀ ∙ ! ft-star))
                     (starTm
                       (qq (qq (⟦ u ⟧Tm X''' $ uᵈ) (ft X) (u₁ ∙ ! (ap ft X= ∙ X'=))) X qq₁)
                       (⟦ t ⟧Tm X $ tᵈ)
                       (⟦⟧Tm₀ t ∙ ! qq₁))
                     (ss₀ ∙ comp₀ ∙ qq₀ ∙ ap2-irr star (ap2-irr qq refl X=) refl ∙ ! qq₁))
                   (ss₀ ∙ comp₀ ∙ qq₀ ∙ ! w₁)
⟦subst3⟧Tm= X= X'= X''= t tᵈ u uᵈ u₁ v vᵈ v₁ w wᵈ w₁ = ! (⟦tsubst⟧Tm= t tᵈ (((idMor _ , u) , v) , w) (⟦idMor+++⟧ᵈ X= X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁)) ∙ ap2-irr starTm (⟦idMor+++⟧= X= X'= X''= u uᵈ u₁ v vᵈ v₁ w wᵈ w₁) refl ∙ starTm-comp {p = comp₁ ∙ qq₁ ∙ {!!} ∙ ! qq₀} {!!} ∙ starTm-comp {p = {!!}} {!!}
-}
