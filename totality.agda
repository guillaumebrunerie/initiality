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

{- We start by stating the types of the main properties that we are going to prove by mutual induction

Unfortunately we cannot define ⟦weaken⟧ᵈ in terms of ⟦tsubst⟧ᵈ because ⟦tsubst⟧Ty+ᵈ calls
⟦weaken⟧Mor+ᵈ on δ, whereas the induction defining ⟦tsubst⟧Tyᵈ is on A.  There is no similar issue
defining ⟦weaken⟧ first (as there is no δ that would mess up the termination) and then ⟦tsubst⟧
(which uses ⟦weaken⟧ which is already defined).  -}

{- Totality of the partial interpretation functions -}

⟦⟧Tyᵈ  : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) → isDefined (⟦ A ⟧Ty (⟦ Γ ⟧Ctx $ Γᵈ))
⟦⟧Tmᵈ  : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → isDefined (⟦ u ⟧Tm (⟦ Γ ⟧Ctx $ Γᵈ))
⟦⟧Morᵈ : {Γ : Ctx n} {Δ : Ctx m} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (Δᵈ : isDefined (⟦ Δ ⟧Ctx)) {δ : Mor n m} (dδ : Γ ⊢ δ ∷> Δ) → isDefined (⟦ δ ⟧Mor (⟦ Γ ⟧Ctx $ Γᵈ) (⟦ Δ ⟧Ctx $ Δᵈ))

{- Interpretation of definitional equalities -}

⟦⟧TyEq : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A')) {Aᵈ : isDefined (⟦ A ⟧Ty X)} {A'ᵈ : isDefined (⟦ A' ⟧Ty X)}
       → ⟦ A ⟧Ty X $ Aᵈ ≡ ⟦ A' ⟧Ty X $ A'ᵈ
⟦⟧TmEq : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A)) {uᵈ : isDefined (⟦ u ⟧Tm X)} {u'ᵈ : isDefined (⟦ u' ⟧Tm X)}
       → ⟦ u ⟧Tm X $ uᵈ ≡ ⟦ u' ⟧Tm X $ u'ᵈ

{- Codomain of the interpretation of a derivable term -}

⟦⟧Tm₁ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {u : TmExpr n} {uᵈ : isDefined (⟦ u ⟧Tm X)} {A : TyExpr n} {Aᵈ : isDefined (⟦ A ⟧Ty X)} (du : Derivable (Γ ⊢ u :> A)) → ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ ⟦ A ⟧Ty X $ Aᵈ

{- Interpretation of weakening -}

⟦weaken⟧Tyᵈ' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob n} {Y : Ob (n -WeakPos k)} (A : TyExpr n)
             → isDefined (⟦ A ⟧Ty X)
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → isDefined (⟦ weakenTy' k A ⟧Ty Z)

⟦weaken⟧Tmᵈ' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr n)
             → isDefined (⟦ u ⟧Tm X)
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → isDefined (⟦ weakenTm' k u ⟧Tm Z)

⟦weaken⟧Ty=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob n} {Y : Ob (n -WeakPos k)} (A : TyExpr n)
             → (Aᵈ : isDefined (⟦ A ⟧Ty X))
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → star (qq^ k X+= X=) (⟦ A ⟧Ty X $ Aᵈ) (⟦⟧Ty-ft A) qq^₁ ≡ ⟦ weakenTy' k A ⟧Ty Z $ ⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z=

⟦weaken⟧Tm=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr n)
             → (uᵈ : isDefined (⟦ u ⟧Tm X))
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → starTm (qq^ k X+= X=) (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' k u ⟧Tm Z $ ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z=

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
            → star (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y $ Aᵈ) (⟦⟧Ty-ft A) (⟦⟧Mor₁ δ)
              ≡ ⟦ A [ δ ]Ty ⟧Ty X $ ⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ

⟦tsubst⟧Tm= : {X : Ob n} {Y : Ob m} (u : TmExpr m)
              (uᵈ : isDefined (⟦ u ⟧Tm Y))
              (δ : Mor n m)
              (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            → starTm (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ u ⟧Tm Y $ uᵈ) (⟦⟧Tm₀ u) (⟦⟧Mor₁ δ)
              ≡ ⟦ u [ δ ]Tm ⟧Tm X $ ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ



{- We now prove a ton of lemmas, mainly special cases of the properties above… -}

{- Type of a weakening -}

⟦weaken⟧Tm₁' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr n)
             → (uᵈ : isDefined (⟦ u ⟧Tm X))
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → {∂₁u : Ob (suc n)} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ ∂₁u)
             → ∂₁ (⟦ weakenTm' k u ⟧Tm Z $ ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z=) ≡ star (qq^ k X+= X=) ∂₁u (⟦⟧Tm₁-ft u u₁) qq^₁
⟦weaken⟧Tm₁' k u uᵈ X+= X= Y= u₁ = ap ∂₁ (! (⟦weaken⟧Tm=' k u uᵈ X+= X= Y=)) ∙ starTm₁ _ (⟦⟧Tm₁-ft u u₁) _ (⟦⟧Tmₛ u) u₁ qq^₁

{- Weakening at [last] -}

⟦weaken⟧Tyᵈ : {X+ : Ob (suc n)} {X : Ob n} (A : TyExpr n)
            → (Aᵈ : isDefined (⟦ A ⟧Ty X))
            → (X= : ft X+ ≡ X)
            → isDefined (⟦ weakenTy A ⟧Ty X+)
⟦weaken⟧Tyᵈ A Aᵈ X= = ⟦weaken⟧Tyᵈ' last A Aᵈ X= refl refl

⟦weaken⟧Ty= : {X+ : Ob (suc n)} {X : Ob n} (A : TyExpr n)
            → (Aᵈ : isDefined (⟦ A ⟧Ty X))
            → (X= : ft X+ ≡ X)
            → star (pp X+) (⟦ A ⟧Ty X $ Aᵈ) (⟦⟧Ty-ft A) (pp₁ ∙ X=) ≡ ⟦ weakenTy A ⟧Ty X+ $ ⟦weaken⟧Tyᵈ A Aᵈ X=
⟦weaken⟧Ty= A Aᵈ X= = ap-irr-star (! qq^last) refl ∙ ⟦weaken⟧Ty=' last A Aᵈ X= refl refl

⟦weaken⟧Tmᵈ : {X+ : Ob (suc n)} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ X)
            → isDefined (⟦ weakenTm u ⟧Tm X+)
⟦weaken⟧Tmᵈ u uᵈ X= = ⟦weaken⟧Tmᵈ' last u uᵈ X= refl refl

⟦weaken⟧Tm= : {X+ : Ob (suc n)} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ X)
            → starTm (pp X+) (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) (pp₁ ∙ X=) ≡ ⟦ weakenTm u ⟧Tm X+ $ ⟦weaken⟧Tmᵈ u uᵈ X=
⟦weaken⟧Tm= u uᵈ X= = ap-irr-starTm (! qq^last) refl ∙ ⟦weaken⟧Tm=' last u uᵈ X= refl refl

⟦weaken⟧Tm₁ : {X+ : Ob (suc n)} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ X)
            → {∂₁u : Ob (suc n)} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ ∂₁u)
            → ∂₁ (⟦ weakenTm u ⟧Tm X+ $ ⟦weaken⟧Tmᵈ u uᵈ X=) ≡ star (pp X+) ∂₁u (⟦⟧Tm₁-ft u u₁) (pp₁ ∙ X=)
⟦weaken⟧Tm₁ u uᵈ X= refl = ⟦weaken⟧Tm₁' last u uᵈ X= refl refl refl ∙ ap3-irr2 star qq^last refl refl

{- Weakening at [prev k] -}

⟦weaken⟧Ty+ᵈ' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -WeakPos k)} (A : TyExpr (suc n))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (X'= : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' X'= qq^₁ ≡ Z)
              → isDefined (⟦ weakenTy' (prev k) A ⟧Ty Z)
⟦weaken⟧Ty+ᵈ' k A Aᵈ X+= X= refl Y= = ⟦weaken⟧Tyᵈ' (prev k) A Aᵈ X+= X= Y=

⟦weaken⟧Ty+=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -WeakPos k)} (A : TyExpr (suc n))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
              → star+ (qq^ k X+= X=) (⟦ A ⟧Ty X' $ Aᵈ) (⟦⟧Ty-ft A) p qq^₁ ≡ ⟦ weakenTy' (prev k) A ⟧Ty Z $ ⟦weaken⟧Ty+ᵈ' k A Aᵈ X+= X= p Y=
⟦weaken⟧Ty+=' k A Aᵈ X+= X= refl Y= = ap-irr-star (! qq^prev) refl ∙ ⟦weaken⟧Ty=' (prev k) A Aᵈ X+= X= Y=

⟦weaken⟧Tm+ᵈ' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
              → isDefined (⟦ weakenTm' (prev k) u ⟧Tm Z)
⟦weaken⟧Tm+ᵈ' k u uᵈ X+= X= refl Y= = ⟦weaken⟧Tmᵈ' (prev k) u uᵈ X+= X= Y=

⟦weaken⟧Tm+=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
              → starTm+ (qq^ k X+= X=) p (⟦ u ⟧Tm X' $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' (prev k) u ⟧Tm Z $ ⟦weaken⟧Tm+ᵈ' k u uᵈ X+= X= p Y=
⟦weaken⟧Tm+=' k u uᵈ X+= X= refl Y= = ap ss (ap-irr-comp refl (! qq^prev)) ∙ ⟦weaken⟧Tm=' (prev k) u uᵈ X+= X= Y=

⟦weaken⟧Tm+₁' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X+= : ft X+ ≡ Y) (X''= : ft^ k X'' ≡ Y) {Z : Ob (suc (suc n))}
              → (X= : ft X ≡ X')
              → (X'= : ft X' ≡ X'')
              → (Z= : star (qq^ k X+= X''=) X' X'= qq^₁ ≡ Z)
              → (u₁ : ∂₁ (⟦ u ⟧Tm X' $ uᵈ) ≡ X)
              → ∂₁ (⟦ weakenTm' (prev k) u ⟧Tm Z $ ⟦weaken⟧Tm+ᵈ' k u uᵈ X+= X''= X'= Z=) ≡ star+ (qq^ k X+= X''=) X X= X'= qq^₁
⟦weaken⟧Tm+₁' k u uᵈ X+= X''= refl refl Z= u₁ = ⟦weaken⟧Tm₁' (prev k) u uᵈ X+= X''= Z= u₁ ∙ ap-irr-star qq^prev refl

{- Weakening at [prev (prev k)] -}

⟦weaken⟧Tm++ᵈ' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {Y : Ob (n -WeakPos k)} {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} (u : TmExpr (suc (suc n)))
               → (uᵈ : isDefined (⟦ u ⟧Tm X))
               → (X+= : ft X+ ≡ Y) (X''= : ft^ k X'' ≡ Y) {Z : Ob (suc (suc (suc n)))} (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (Y= : star+ (qq^ k X+= X''=) X X= X'= qq^₁ ≡ Z)
               → isDefined (⟦ weakenTm' (prev (prev k)) u ⟧Tm Z)
⟦weaken⟧Tm++ᵈ' k u uᵈ X+= X''= refl refl Y= = ⟦weaken⟧Tm+ᵈ' (prev k) u uᵈ X+= X''= refl (ap-irr-star qq^prev refl ∙ Y=)

⟦weaken⟧Tm++=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {Y : Ob (n -WeakPos k)} {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} (u : TmExpr (suc (suc n)))
               → (uᵈ : isDefined (⟦ u ⟧Tm X))
               → (X+= : ft X+ ≡ Y) (X''= : ft^ k X'' ≡ Y) {Z : Ob (suc (suc (suc n)))} (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (Y= : star+ (qq^ k X+= X''=) X X= X'= qq^₁ ≡ Z)
               → starTm++ (qq^ k X+= X''=) X= X'= (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' (prev (prev k)) u ⟧Tm Z $ ⟦weaken⟧Tm++ᵈ' k u uᵈ X+= X''= X= X'= Y=
⟦weaken⟧Tm++=' k u uᵈ X+= X''= refl refl Y= = ap ss (ap-irr-comp refl (ap-irr-qq (! qq^prev) refl)) ∙ ⟦weaken⟧Tm+=' (prev k) u uᵈ X+= X''= refl (ap-irr-star qq^prev refl ∙ Y=)

⟦weaken⟧Tm++₁' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {Y : Ob (n -WeakPos k)} {X : Ob (suc (suc (suc n))) } {X' : Ob (suc (suc n))} {X'' : Ob (suc n)} {X''' : Ob n} (u : TmExpr (suc (suc n)))
               → (uᵈ : isDefined (⟦ u ⟧Tm X'))
               → (X+= : ft X+ ≡ Y) (X'''= : ft^ k X''' ≡ Y) {Z : Ob (suc (suc (suc n)))}
               → (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (X''= : ft X'' ≡ X''')
               → (Z= : star+ (qq^ k X+= X'''=) X' X'= X''= qq^₁ ≡ Z)
               → (u₁ : ∂₁ (⟦ u ⟧Tm X' $ uᵈ) ≡ X)
               → ∂₁ (⟦ weakenTm' (prev (prev k)) u ⟧Tm Z $ ⟦weaken⟧Tm++ᵈ' k u uᵈ X+= X'''= X'= X''= Z=) ≡ star++ (qq^ k X+= X'''=) X X= X'= X''= qq^₁
⟦weaken⟧Tm++₁' k u uᵈ X+= X'''= refl refl refl Y= u₁ = ⟦weaken⟧Tm+₁' (prev k) u uᵈ X+= X'''= refl refl (ap-irr-star qq^prev refl ∙ Y=) u₁ ∙ ap-irr-star (ap-irr-qq qq^prev refl) refl

{- Weakening at [prev (prev (prev k))] -}

⟦weaken⟧Ty+++ᵈ' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {Y : Ob (n -WeakPos k)} {X''' : Ob (suc (suc (suc n)))} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc (suc n))))
                → (Aᵈ : isDefined (⟦ A ⟧Ty X'''))
                → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc (suc (suc n))))} (X'''= : ft X''' ≡ X'') (X''= : ft X'' ≡ X') (X'= : ft X' ≡ X) (Z= : star++ (qq^ k X+= X=)  X''' X'''= X''= X'= qq^₁ ≡ Z)
               → isDefined (⟦ weakenTy' (prev (prev (prev k))) A ⟧Ty Z)
⟦weaken⟧Ty+++ᵈ' k A Aᵈ X+= X= refl refl refl Z= = ⟦weaken⟧Tyᵈ' (prev (prev (prev k))) A Aᵈ X+= X= (ap-irr-star (qq^prev ∙ ap-irr-qq qq^prev refl) refl ∙ Z=)

⟦weaken⟧Ty+++=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {Y : Ob (n -WeakPos k)} {X''' : Ob (suc (suc (suc n)))} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc (suc n))))
                → (Aᵈ : isDefined (⟦ A ⟧Ty X'''))
                → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc (suc (suc n))))} (X'''= : ft X''' ≡ X'') (X''= : ft X'' ≡ X') (X'= : ft X' ≡ X) (Z= : star++ (qq^ k X+= X=)  X''' X'''= X''= X'= qq^₁ ≡ Z)
               → star+++ (qq^ k X+= X=) (⟦ A ⟧Ty X''' $ Aᵈ) (⟦⟧Ty-ft A) X'''= X''= X'= qq^₁ ≡ ⟦ weakenTy' (prev (prev (prev k))) A ⟧Ty Z $ ⟦weaken⟧Ty+++ᵈ' k A Aᵈ X+= X= X'''= X''= X'= Z=
⟦weaken⟧Ty+++=' k A Aᵈ X+= X= refl refl refl Z= = ap-irr-star (! (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq qq^prev refl) refl)) refl ∙ ⟦weaken⟧Ty=' (prev (prev (prev k))) A Aᵈ X+= X= (ap-irr-star (qq^prev ∙ ap-irr-qq qq^prev refl) refl ∙ Z=)

{- Weakening at [prev last] -}

⟦weaken⟧Ty+ᵈ : {X+ : Ob (suc n)} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc n))
             → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
             → (X= : ft X+ ≡ X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (pp X+) X' p (pp₁ ∙ X=) ≡ Y)
             → isDefined (⟦ weakenTy' (prev last) A ⟧Ty Y)
⟦weaken⟧Ty+ᵈ A Aᵈ X= p Y= = ⟦weaken⟧Ty+ᵈ' last A Aᵈ X= refl p (ap-irr-star qq^last refl ∙ Y=)

⟦weaken⟧Ty+= : {X+ : Ob (suc n)} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc n))
             → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
             → (X= : ft X+ ≡ X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (pp X+) X' p (pp₁ ∙ X=) ≡ Y)
             → star (qq (pp X+) X' p (pp₁ ∙ X=)) (⟦ A ⟧Ty X' $ Aᵈ) (⟦⟧Ty-ft A) qq₁ ≡ ⟦ weakenTy' (prev last) A ⟧Ty Y $ ⟦weaken⟧Ty+ᵈ A Aᵈ X= p Y=
⟦weaken⟧Ty+= A Aᵈ X= refl Y= = ap-irr-star (ap-irr-qq (! qq^last) refl) refl ∙ ⟦weaken⟧Ty+=' last A Aᵈ X= refl refl (ap-irr-star qq^last refl ∙ Y=)

{- Weakening at [prev (prev last)] -}

⟦weaken⟧Ty++ᵈ : {X+ : Ob (suc n)} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc n)))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X''))
              → (X= : ft X+ ≡ X) {Y : Ob (suc (suc (suc n)))} (p : ft X'' ≡ X') (p' : ft X' ≡ X) (Y= : star (qq (pp X+) X' p' (pp₁ ∙ X=)) X'' p qq₁ ≡ Y)
              → isDefined (⟦ weakenTy' (prev (prev last)) A ⟧Ty Y)
⟦weaken⟧Ty++ᵈ A Aᵈ X= refl refl Y= = ⟦weaken⟧Tyᵈ' (prev (prev last)) A Aᵈ X= refl (ap-irr-star (qq^prev ∙ ap-irr-qq qq^last refl) refl ∙ Y=)

⟦weaken⟧Ty++= : {X+ : Ob (suc n)} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc n)))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X''))
              → (X= : ft X+ ≡ X) {Y : Ob (suc (suc (suc n)))} (p : ft X'' ≡ X') (p' : ft X' ≡ X) (Y= : star (qq (pp X+) X' p' (pp₁ ∙ X=)) X'' p qq₁ ≡ Y)
              → star (qq (qq (pp X+) X' p' (pp₁ ∙ X=)) X'' p qq₁) (⟦ A ⟧Ty X'' $ Aᵈ) (⟦⟧Ty-ft A) qq₁ ≡ ⟦ weakenTy' (prev (prev last)) A ⟧Ty Y $ ⟦weaken⟧Ty++ᵈ A Aᵈ X= p p' Y=
⟦weaken⟧Ty++= A Aᵈ X= refl refl Y= = ap-irr-star (ap-irr-qq (ap-irr-qq (! qq^last) refl ∙ ! qq^prev) refl ∙ ! qq^prev) refl ∙ ⟦weaken⟧Ty=' (prev (prev last)) A Aᵈ X= refl (ap-irr-star (qq^prev ∙ ap-irr-qq qq^last refl) refl ∙ Y=)

{- Weakening at [prev (prev (prev last))] -}

⟦weaken⟧Ty+++ᵈ : {X+ : Ob (suc n)} {X''' : Ob (suc (suc (suc n)))} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc (suc n))))
               → (Aᵈ : isDefined (⟦ A ⟧Ty X'''))
               → (X= : ft X+ ≡ X) {Y : Ob (suc (suc (suc (suc n))))} (p : ft X''' ≡ X'') (p' : ft X'' ≡ X') (p'' : ft X' ≡ X) (Y= : star (qq (qq (pp X+) X' p'' (pp₁ ∙ X=)) X'' p' qq₁) X''' p qq₁ ≡ Y)
               → isDefined (⟦ weakenTy' (prev (prev (prev last))) A ⟧Ty Y)
⟦weaken⟧Ty+++ᵈ A Aᵈ X= refl refl refl Y= = ⟦weaken⟧Tyᵈ' (prev (prev (prev last))) A Aᵈ X= refl (ap-irr-star (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq qq^last refl) refl) refl ∙ Y=)

⟦weaken⟧Ty+++= : {X+ : Ob (suc n)} {X''' : Ob (suc (suc (suc n)))} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc (suc n))))
               → (Aᵈ : isDefined (⟦ A ⟧Ty X'''))
               → (X= : ft X+ ≡ X) {Y : Ob (suc (suc (suc (suc n))))} (p : ft X''' ≡ X'') (p' : ft X'' ≡ X') (p'' : ft X' ≡ X) (Y= : star (qq (qq (pp X+) X' p'' (pp₁ ∙ X=)) X'' p' qq₁) X''' p qq₁ ≡ Y)
               → star (qq (qq (qq (pp X+) X' p'' (pp₁ ∙ X=)) X'' p' qq₁) X''' p qq₁) (⟦ A ⟧Ty X''' $ Aᵈ) (⟦⟧Ty-ft A) qq₁ ≡ ⟦ weakenTy' (prev (prev (prev last))) A ⟧Ty Y $ ⟦weaken⟧Ty+++ᵈ A Aᵈ X= p p' p'' Y=
⟦weaken⟧Ty+++= A Aᵈ X= refl refl refl Y= = ! (ap-irr-star (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq qq^last refl) refl) refl) refl) ∙ ⟦weaken⟧Ty=' (prev (prev (prev last))) A Aᵈ X= refl (ap-irr-star (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq qq^last refl) refl) refl ∙ Y=)

{- Weakening of morphisms -}

⟦weaken⟧Morᵈ : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y : Ob m} (δ : Mor n m)
           → isDefined (⟦ δ ⟧Mor X Y)
           → isDefined (⟦ weakenMor δ ⟧Mor X+ Y)
⟦weaken⟧Mor= : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y : Ob m} (δ : Mor n m)
           → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
           → ⟦ weakenMor δ ⟧Mor X+ Y $ ⟦weaken⟧Morᵈ X= δ δᵈ ≡ comp (⟦ δ ⟧Mor X Y $ δᵈ) (pp X+) (⟦⟧Mor₀ δ ∙ ! X=) pp₁

⟦weaken⟧Morᵈ refl ◇ tt = tt
⟦weaken⟧Morᵈ {X+ = X+} refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = (⟦weaken⟧Morᵈ refl δ δᵈ , ⟦weaken⟧Tmᵈ u uᵈ refl , ⟦⟧Mor₁ (weakenMor δ) , (⟦weaken⟧Tm₁ u uᵈ refl u₁ ∙ ! star-comp ∙ ! (ap3-irr2 star (⟦weaken⟧Mor= refl δ δᵈ) refl refl)) , tt)

⟦weaken⟧Mor= refl ◇ tt = ! (ptmor-unique _ _ (comp₀ ∙ pp₀) (comp₁ ∙ pt-unique _))
⟦weaken⟧Mor= refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) =
  ap-irr-comp
    (ap-irr-qq
      (⟦weaken⟧Mor= refl δ δᵈ)
      refl
     ∙ qq-comp
     ∙ ap-irr-comp refl
       ((ap-irr-qq (! (ap-irr-comp (is-section= (ft-star ∙ ⟦⟧Mor₀ δ) (⟦⟧Tmₛ u) u₁) refl ∙ id-right pp₁) ∙ assoc) refl)))
    (! (⟦weaken⟧Tm= u uᵈ refl))
  ∙ assoc {g₁ = qq₁} {h₀ = qq₀}
  ∙ ! (ap-irr-comp refl (ss-qq {f₁ = comp₁ ∙ u₁}))
  ∙ ! assoc

⟦weaken⟧Mor+ᵈ : {Z : Ob (suc n)} {X : Ob n} {Y' : Ob (suc m)} {Y : Ob m}
                (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'= : ft Y' ≡ Y) 
              → (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → isDefined (⟦ weakenMor+ δ ⟧Mor Z Y')
⟦weaken⟧Mor+ᵈ δ δᵈ refl Z= = (⟦weaken⟧Morᵈ (ap ft (! Z=) ∙ ft-star ∙ ⟦⟧Mor₀ δ) δ δᵈ , (tt , (⟦⟧Mor₁ (weakenMor δ) , (varCL₁ {X= = refl} ∙ ap-irr-star refl (! Z=) ∙ ! star-comp ∙ ap-irr-star (! (⟦weaken⟧Mor= (ap ft (! Z=) ∙ ft-star ∙ ⟦⟧Mor₀ δ) δ δᵈ)) refl) , tt)))

⟦weaken⟧Mor+= : {Z : Ob (suc n)} {X : Ob n} {Y' : Ob (suc m)} {Y : Ob m}
                (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'= : ft Y' ≡ Y) 
              → (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → ⟦ weakenMor+ δ ⟧Mor Z Y' $ ⟦weaken⟧Mor+ᵈ δ δᵈ Y'= Z= ≡ qq (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ)
⟦weaken⟧Mor+= δ δᵈ refl Z= = ap-irr-comp (ap-irr-qq (⟦weaken⟧Mor= (ap ft (! Z=) ∙ ft-star ∙ ⟦⟧Mor₀ δ) δ δᵈ ∙ refl) refl ∙ qq-comp) refl {f₁' = varCL₁ {X= = refl}} ∙ assoc {g₀ = qq₀ ∙ ap-irr-star refl Z=} ∙ ap-irr-comp refl (ap-irr-comp (ap-irr-qq (! (id-left pp₀)) Z=) refl ∙ (! ss-qq)) ∙ id-left (qq₀ ∙ Z=)


{- Type of a substitution -}

⟦tsubst⟧Tm₁ : {Z : Ob (suc m)} {X : Ob n} {Y : Ob m} (u : TmExpr m)
            → (uᵈ : isDefined (⟦ u ⟧Tm Y)) (u₁ : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ Z)
            → (δ : Mor n m)
            → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))            
            → ∂₁ (⟦ u [ δ ]Tm ⟧Tm X $ ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ)
              ≡ star (⟦ δ ⟧Mor X Y $ δᵈ) Z (⟦⟧Tm₁-ft u u₁) (⟦⟧Mor₁ δ)
⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ = ap ∂₁ (! (⟦tsubst⟧Tm= u uᵈ δ δᵈ)) ∙ starTm₁ _ (⟦⟧Tm₁-ft u u₁) _ (⟦⟧Tmₛ u) u₁ (⟦⟧Mor₁ δ)

{- Substitution by a weakenMor+ -}

⟦tsubst⟧Ty+ᵈ : {Z : Ob (suc n)} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} (A : TyExpr (suc m)) (Aᵈ : isDefined (⟦ A ⟧Ty Y'))
               (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'= : ft Y' ≡ Y)
               (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
             → isDefined (⟦ A [ weakenMor+ δ ]Ty ⟧Ty Z)
⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ Y'= Z= = ⟦tsubst⟧Tyᵈ A Aᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= Z=)

⟦tsubst⟧Ty++ᵈ : {Z : Ob (suc (suc n))} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} {Y'' : Ob (suc (suc m))} (A : TyExpr (suc (suc m))) (Aᵈ : isDefined (⟦ A ⟧Ty Y''))
                (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
                (Z= : star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → isDefined (⟦ A [ weakenMor+ (weakenMor+ δ) ]Ty ⟧Ty Z)
⟦tsubst⟧Ty++ᵈ A Aᵈ δ δᵈ Y''= Y'= Z= = ⟦tsubst⟧Ty+ᵈ A Aᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) Y''= ((ap-irr-star (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) refl) ∙ Z=)

⟦tsubst⟧Ty+++ᵈ : {Z : Ob (suc (suc (suc n)))} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} {Y'' : Ob (suc (suc m))} {Y''' : Ob (suc (suc (suc m)))} (A : TyExpr (suc (suc (suc m)))) (Aᵈ : isDefined (⟦ A ⟧Ty Y'''))
                 (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'''= : ft Y''' ≡ Y'') (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
                 (Z= : star++ (⟦ δ ⟧Mor X Y $ δᵈ) Y''' Y'''= Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
               → isDefined (⟦ A [ weakenMor+ (weakenMor+ (weakenMor+ δ)) ]Ty ⟧Ty Z)
⟦tsubst⟧Ty+++ᵈ A Aᵈ δ δᵈ Y'''= Y''= Y'= Z= = ⟦tsubst⟧Ty++ᵈ A Aᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=))) Y'''= Y''= (ap-irr-star (ap-irr-qq (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=))) refl) refl ∙ Z=)


⟦tsubst⟧Ty+= : {Z : Ob (suc n)} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} (A : TyExpr (suc m)) (Aᵈ : isDefined (⟦ A ⟧Ty Y'))
               (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'= : ft Y' ≡ Y)
               (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
             → star+ (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y' $ Aᵈ) (⟦⟧Ty-ft A) Y'= (⟦⟧Mor₁ δ)
               ≡ ⟦ A [ weakenMor+ δ ]Ty ⟧Ty Z $ ⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ Y'= Z=
⟦tsubst⟧Ty+= A Aᵈ δ δᵈ Y'= Z= = ap-irr-star (! (⟦weaken⟧Mor+= δ δᵈ Y'= Z=)) refl ∙ ⟦tsubst⟧Ty= A Aᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= Z=)

⟦tsubst⟧Ty++= : {Z : Ob (suc (suc n))} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} {Y'' : Ob (suc (suc m))} (A : TyExpr (suc (suc m))) (Aᵈ : isDefined (⟦ A ⟧Ty Y''))
               (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
               (Z= : star+ (⟦ δ ⟧Mor X Y $ δᵈ) Y'' Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
               → star++ (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y'' $ Aᵈ) (⟦⟧Ty-ft A) Y''= Y'= (⟦⟧Mor₁ δ)
                 ≡ ⟦ A [ weakenMor+ (weakenMor+ δ) ]Ty ⟧Ty Z $ ⟦tsubst⟧Ty++ᵈ A Aᵈ δ δᵈ Y''= Y'= Z=
⟦tsubst⟧Ty++= A Aᵈ δ δᵈ Y''= Y'= Z= = ap-irr-star (ap-irr-qq (! (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=))) refl) refl ∙ ⟦tsubst⟧Ty+= A Aᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) Y''= (ap-irr-star (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ft-star ∙ qq₀) ∙ ap ft Z=)) refl ∙ Z=) 

⟦tsubst⟧Ty+++= : {Z : Ob (suc (suc (suc n)))} {X : Ob n} {Y : Ob m} {Y' : Ob (suc m)} {Y'' : Ob (suc (suc m))} {Y''' : Ob (suc (suc (suc m)))} (A : TyExpr (suc (suc (suc m)))) (Aᵈ : isDefined (⟦ A ⟧Ty Y'''))
                 (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'''= : ft Y''' ≡ Y'') (Y''= : ft Y'' ≡ Y') (Y'= : ft Y' ≡ Y)
                 (Z= : star++ (⟦ δ ⟧Mor X Y $ δᵈ) Y''' Y'''= Y''= Y'= (⟦⟧Mor₁ δ) ≡ Z)
                 → star+++ (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y''' $ Aᵈ) (⟦⟧Ty-ft A) Y'''= Y''= Y'= (⟦⟧Mor₁ δ)
                   ≡ ⟦ A [ weakenMor+ (weakenMor+ (weakenMor+ δ)) ]Ty ⟧Ty Z $ ⟦tsubst⟧Ty+++ᵈ A Aᵈ δ δᵈ Y'''= Y''= Y'= Z=
⟦tsubst⟧Ty+++= A Aᵈ δ δᵈ Y'''= Y''= Y'= Z= = ap-irr-star (ap-irr-qq (ap-irr-qq (! (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=)))) refl) refl) refl ∙ ⟦tsubst⟧Ty++= A Aᵈ (weakenMor+ δ) (⟦weaken⟧Mor+ᵈ δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=))) Y'''= Y''= (ap-irr-star (ap-irr-qq (⟦weaken⟧Mor+= δ δᵈ Y'= (! (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ qq₀) ∙ ap ft (ap ft Z=))) refl) refl ∙ Z=)


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
            → ⟦ idMor n , u ⟧Mor X Y $ idMor+⟧ᵈ p u uᵈ u₁ ≡ ⟦ u ⟧Tm X $ uᵈ
⟦idMor+⟧= refl u uᵈ u₁ =
  ap-irr-comp (ap-irr-qq (⟦idMor⟧= refl) refl ∙ qq-id {p = refl}) refl ∙ id-right u₁

⟦subst⟧Tyᵈ : {X : Ob (suc n)} {Y : Ob n} (B : TyExpr (suc n))
           → isDefined (⟦ B ⟧Ty X)
           → (u : TmExpr n)
           → (uᵈ : isDefined (⟦ u ⟧Tm Y))
           → (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
           → isDefined (⟦ substTy B u ⟧Ty Y)
⟦subst⟧Tyᵈ B Bᵈ u uᵈ q = ⟦tsubst⟧Tyᵈ B Bᵈ _ (idMor+⟧ᵈ (ap ft (! q) ∙ ⟦⟧Tm₁-ft u refl) u uᵈ q)

⟦subst⟧Tmᵈ : {X : Ob (suc n)} {Y : Ob n} (v : TmExpr (suc n))
            → isDefined (⟦ v ⟧Tm X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm Y))
            → (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → isDefined (⟦ substTm v u ⟧Tm Y)
⟦subst⟧Tmᵈ v vᵈ u uᵈ q = ⟦tsubst⟧Tmᵈ v vᵈ _ (idMor+⟧ᵈ (ap ft (! q) ∙ ⟦⟧Tm₁-ft u refl) u uᵈ q)

⟦subst⟧Ty= : {X : Ob (suc n)} {Y : Ob n} (B : TyExpr (suc n))
             (Bᵈ : isDefined (⟦ B ⟧Ty X))
             (u : TmExpr n)
             (uᵈ : isDefined (⟦ u ⟧Tm Y))
             (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → ⟦ substTy B u ⟧Ty Y $ ⟦subst⟧Tyᵈ B Bᵈ u uᵈ q ≡ star (⟦ u ⟧Tm Y $ uᵈ) (⟦ B ⟧Ty X $ Bᵈ) (⟦⟧Ty-ft B) q
⟦subst⟧Ty= B Bᵈ u uᵈ q = ! (⟦tsubst⟧Ty= B Bᵈ _ (idMor+⟧ᵈ (ap ft (! q) ∙ ⟦⟧Tm₁-ft u refl) u uᵈ q)) ∙ ap-irr-star (idMor+⟧= (ap ft (! q) ∙ ⟦⟧Tm₁-ft u refl) u uᵈ q) refl

⟦subst⟧Tm= : {X : Ob (suc n)} {Y : Ob n} (v : TmExpr (suc n))
             (vᵈ : isDefined (⟦ v ⟧Tm X))
             (u : TmExpr n)
             (uᵈ : isDefined (⟦ u ⟧Tm Y))
             (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → ⟦ substTm v u ⟧Tm Y $ ⟦subst⟧Tmᵈ v vᵈ u uᵈ q ≡ starTm (⟦ u ⟧Tm Y $ uᵈ) (⟦ v ⟧Tm X $ vᵈ) (⟦⟧Tm₀ v) q
⟦subst⟧Tm= v vᵈ u uᵈ q = ! (⟦tsubst⟧Tm= v vᵈ _ (idMor+⟧ᵈ (ap ft (! q) ∙ ⟦⟧Tm₁-ft u refl) u uᵈ q)) ∙ ap-irr-starTm (idMor+⟧= (ap ft (! q) ∙ ⟦⟧Tm₁-ft u refl) u uᵈ q) refl

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

{- More stuff -}

cong⟦⟧Tyᵈ : {X Y : Ob n} {A : TyExpr n} → X ≡ Y → isDefined (⟦ A ⟧Ty Y) → isDefined (⟦ A ⟧Ty X)
cong⟦⟧Tyᵈ refl Aᵈ = Aᵈ

cong⟦⟧TyEq : {X Y : Ob n} {A : TyExpr n} (p : X ≡ Y) (w₁ : _) → ⟦ A ⟧Ty Y $ w₁ ≡ ⟦ A ⟧Ty X $ (cong⟦⟧Tyᵈ {A = A} p w₁)
cong⟦⟧TyEq refl _ = refl

cong⟦⟧Mor : {X : Ob n} {Y Y' : Ob m} {δ : Mor n m} → Y ≡ Y' → isDefined (⟦ δ ⟧Mor X Y) → isDefined (⟦ δ ⟧Mor X Y')
cong⟦⟧Mor refl δᵈ = δᵈ

⟦⟧TyEq+ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {X' : Ob n} {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A'))
          {Aᵈ : isDefined (⟦ A ⟧Ty X)} {A'ᵈ : isDefined (⟦ A' ⟧Ty X')} → X ≡ X' → ⟦ A ⟧Ty X $ Aᵈ ≡ ⟦ A' ⟧Ty X' $ A'ᵈ
⟦⟧TyEq+ Γᵈ dA= refl = ⟦⟧TyEq Γᵈ dA=

⟦⟧TmEq+ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {X' : Ob n} {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A))
          {uᵈ : isDefined (⟦ u ⟧Tm X)} {u'ᵈ : isDefined (⟦ u' ⟧Tm X')} → X ≡ X' → ⟦ u ⟧Tm X $ uᵈ ≡ ⟦ u' ⟧Tm X' $ u'ᵈ
⟦⟧TmEq+ Γᵈ du= refl = ⟦⟧TmEq Γᵈ du=


{- We can now finally define our main properties -}

⟦⟧Tyᵈ Γᵈ UU = tt
⟦⟧Tyᵈ Γᵈ {A = el i v} (El dv) =
  (⟦⟧Tmᵈ Γᵈ dv ,
   ⟦⟧Tmₛ v ,
   ⟦⟧Tm₁ Γᵈ dv , tt)
⟦⟧Tyᵈ Γᵈ {A = sum A B} (Sum dA dB) =
  (⟦⟧Tyᵈ Γᵈ dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ Γᵈ dB ,
   ⟦⟧Ty-ft B , tt)
⟦⟧Tyᵈ Γᵈ {A = pi A B} (Pi dA dB) =
  (Aᵈ ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB ,
   ⟦⟧Ty-ft B , tt)
  where Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
⟦⟧Tyᵈ Γᵈ {A = sig A B} (Sig dA dB) =
  (Aᵈ ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB ,
   ⟦⟧Ty-ft B , tt)
  where
    Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
⟦⟧Tyᵈ Γᵈ Empty = tt
⟦⟧Tyᵈ Γᵈ Unit = tt
⟦⟧Tyᵈ Γᵈ Nat = tt
⟦⟧Tyᵈ Γᵈ {A = id A a b} (Id dA da db) =
  (⟦⟧Tyᵈ Γᵈ dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da ,
   ⟦⟧Tmᵈ Γᵈ db ,
   ⟦⟧Tmₛ b ,
   ⟦⟧Tm₁ Γᵈ db , tt)

⟦⟧Tmᵈ Γᵈ (VarLast _) = tt
⟦⟧Tmᵈ Γᵈ (VarPrev _ _) = tt
⟦⟧Tmᵈ Γᵈ (Conv dA du dA=) = ⟦⟧Tmᵈ Γᵈ du

⟦⟧Tmᵈ Γᵈ {u = uu i} UUUU = tt

⟦⟧Tmᵈ Γᵈ {u = sum i a b} (SumUU da db) =
  (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)
    where
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da
      bᵈ = ⟦⟧Tmᵈ Γᵈ db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ Γᵈ db
⟦⟧Tmᵈ Γᵈ {u = inl A B a} (Inl dA dB da) =
   (Aᵈ , ⟦⟧Ty-ft A , Bᵈ , ⟦⟧Ty-ft B , aᵈ , aₛ , a₁ , tt)
     where
       Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
       Bᵈ = ⟦⟧Tyᵈ Γᵈ dB
       aᵈ = ⟦⟧Tmᵈ Γᵈ da
       aₛ = ⟦⟧Tmₛ a
       a₁ = ⟦⟧Tm₁ Γᵈ da
⟦⟧Tmᵈ Γᵈ {u = inr A B b} (Inr dA dB db) =
   (Aᵈ , ⟦⟧Ty-ft A , Bᵈ , ⟦⟧Ty-ft B , bᵈ , bₛ , b₁ , tt)
     where
       Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
       Bᵈ = ⟦⟧Tyᵈ Γᵈ dB
       bᵈ = ⟦⟧Tmᵈ Γᵈ db
       bₛ = ⟦⟧Tmₛ b
       b₁ = ⟦⟧Tm₁ Γᵈ db
⟦⟧Tmᵈ {Γ = Γ} Γᵈ {u = match A B C da db u} (Match dA dB dC dda ddb du) =
  (Aᵈ , A= , Bᵈ , B= , Cᵈ , ⟦⟧Ty-ft C , daᵈ , daₛ , da₁ , dbᵈ , dbₛ , db₁ , uᵈ , uₛ , u₁ , tt)
    where
      [Γ] = ⟦ Γ ⟧Ctx $ Γᵈ

      Aᵈ : isDefined (⟦ A ⟧Ty [Γ])
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      [A] = ⟦ A ⟧Ty [Γ] $ Aᵈ
      A= = ⟦⟧Ty-ft A

      Bᵈ : isDefined (⟦ B ⟧Ty [Γ])
      Bᵈ = ⟦⟧Tyᵈ Γᵈ dB
      [B] = ⟦ B ⟧Ty [Γ] $ Bᵈ
      B= = ⟦⟧Ty-ft B

      SumABᵈ : isDefined (⟦ sum  A B ⟧Ty [Γ])
      SumABᵈ = (Aᵈ , ⟦⟧Ty-ft A , Bᵈ , ⟦⟧Ty-ft B , tt)
      [SumAB] = ⟦ sum A B ⟧Ty [Γ] $ SumABᵈ
      SumAB-ft = ⟦⟧Ty-ft (sum A B) {Aᵈ = SumABᵈ}

      Cᵈ : isDefined (⟦ C ⟧Ty [SumAB])
      Cᵈ = ⟦⟧Tyᵈ (Γᵈ , SumABᵈ , tt) dC
      [C] = ⟦ C ⟧Ty [SumAB] $ Cᵈ
      C= = ⟦⟧Ty-ft C {Aᵈ = Cᵈ}

      daᵈ = ⟦⟧Tmᵈ (Γᵈ , Aᵈ , tt) dda
      daₛ = ⟦⟧Tmₛ da
      da₁ = ⟦⟧Tm₁ (Γᵈ , Aᵈ , tt) dda ∙ substAwCinla=
          where substAwCinla= : ⟦ substTy (weakenTy' (prev last) C) (inl (weakenTy A) (weakenTy B) (var last)) ⟧Ty  [A] $ _
                              ≡ T-da₁ _ [A] A= [B] B= [C] C=
                substAwCinla= = ⟦subst⟧Ty= (weakenTy' (prev last) C)
                                           AwCᵈ
                                           (inl (weakenTy A) (weakenTy B) (var last))
                                           inlwAwBlastᵈ
                                           inlwAwBlast₁
                                ∙ ! (ap-irr-star (ap-irr-inlStr refl AwA= AwB= refl) AwC=) 
                              where AwSumABᵈ : isDefined (⟦ weakenTy (sum A B) ⟧Ty [A])
                                    AwSumABᵈ = ⟦weaken⟧Tyᵈ (sum A B) SumABᵈ A=                                    
                                    AwSumAB= = ⟦weaken⟧Ty= (sum A B) SumABᵈ A=                                    

                                    AwCᵈ : isDefined (⟦ weakenTy' (prev last) C ⟧Ty _)
                                    AwCᵈ = ⟦weaken⟧Ty+ᵈ C Cᵈ A= SumAB-ft refl
                                    AwC= = ⟦weaken⟧Ty+= C Cᵈ A= SumAB-ft refl
                                    
                                    AwAᵈ : isDefined (⟦ weakenTy A ⟧Ty [A])
                                    AwAᵈ = ⟦weaken⟧Tyᵈ A Aᵈ A=
                                    AwA= = ⟦weaken⟧Ty= A Aᵈ A=
                                    AwA-ft = ⟦⟧Ty-ft (weakenTy A)

                                    AwBᵈ : isDefined (⟦ weakenTy B ⟧Ty [A])
                                    AwBᵈ = ⟦weaken⟧Tyᵈ B Bᵈ A=
                                    AwB= = ⟦weaken⟧Ty= B Bᵈ A=
                                    AwB-ft = ⟦⟧Ty-ft (weakenTy B)

                                    inlwAwBlastᵈ : isDefined (⟦ inl (weakenTy A) (weakenTy B) (var last) ⟧Tm [A])
                                    inlwAwBlastᵈ = (AwAᵈ , AwA-ft , AwBᵈ , AwB-ft , tt , ssₛ , (varCL₁ ∙ AwA=) , tt)
                                    inlwAwBlast₁ = inlStr₁ ∙ ! AwSumAB=

      dbᵈ = ⟦⟧Tmᵈ (Γᵈ , Bᵈ , tt) ddb
      dbₛ = ⟦⟧Tmₛ db
      db₁ = ⟦⟧Tm₁ (Γᵈ , Bᵈ , tt) ddb ∙ substBwCinrb=
          where  substBwCinrb= : ⟦ substTy (weakenTy' (prev last) C) (inr (weakenTy A) (weakenTy B) (var last)) ⟧Ty [B] $ _
                               ≡ T-db₁ _ [A] A= [B] B= [C] C=
                 substBwCinrb= = ⟦subst⟧Ty= (weakenTy' (prev last) C)
                                            BwCᵈ
                                            (inr (weakenTy A) (weakenTy B) (var last))
                                            inrwAwBlastᵈ
                                            inrwAwBlast₁
                                 ∙ ! (ap-irr-star (ap-irr-inrStr refl BwA= BwB= refl) BwC=)
                               where BwSumABᵈ : isDefined (⟦ weakenTy (sum A B) ⟧Ty [B])
                                     BwSumABᵈ = ⟦weaken⟧Tyᵈ (sum A B) SumABᵈ B=                                     
                                     BwSumAB= = ⟦weaken⟧Ty= (sum A B) SumABᵈ B=                                   
      
                                     BwCᵈ : isDefined (⟦ weakenTy' (prev last) C ⟧Ty _)
                                     BwCᵈ = ⟦weaken⟧Ty+ᵈ C Cᵈ B= SumAB-ft refl
                                     BwC= = ⟦weaken⟧Ty+= C Cᵈ B= SumAB-ft refl
                                     
                                     BwAᵈ : isDefined (⟦ weakenTy A ⟧Ty [B])
                                     BwAᵈ = ⟦weaken⟧Tyᵈ A Aᵈ B=
                                     BwA= = ⟦weaken⟧Ty= A Aᵈ B=
                                     BwA-ft = ⟦⟧Ty-ft (weakenTy A)

                                     BwBᵈ : isDefined (⟦ weakenTy B ⟧Ty [B])
                                     BwBᵈ = ⟦weaken⟧Tyᵈ B Bᵈ B=
                                     BwB= = ⟦weaken⟧Ty= B Bᵈ B=
                                     BwB-ft = ⟦⟧Ty-ft (weakenTy B)

                                     inrwAwBlastᵈ : isDefined (⟦ inr (weakenTy A) (weakenTy B) (var last) ⟧Tm [B])
                                     inrwAwBlastᵈ = (BwAᵈ , BwA-ft , BwBᵈ , BwB-ft , tt , ssₛ , (varCL₁ ∙ BwB=) , tt)
                                     inrwAwBlast₁ = inrStr₁ ∙ ! BwSumAB=
            
      uᵈ = ⟦⟧Tmᵈ Γᵈ du
      uₛ = ⟦⟧Tmₛ u
      u₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = SumABᵈ} du

⟦⟧Tmᵈ Γᵈ {u = pi i a b} (PiUU da db) =
  (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)
    where
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da
      bᵈ = ⟦⟧Tmᵈ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
⟦⟧Tmᵈ Γᵈ {u = lam A B u} (Lam dA dB du) =
  (Aᵈ ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt ) dB ,
   ⟦⟧Ty-ft B ,
   ⟦⟧Tmᵈ (Γᵈ , Aᵈ , tt) du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ (Γᵈ , Aᵈ , tt) du , tt)
  where
    Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
⟦⟧Tmᵈ Γᵈ {u = app A B f a} (App dA dB df da) =
  (Aᵈ ,
   A= ,
   Bᵈ ,
   B= ,
   ⟦⟧Tmᵈ Γᵈ df ,
   ⟦⟧Tmₛ f ,
   ⟦⟧Tm₁ Γᵈ {A = pi A B} {Aᵈ = (Aᵈ , A= , Bᵈ , B= , tt)} df ,
   ⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da , tt)
     where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B
 
  

⟦⟧Tmᵈ Γᵈ {u = sig i a b} (SigUU da db) =
  (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)
    where
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da
      bᵈ = ⟦⟧Tmᵈ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
⟦⟧Tmᵈ Γᵈ {u = pair A B a b} (Pair dA dB da db) =
  (Aᵈ ,
   A= ,
   Bᵈ ,
   ⟦⟧Ty-ft B ,
   aᵈ ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da ,
   ⟦⟧Tmᵈ Γᵈ db ,
   ⟦⟧Tmₛ b ,
   (⟦⟧Tm₁ Γᵈ db ∙ ⟦subst⟧Ty= B Bᵈ a aᵈ (⟦⟧Tm₁ Γᵈ da)) , tt)
     where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
⟦⟧Tmᵈ Γᵈ {u = pr1 A B u} (Pr1 dA dB du) =
  (Aᵈ ,
   A= ,
   Bᵈ ,
   B= ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ {A = sig A B} {Aᵈ = (Aᵈ , A= , Bᵈ , B= , tt)} du , tt)
     where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B 
⟦⟧Tmᵈ Γᵈ {u = pr2 A B u} (Pr2 dA dB du) =
  (Aᵈ ,
   A= ,
   Bᵈ ,
   B= ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ {A = sig A B} {Aᵈ = (Aᵈ , A= , Bᵈ , B= , tt)} du , tt)
     where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B  

⟦⟧Tmᵈ Γᵈ EmptyUU = tt
⟦⟧Tmᵈ Γᵈ {u = emptyelim A u} (Emptyelim dA du) =
  (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ du , tt)
⟦⟧Tmᵈ Γᵈ UnitUU = tt
⟦⟧Tmᵈ Γ TT = tt
⟦⟧Tmᵈ Γᵈ {u = unitelim A dtt u} (Unitelim dA ddtt du) =
  (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tmᵈ Γᵈ ddtt ,
   ⟦⟧Tmₛ dtt ,
   (⟦⟧Tm₁ Γᵈ ddtt ∙ ⟦subst⟧Ty= A (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA) tt tt ttStr₁) ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ du , tt)
⟦⟧Tmᵈ Γᵈ {u = nat i} NatUU = tt
⟦⟧Tmᵈ Γᵈ {u = zero} Zero = tt
⟦⟧Tmᵈ Γᵈ {u = suc u} (Suc du) =
  (⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ du , tt)
⟦⟧Tmᵈ {Γ = Γ} Γᵈ {u = natelim P dO dS u} (Natelim dP ddO ddS du) =
  (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt)
    where
      [Γ] = ⟦ Γ ⟧Ctx $ Γᵈ     

      Pᵈ : isDefined (⟦ P ⟧Ty (NatStr [Γ]))
      Pᵈ  = ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP
      [P] = ⟦ P ⟧Ty (NatStr [Γ]) $ Pᵈ
      P=  = ⟦⟧Ty-ft P {Aᵈ = Pᵈ}

      dOᵈ = ⟦⟧Tmᵈ Γᵈ ddO
      dOₛ = ⟦⟧Tmₛ dO
      dO₁ = ⟦⟧Tm₁ Γᵈ ddO ∙ substPzero=
          where substPzero= : ⟦ substTy P zero ⟧Ty [Γ] $ _ ≡ star (⟦ zero ⟧Tm [Γ] $ tt) [P] P= zeroStr₁
                substPzero= = ⟦subst⟧Ty= P Pᵈ zero tt zeroStr₁       
    
      dSᵈ = ⟦⟧Tmᵈ ((Γᵈ , (tt , tt)) , Pᵈ , tt) ddS
      dSₛ = ⟦⟧Tmₛ dS      
      dS₁ = ⟦⟧Tm₁ ((Γᵈ , (tt , tt)) , Pᵈ , tt) ddS ∙ subst_PprevwnatprevwP_sucprevlast=
          where subst_PprevwnatprevwP_sucprevlast= : ⟦ substTy (weakenTy' (prev last) (weakenTy' (prev last) P)) (suc (var (prev last))) ⟧Ty [P] $ _ ≡ T-dS₁ [Γ] [P] P=
                subst_PprevwnatprevwP_sucprevlast= = ⟦subst⟧Ty= (weakenTy' (prev last) (weakenTy' (prev last) P))
                                                      PprevwnatprevwPᵈ
                                                      (suc (var (prev last)))
                                                      sucprevlastᵈ
                                                      sucprevlast₁
                                                   ∙ ! (ap-irr-star refl PprevwnatprevwP=)
                                                   where nat= = ⟦⟧Ty-ft nat {Aᵈ = tt}
                                                   
                                                         natwnatᵈ : isDefined (⟦ weakenTy nat ⟧Ty (NatStr [Γ]))
                                                         natwnatᵈ = ⟦weaken⟧Tyᵈ nat tt nat=
                                                         natwnat= = ⟦weaken⟧Ty= nat tt nat=                                                        
                                                         
                                                         natprevwPᵈ : isDefined (⟦ weakenTy' (prev last) P ⟧Ty _)
                                                         natprevwPᵈ = ⟦weaken⟧Ty+ᵈ P Pᵈ nat= nat= refl
                                                         natprevwP= = ⟦weaken⟧Ty+= P Pᵈ nat= nat= refl
      
                                                         PprevwnatprevwPᵈ : isDefined (⟦ weakenTy' (prev last) (weakenTy' (prev last) P) ⟧Ty _)
                                                         PprevwnatprevwPᵈ = ⟦weaken⟧Ty+ᵈ (weakenTy' (prev last) P) natprevwPᵈ P= (ft-star ∙ pp₀) refl
                                                         PprevwnatprevwP= = ap-irr-star refl natprevwP= ∙ ⟦weaken⟧Ty+= (weakenTy' (prev last) P) natprevwPᵈ P= (ft-star ∙ pp₀) refl

                                                         Pwnatwnatᵈ : isDefined (⟦ weakenTy (weakenTy nat) ⟧Ty [P])
                                                         Pwnatwnatᵈ = ⟦weaken⟧Tyᵈ (weakenTy nat) natwnatᵈ P=
                                                         Pwnatwnat= = ap-irr-star refl natwnat= ∙ ⟦weaken⟧Ty= (weakenTy nat) natwnatᵈ P=                                                               
                                                         
                                                         sucprevlastᵈ : isDefined (⟦ suc (var (prev last)) ⟧Tm [P])
                                                         sucprevlastᵈ = (tt , ssₛ , (varC+₁ last P= varCL₁ ∙ Pwnatwnat=) , tt)
                                                         sucprevlast₁ = sucStr₁ ∙ ! Pwnatwnat=

      uᵈ  = ⟦⟧Tmᵈ Γᵈ du
      uₛ  = ⟦⟧Tmₛ u
      u₁  = ⟦⟧Tm₁ Γᵈ du


⟦⟧Tmᵈ Γᵈ {u = id i a u v} (IdUU da du dv) =
  (⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ {A = el i a} {Aᵈ = ⟦⟧Tmᵈ Γᵈ da , ⟦⟧Tmₛ a , ⟦⟧Tm₁ Γᵈ da , tt} du ,
   ⟦⟧Tmᵈ Γᵈ dv ,
   ⟦⟧Tmₛ v ,
   ⟦⟧Tm₁ Γᵈ {A = el i a} {Aᵈ = ⟦⟧Tmᵈ Γᵈ da , ⟦⟧Tmₛ a , ⟦⟧Tm₁ Γᵈ da , tt} dv , tt)
⟦⟧Tmᵈ Γᵈ {u = refl A a} (Refl dA da) =
  (⟦⟧Tyᵈ Γᵈ dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da , tt)
⟦⟧Tmᵈ {Γ = Γ} Γᵈ {u = jj A P d a b p} (JJ dA dP dd da db dp) = 
  (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt)
   where
      [Γ] = ⟦ Γ ⟧Ctx $ Γᵈ
      
      Aᵈ : isDefined (⟦ A ⟧Ty [Γ])
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      [A] = ⟦ A ⟧Ty [Γ] $ Aᵈ      
      A= = ⟦⟧Ty-ft A
      
      AwAᵈ : isDefined (⟦ weakenTy A ⟧Ty [A])
      AwAᵈ = ⟦weaken⟧Tyᵈ A Aᵈ A=
      AwA= = ⟦weaken⟧Ty= A Aᵈ A=
      AwA-ft = ⟦⟧Ty-ft (weakenTy A) {Aᵈ = AwAᵈ}
      
      Pᵈ : isDefined (⟦ P ⟧Ty (T-ftP [Γ] [A] A=))
      Pᵈ = cong⟦⟧Tyᵈ {A = P} id= Pᵈ'
         where [AwA] = ⟦ weakenTy A ⟧Ty [A] $ AwAᵈ
                     
               AwAwAᵈ : isDefined (⟦ weakenTy (weakenTy A) ⟧Ty [AwA])
               AwAwAᵈ = ⟦weaken⟧Tyᵈ (weakenTy A) AwAᵈ AwA-ft
               AwAwA= = ⟦weaken⟧Ty= (weakenTy A) AwAᵈ AwA-ft
               AwAwA-ft = ⟦⟧Ty-ft (weakenTy (weakenTy A)) {Aᵈ = AwAwAᵈ}
                         
               idᵈ : isDefined (⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [AwA])
               idᵈ = (AwAwAᵈ , AwAwA-ft
                     , tt , ssₛ , (varC+₁ last AwA-ft (varCL₁ ∙ AwA=) ∙ AwAwA=)
                     , tt , ssₛ , (varCL₁ ∙ AwAwA=) , tt)
               [id] = ⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty _ $ idᵈ
               id= : T-ftP [Γ] [A] A= ≡ [id]
               id= = ap-irr-IdStr AwA=
                                  (ap-irr-star (ap pp AwA=) AwA= ∙ AwAwA=)                          
                                  (ap (varC (prev last)) AwA=)
                                  (ap (varC last) AwA=)
               Pᵈ' : isDefined (⟦ P ⟧Ty [id])    
               Pᵈ' = ⟦⟧Tyᵈ (((Γᵈ , Aᵈ , tt) , AwAᵈ , tt) , idᵈ , tt) dP
      [P] = ⟦ P ⟧Ty (T-ftP [Γ] [A] A=) $ Pᵈ
      P= = ⟦⟧Ty-ft P {Aᵈ = Pᵈ}  
      
                                                    
      dᵈ : isDefined (⟦ d ⟧Tm [A])
      dᵈ = ⟦⟧Tmᵈ (Γᵈ , Aᵈ , tt) dd
      dₛ = ⟦⟧Tmₛ d
      d₁ : ∂₁ (⟦ d ⟧Tm [A] $ dᵈ) ≡ T-d₁ [Γ] [A] A= [P] P=
      d₁ = ⟦⟧Tm₁ (Γᵈ , Aᵈ , tt) dd ∙ subst3_prevprevprevwP_varlast_varlast_refllast
         where subst3_prevprevprevwP_varlast_varlast_refllast : ⟦ subst3Ty (weakenTy' (prev (prev (prev last))) P) (var last) (var last) (refl (weakenTy A) (var last)) ⟧Ty [A] $ _ ≡  T-d₁ [Γ] [A] A= [P] P=
               subst3_prevprevprevwP_varlast_varlast_refllast = ⟦subst3⟧Ty= (ft-star ∙ qq₀) (ft-star ∙ qq₀) (ft-star ∙ pp₀)
                                                                            (weakenTy' (prev (prev (prev last))) P) AprevprevprevwPᵈ
                                                                            (var last) varlastᵈ varlast₁
                                                                            (var last) varlastᵈ (varlast₁ ∙ ! star-varCL-star-qqpp)
                                                                            (refl (weakenTy A) (var last)) reflᵈ (refl₁' ∙ eq9)
                                                                ∙ ! (ap-irr-star (ap-irr-reflStr refl AwA= refl) (ap-irr-star refl (ap-irr-star refl AprevprevprevwP=)))
                                                              where varlastᵈ : isDefined (⟦ var last ⟧Tm [A])
                                                                    varlastᵈ = tt
                                                                    [varlast] = ⟦ var last ⟧Tm [A] $ varlastᵈ
                                                                    varlast₁ : ∂₁ [varlast] ≡ star (pp [A]) [A] _ _
                                                                    varlast₁ = varCL₁

                                                                    reflᵈ : isDefined (⟦ refl (weakenTy A) (var last) ⟧Tm [A])
                                                                    reflᵈ = (AwAᵈ , AwA-ft , tt , varCₛ last [A] , (varlast₁ ∙ AwA=) , tt)
                                                                    refl₁' : ∂₁ (⟦ refl (weakenTy A) (var last) ⟧Tm [A] $ reflᵈ ) ≡ IdStr [A] (star (pp [A]) [A] _ _) (ft-star ∙ pp₀)
                                                                                                                                          [varlast] ssₛ varlast₁
                                                                                                                                          [varlast] ssₛ varlast₁
                                                                    refl₁' = reflStr₁ ∙ ! (ap-irr-IdStr refl AwA= refl refl)
                                                                    eq9 = ! (ap-irr-star refl star-qqvarCL-star-qqqqpp
                                                                            ∙ IdStrNat (varC₀ {k = last}) {g₁ = varCL₁}
                                                                              ∙ ap-irr-IdStr refl
                                                                                             (star-pp' (ft-star ∙ pp₀)
                                                                                                       (ft-star ∙ pp₀)
                                                                                                       (varCₛ last _)
                                                                                                       varCL₁)
                                                                                             (star-varCL''
                                                                                             ∙ ap ss (is-section= (ft-star ∙ pp₀)
                                                                                                                  (varCₛ last _)
                                                                                                                  varCL₁))
                                                                                             (star-varCL'
                                                                                             ∙ ss-of-section _ (varCₛ last _)))
                                                                                                                                            
                                                                    AprevprevprevwPᵈ : isDefined (⟦ weakenTy' (prev (prev (prev last))) P ⟧Ty _)
                                                                    AprevprevprevwPᵈ = ⟦weaken⟧Ty+++ᵈ P Pᵈ A= T-ftP= (ft-star ∙ pp₀) A= refl
                                                                    AprevprevprevwP= = ⟦weaken⟧Ty+++= P Pᵈ A= T-ftP= (ft-star ∙ pp₀) A= refl

      aᵈ : isDefined (⟦ a ⟧Tm [Γ])
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da

      bᵈ : isDefined (⟦ b ⟧Tm [Γ])
      bᵈ = ⟦⟧Tmᵈ Γᵈ db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ Γᵈ db

      pᵈ : isDefined (⟦ p ⟧Tm [Γ])
      pᵈ = ⟦⟧Tmᵈ Γᵈ dp
      pₛ = ⟦⟧Tmₛ p
      p₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = (Aᵈ , A= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)} dp

⟦⟧Morᵈ {Δ = ◇} _ _ {◇} tt = tt
⟦⟧Morᵈ {Δ = Δ , B} Γᵈ (Δᵈ , Bᵈ , tt) {δ , u} (dδ , du) =
  (δᵈ , uᵈ , δ₁ , u₁ , tt)
    where
      δᵈ' = ⟦⟧Morᵈ Γᵈ Δᵈ dδ
      δᵈ = cong⟦⟧Mor {δ = δ} (! (⟦⟧Ty-ft B)) δᵈ'
      uᵈ = ⟦⟧Tmᵈ Γᵈ du
      δ₁ = ⟦⟧Mor₁ δ
      u₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = ⟦tsubst⟧Tyᵈ B Bᵈ δ δᵈ'} du ∙ ! (⟦tsubst⟧Ty= B Bᵈ δ δᵈ') ∙ ap-irr-star (ap-irr {B = λ X → isDefined (⟦ δ ⟧Mor _ X)} (λ x z → ⟦ δ ⟧Mor _ x $ z) (! (⟦⟧Ty-ft B))) refl

⟦⟧Tm₁ Γᵈ (VarLast {A = A} dA) = varCL₁ ∙ ⟦weaken⟧Ty= A (fst (snd Γᵈ)) (⟦⟧Ty-ft A)
⟦⟧Tm₁ Γᵈ {u = var (prev k)} (VarPrev {B = B} {A = A} dA dk) = varC+₁ k (⟦⟧Ty-ft B) (⟦⟧Tm₁ (fst Γᵈ) dk) ∙ ⟦weaken⟧Ty= A (⟦⟧Tyᵈ (fst Γᵈ) dA) (⟦⟧Ty-ft B)
⟦⟧Tm₁ Γᵈ (Conv dA du dA=) = ⟦⟧Tm₁ Γᵈ du ∙ ⟦⟧TyEq Γᵈ dA= {Aᵈ = ⟦⟧Tyᵈ Γᵈ dA}

⟦⟧Tm₁ Γᵈ {u = uu i} UUUU = uuStr₁

⟦⟧Tm₁ Γᵈ {u = sum i a b} (SumUU da db) = sumStr₁
⟦⟧Tm₁ Γᵈ {u = inl A B a} (Inl dA dB da) = inlStr₁
⟦⟧Tm₁ Γᵈ {u = inr A B b} (Inr dA dB db) = inrStr₁
⟦⟧Tm₁ Γᵈ {u = match A B C da db u} (Match dA dB dC dda ddb du) = matchStr₁ ∙ ! (⟦subst⟧Ty= C (⟦⟧Tyᵈ (Γᵈ , (⟦⟧Tyᵈ Γᵈ dA , ⟦⟧Ty-ft A , ⟦⟧Tyᵈ Γᵈ dB , ⟦⟧Ty-ft B , tt) , tt) dC) u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ {Aᵈ = (⟦⟧Tyᵈ Γᵈ dA , ⟦⟧Ty-ft A , ⟦⟧Tyᵈ Γᵈ dB , ⟦⟧Ty-ft B , tt)} du))

⟦⟧Tm₁ Γᵈ {u = pi i a b} (PiUU da db) = piStr₁
⟦⟧Tm₁ Γᵈ {u = lam A B u} (Lam dA dB du) = lamStr₁
⟦⟧Tm₁ Γᵈ {u = app A B f a} (App dA dB df da) = appStr₁ ∙ ! (⟦subst⟧Ty= B (⟦⟧Tyᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))

⟦⟧Tm₁ Γᵈ {u = sig i a b} (SigUU da db) = sigStr₁
⟦⟧Tm₁ Γᵈ {u = pair A B a b} (Pair dA dB da db) = pairStr₁
⟦⟧Tm₁ Γᵈ {u = pr1 A B u} (Pr1 dA dB du) = pr1Str₁
⟦⟧Tm₁ Γᵈ {u = pr2 A B u} (Pr2 dA dB du) =
  pr2Str₁ ∙ ! (⟦subst⟧Ty= B Bᵈ (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , ⟦⟧Tmᵈ Γᵈ du , ⟦⟧Tmₛ u , ⟦⟧Tm₁ Γᵈ {A = sig A B} {Aᵈ = Aᵈ , A= , Bᵈ , B= , tt} du , tt) pr1Str₁)
    where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B
      
⟦⟧Tm₁ Γᵈ EmptyUU = emptyStr₁
⟦⟧Tm₁ Γᵈ {u = emptyelim A u} (Emptyelim dA du) = emptyelimStr₁ ∙ ! (⟦subst⟧Ty= A (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA) u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ du))
⟦⟧Tm₁ Γᵈ UnitUU = unitStr₁
⟦⟧Tm₁ Γᵈ TT = ttStr₁
⟦⟧Tm₁ Γᵈ {u = unitelim A dtt u} (Unitelim dA ddtt du) = unitelimStr₁ ∙ ! (⟦subst⟧Ty= A (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA) u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ du))

⟦⟧Tm₁ Γᵈ {u = nat i} NatUU = natStr₁
⟦⟧Tm₁ Γᵈ {u = zero} Zero = zeroStr₁
⟦⟧Tm₁ Γᵈ {u = suc u} (Suc du) = sucStr₁
⟦⟧Tm₁ Γᵈ {u = natelim P dO dS u} (Natelim dP ddO ddS du) = natelimStr₁ ∙ ! (⟦subst⟧Ty= P (⟦⟧Tyᵈ (Γᵈ , tt , tt) dP) u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ du))

⟦⟧Tm₁ Γᵈ {u = id i a u v} (IdUU da du dv) = idStr₁
⟦⟧Tm₁ Γᵈ {u = refl A a} (Refl dA da) = reflStr₁
⟦⟧Tm₁ {Γ = Γ} Γᵈ {u = jj A P d a b p} (JJ dA dP dd da db dp) =
         jjStr₁ ∙ ! (⟦subst3⟧Ty= IdStr= (⟦⟧Ty-ft (weakenTy A)) (⟦⟧Ty-ft A) P (⟦⟧Tyᵈ (((Γᵈ , (Aᵈ , tt)) , wAᵈ , tt) , (idᵈ , tt)) dP)
                                 a aᵈ a₁
                                 b bᵈ (b₁ ∙ ! [wA][a] ∙ ap-irr-star refl wA=)
                                 p pᵈ (p₁ ∙ eq1)
                ∙ ap-irr-star refl (ap-irr-star (ap-irr-qq refl (ap-irr-star (ap-irr-qq refl (! wA=)) id=))
                                                (ap-irr-star (ap-irr-qq  (ap-irr-qq refl (! wA=)) id=)
                                                             (ap-irr (λ z p → ⟦ P ⟧Ty z $ p) id=))))
      where
        X = ⟦ Γ ⟧Ctx $ Γᵈ
        Aᵈ : isDefined (⟦ A ⟧Ty X)
        Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
        [A] = ⟦ A ⟧Ty X $ Aᵈ
        A= : ft [A] ≡ X
        A= = ⟦⟧Ty-ft A
        wAᵈ : isDefined (⟦ weakenTy A ⟧Ty [A])
        wAᵈ = ⟦weaken⟧Tyᵈ A Aᵈ A=
        wA= = ⟦weaken⟧Ty= A Aᵈ A=
        [wA] = ⟦ weakenTy A ⟧Ty [A] $ wAᵈ
        [wA]-ft : ft [wA] ≡ [A]
        [wA]-ft = ⟦⟧Ty-ft (weakenTy A)
        wwAᵈ : isDefined (⟦ weakenTy (weakenTy A) ⟧Ty [wA])
        wwAᵈ = ⟦weaken⟧Tyᵈ (weakenTy A) wAᵈ [wA]-ft
        wwA= = ⟦weaken⟧Ty= (weakenTy A) wAᵈ [wA]-ft
        [wwA] = ⟦ weakenTy (weakenTy A) ⟧Ty [wA] $ wwAᵈ
        [wwA]-ft : ft [wwA] ≡ [wA]
        [wwA]-ft = ⟦⟧Ty-ft (weakenTy (weakenTy A))
        idᵈ : isDefined (⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [wA])
        idᵈ = (wwAᵈ , [wwA]-ft , tt , varCₛ (prev last) [wA] , (varC+₁ last [wA]-ft (varCL₁ ∙ wA=) ∙ wwA=) , tt , varCₛ last [wA] , (varCL₁ ∙ wwA=) , tt)     
        id= = ap-irr-IdStr (!  wA=) (! wwA= ∙ ap-irr-star (ap pp (! wA=)) (! wA=)) (ap ss (ap pp (! wA=))) (ap ss (ap idC (! wA=))) {v'ₛ = ssₛ} {v'₁ = ss₁ id₁ ∙ ap-irr-star (id-left pp₀) refl}

        aᵈ : isDefined (⟦ a ⟧Tm X)
        aᵈ = ⟦⟧Tmᵈ Γᵈ da
        aₛ = ⟦⟧Tmₛ a
        a₁ = ⟦⟧Tm₁ Γᵈ da

        bᵈ : isDefined (⟦ b ⟧Tm X)
        bᵈ = ⟦⟧Tmᵈ Γᵈ db
        bₛ = ⟦⟧Tmₛ b
        b₁ = ⟦⟧Tm₁ Γᵈ db

        pᵈ : isDefined (⟦ p ⟧Tm X)
        pᵈ = ⟦⟧Tmᵈ Γᵈ dp
        p₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = (Aᵈ , A= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)} dp
 
        [wA][a] = star-pp' A= A= aₛ a₁
        [wA][b] = star-pp' A= A= bₛ b₁
        eq1 = ! (ap-irr-star refl ((ap-irr-star (ap-irr-qq refl (! wA=)) id=) ∙ IdStrNat (qq₀ ∙ [wA][a]) ∙ ap-irr-IdStr refl (star-pp (⟦⟧Tm₀ a) ∙ ap-irr-star (ap pp [wA][a]) [wA][a])
                                                                              (star-varC+' (⟦⟧Tmₛ a) ∙ ap-irr-starTm (ap pp [wA][a]) refl) {u'ₛ = ssₛ} {u'₁ = starTm₁ (pp [A]) A= _ aₛ a₁ (pp₁ ∙ A=)}
                                                                              (star-varCL ∙ ap (varC last) [wA][a]) {v'ₛ = ssₛ} {v'₁ = varCL₁}) {q = ft-star ∙ qq₀} {q' = IdStr=} {f₁' = b₁}
                                  ∙ IdStrNat (⟦⟧Tm₀ b) ∙ ap-irr-IdStr refl [wA][b]
                                                                           (! (starTm-comp pp₀) ∙ ap-irr-starTm (is-section= A= bₛ b₁) refl ∙ starTm-id (⟦⟧Tm₀ a) aₛ)
                                                                           (star-varCL' ∙ ss-of-section _ bₛ))
                                                                                            


⟦weaken⟧Tyᵈ' k (uu i) Aᵈ _ _ _ = tt
⟦weaken⟧Tyᵈ' k (el i v) (vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tmᵈ' k v vᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weaken⟧Tm₁' k v vᵈ X+= X= Z= v₁ ∙ UUStrNat (qq^₀ ∙ Z=)) , tt)
⟦weaken⟧Tyᵈ' k (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k A)
  , ⟦weaken⟧Tyᵈ' k B Bᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k B)
  , tt)  
⟦weaken⟧Tyᵈ' k (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) , tt)
⟦weaken⟧Tyᵈ' k (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) , tt)
⟦weaken⟧Tyᵈ' k empty Aᵈ _ _ _  = tt
⟦weaken⟧Tyᵈ' k unit Aᵈ _ _ _ = tt
⟦weaken⟧Tyᵈ' k nat Aᵈ _ _ _ = tt
⟦weaken⟧Tyᵈ' k (id A u v) (Aᵈ , A= , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦weaken⟧Tmᵈ' k v vᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weaken⟧Tm₁' k v vᵈ X+= X= Z= v₁ ∙ ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) , tt)

⟦weaken⟧Tmᵈ' k (var x) tt X+= X= Z= = tt

⟦weaken⟧Tmᵈ' k (uu i) tt X+= X= Z= = tt
⟦weaken⟧Tmᵈ' k (sum i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z=
  , ⟦⟧Tmₛ (weakenTm' k a)
  , (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ UUStrNat qq^₀ ∙ ap-irr-UUStr Z=)
  , ⟦weaken⟧Tmᵈ' k b bᵈ X+= X= Z=
  , ⟦⟧Tmₛ (weakenTm' k b)
  , (⟦weaken⟧Tm₁' k b bᵈ X+= X= Z= b₁ ∙ UUStrNat qq^₀ ∙ ap-irr-UUStr Z=)
  , tt)
⟦weaken⟧Tmᵈ' k (inl A B a) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k A)
  , ⟦weaken⟧Tyᵈ' k B Bᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k B)
  , ⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z=
  , ⟦⟧Tmₛ (weakenTm' k a)
  , (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
  , tt)  
⟦weaken⟧Tmᵈ' k (inr A B b) (Aᵈ , A= , Bᵈ , B= , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k A)
  , ⟦weaken⟧Tyᵈ' k B Bᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k B)
  , ⟦weaken⟧Tmᵈ' k b bᵈ X+= X= Z=
  , ⟦⟧Tmₛ (weakenTm' k b)
  , (⟦weaken⟧Tm₁' k b bᵈ X+= X= Z= b₁ ∙ ⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=)
  , tt)
⟦weaken⟧Tmᵈ' k (match A B C da db u) (Aᵈ , A= , Bᵈ , B= , Cᵈ , C= , daᵈ , daₛ , da₁ , dbᵈ , dbₛ , db₁ , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k A)
  , ⟦weaken⟧Tyᵈ' k B Bᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k B)
  , ⟦weaken⟧Ty+ᵈ' k C Cᵈ X+= X= SumStr= (⟦weaken⟧Ty=' k (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z=)
  , ⟦⟧Ty-ft (weakenTy' (prev k) C)
  , ⟦weaken⟧Tm+ᵈ' k da daᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
  , ⟦⟧Tmₛ (weakenTm' (prev k) da)
  , (⟦weaken⟧Tm+₁' k da daᵈ X+= X= T-da₁= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) da₁ ∙ T-da₁Nat qq^₀ ∙ ap-irr-T-da₁ Z= (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) (⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=) (⟦weaken⟧Ty+=' k C Cᵈ X+= X= SumStr= (⟦weaken⟧Ty=' k (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z=)))
  , ⟦weaken⟧Tm+ᵈ' k db dbᵈ X+= X= (⟦⟧Ty-ft B) (⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=)
  , ⟦⟧Tmₛ (weakenTm' (prev k) db)
  , (⟦weaken⟧Tm+₁' k db dbᵈ X+= X= T-db₁= (⟦⟧Ty-ft B) (⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=) db₁ ∙ T-db₁Nat qq^₀ ∙ ap-irr-T-db₁ Z= (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) (⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=) (⟦weaken⟧Ty+=' k C Cᵈ X+= X= SumStr= (⟦weaken⟧Ty=' k (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z=)))
  , ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z=
  , ⟦⟧Tmₛ (weakenTm' k u)
  , (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ ⟦weaken⟧Ty=' k (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z=)
  , tt)
⟦weaken⟧Tmᵈ' k (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ UUStrNat (qq^₀ ∙ Z=)) ,
   ⟦weaken⟧Tm+ᵈ' k b bᵈ X+= X= ElStr= (ElStrNat (qq^₀ ∙ Z=) ∙ ap-irr-ElStr refl (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) b) ,
   (⟦weaken⟧Tm+₁' k b bᵈ X+= X= UUStr= ElStr= (ElStrNat (qq^₀ ∙ Z=) ∙ ap-irr-ElStr refl (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)) b₁ ∙ UUStrNat (qq₀ ∙ ElStrNat (qq^₀ ∙ Z=) ∙ ap-irr-ElStr refl (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=))) , tt)
⟦weaken⟧Tmᵈ' k (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weaken⟧Tm+ᵈ' k u uᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) u) ,
   (⟦weaken⟧Tm+₁' k u uᵈ X+= X= (⟦⟧Ty-ft B) (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) u₁ ∙ ⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)) , tt)
⟦weaken⟧Tmᵈ' k (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weaken⟧Tmᵈ' k f fᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k f) ,
   (⟦weaken⟧Tm₁' k f fᵈ X+= X= Z= f₁ ∙ PiStrNat qq^₀ ∙ ap-irr-PiStr Z= (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))) ,
   ⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) , tt)
⟦weaken⟧Tmᵈ' k (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= = 
  (⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ UUStrNat qq^₀ ∙ ap-irr-UUStr Z=) ,
   ⟦weaken⟧Tm+ᵈ' k b bᵈ X+= X= ElStr= (⟦weaken⟧Ty=' k (el i a) (aᵈ , aₛ , a₁ , tt) X+= X= Z=) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) b) ,
   (⟦weaken⟧Tm+₁' k b bᵈ X+= X= UUStr= ElStr= (⟦weaken⟧Ty=' k (el i a) (aᵈ , aₛ , a₁ , tt) X+= X= Z=) b₁ ∙ UUStrNat qq₀ ∙ ap-irr-UUStr (⟦weaken⟧Ty=' k (el i a) (aᵈ , aₛ , a₁ , tt) X+= X= Z=))
   , tt)
⟦weaken⟧Tmᵈ' k (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦weaken⟧Tmᵈ' k b bᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k b) ,
   (⟦weaken⟧Tm₁' k b bᵈ X+= X= Z= b₁ ∙ starstar (⟦⟧Ty-ft A) aₛ ∙ ap-irr-star (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=) (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))) , tt)
⟦weaken⟧Tmᵈ' k (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ SigStrNat qq^₀ ∙ ap-irr-SigStr Z= (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))) , tt)
⟦weaken⟧Tmᵈ' k (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ SigStrNat qq^₀ ∙ ap-irr-SigStr Z= (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))) , tt)

⟦weaken⟧Tmᵈ' k (empty i) tt X+= X= Z= = tt
⟦weaken⟧Tmᵈ' k (emptyelim A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Ty+ᵈ' k A Aᵈ X+= X= EmptyStr= (EmptyStrNat (qq^₀ ∙ Z=)) ,
    ⟦⟧Ty-ft (weakenTy' (prev k) A) ,
    ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
    ⟦⟧Tmₛ (weakenTm' k u) ,
    (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ EmptyStrNat (qq^₀ ∙ Z=)) , tt)

⟦weaken⟧Tmᵈ' k (unit i) tt X+= X= Z= = tt
⟦weaken⟧Tmᵈ' k tt tt X+= X= Z= = tt
⟦weaken⟧Tmᵈ' k (unitelim A dtt u) (Aᵈ , A= , dttᵈ , dttₛ , dtt₁ , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Ty+ᵈ' k A Aᵈ X+= X= UnitStr= (UnitStrNat (qq^₀ ∙ Z=)) ,
    ⟦⟧Ty-ft (weakenTy' (prev k) A) ,
    ⟦weaken⟧Tmᵈ' k dtt dttᵈ X+= X= Z= ,
    ⟦⟧Tmₛ (weakenTm' k dtt) ,
    (⟦weaken⟧Tm₁' k dtt dttᵈ X+= X= Z= dtt₁ ∙ starstar UnitStr= ttStrₛ ∙ ap-irr-star (ttStrNat (qq^₀ ∙ Z=)) (⟦weaken⟧Ty+=' k A Aᵈ X+= X= UnitStr= (UnitStrNat (qq^₀ ∙ Z=)))) ,
    ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
    ⟦⟧Tmₛ (weakenTm' k u) ,
    (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ UnitStrNat (qq^₀ ∙ Z=)) , tt)

⟦weaken⟧Tmᵈ' k (nat i) tt X+= X= Z= = tt
⟦weaken⟧Tmᵈ' k zero tt X+= X= Z= = tt
⟦weaken⟧Tmᵈ' k (suc u) (uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ NatStrNat qq^₀ ∙ ap NatStr Z=) , tt)
⟦weaken⟧Tmᵈ' k (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) X+= X= {Z = Y} Z= =
  (Pᵈw , P=w , dOᵈw , dOₛw , dO₁w , dSᵈw , dSₛw , dS₁w , uᵈw , uₛw , u₁w , tt)
    where
      naturalityNat = NatStrNat (qq^₀ ∙ Z=)
      wP= = ⟦weaken⟧Ty+=' k P Pᵈ X+= X= NatStr= naturalityNat
      Pᵈw = ⟦weaken⟧Ty+ᵈ' k P Pᵈ X+= X= NatStr= naturalityNat
      P=w = ⟦⟧Ty-ft (weakenTy' (prev k) P)
      dOᵈw = ⟦weaken⟧Tmᵈ' k dO dOᵈ X+= X= Z=
      dOₛw = ⟦⟧Tmₛ (weakenTm' k dO)
      dO₁w = ⟦weaken⟧Tm₁' k dO dOᵈ X+= X= Z= dO₁ ∙ starstar NatStr= zeroStrₛ ∙ ap-irr-star (zeroStrNat (qq^₀ ∙ Z=)) wP=
      dSᵈw = ⟦weaken⟧Tm++ᵈ' k dS dSᵈ X+= X= (⟦⟧Ty-ft P) NatStr= (⟦weaken⟧Ty+=' k P Pᵈ X+= X= NatStr= naturalityNat)
      dSₛw = ⟦⟧Tmₛ (weakenTm' (prev (prev k)) dS)
      dS₁w = ⟦weaken⟧Tm++₁' k dS dSᵈ X+= X= (ft-star ∙ sucStr₀) P= NatStr= wP= dS₁ ∙
             T-dS₁Nat (qq^₀ ∙ Z=) ∙ ap-irr-T-dS₁ refl wP=
      uᵈw = ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z=
      uₛw = ⟦⟧Tmₛ (weakenTm' k u)
      u₁w = ⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ naturalityNat
      
⟦weaken⟧Tmᵈ' k (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ UUStrNat (qq^₀ ∙ Z=)) ,
   ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ ElStrNat (qq^₀ ∙ Z=) ∙ ap-irr-ElStr refl (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)) ,
   ⟦weaken⟧Tmᵈ' k v vᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weaken⟧Tm₁' k v vᵈ X+= X= Z= v₁ ∙ ElStrNat (qq^₀ ∙ Z=) ∙ ap-irr-ElStr refl (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)) , tt)
⟦weaken⟧Tmᵈ' k (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) , tt)
⟦weaken⟧Tmᵈ' k (jj A P d a b p) (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt) X+= X= Z= =
  (Aᵈw , A=w , Pᵈw , P=w , dᵈw , dₛw , d₁w , aᵈw , aₛw , a₁w , bᵈw , bₛw , b₁w , pᵈw , pₛw , p₁w , tt)
  where
   Aᵈw = ⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z=
   Aw= = ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=
   A=w = ⟦⟧Ty-ft (weakenTy' k A)
   Pᵈw = ⟦weaken⟧Ty+++ᵈ' k P Pᵈ X+= X= T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (qq^₀ ∙ Z=) ∙ ap-irr (T-ftP _) Aw=)
   Pw= = ⟦weaken⟧Ty+++=' k P Pᵈ X+= X= T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (qq^₀ ∙ Z=) ∙ ap-irr (T-ftP _) Aw=)
   P=w = ⟦⟧Ty-ft (weakenTy' (prev (prev (prev k))) P)
   dᵈw = ⟦weaken⟧Tm+ᵈ' k d dᵈ X+= X= A= Aw=
   dₛw = ⟦⟧Tmₛ (weakenTm' (prev k) d)
   d₁w = ⟦weaken⟧Tm+₁' k d dᵈ X+= X= T-d₁= A= Aw= d₁ ∙ T-d₁Nat  (qq^₀ ∙ Z=) ∙ ap-irr-T-d₁ refl Aw= Pw=
   aᵈw = ⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z=
   aₛw = ⟦⟧Tmₛ (weakenTm' k a)
   a₁w = ⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ Aw=
   bᵈw = ⟦weaken⟧Tmᵈ' k b bᵈ X+= X= Z=
   bₛw = ⟦⟧Tmₛ (weakenTm' k b)
   b₁w = ⟦weaken⟧Tm₁' k b bᵈ X+= X= Z= b₁ ∙ Aw=
   pᵈw = ⟦weaken⟧Tmᵈ' k p pᵈ X+= X= Z=
   pₛw = ⟦⟧Tmₛ (weakenTm' k p)
   p₁w = ⟦weaken⟧Tm₁' k p pᵈ X+= X= Z= p₁ ∙ IdStrNat (qq^₀ ∙ Z=) ∙ ap-irr-IdStr refl Aw= (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=) (⟦weaken⟧Tm=' k b bᵈ X+= X= Z=)

⟦weaken⟧Ty=' k (uu i) _ X+= X= Z= =
  UUStrNat qq^₀ ∙ ap-irr-UUStr Z=
⟦weaken⟧Ty=' k (el i v) (vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  ElStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-ElStr refl (⟦weaken⟧Tm=' k v vᵈ X+= X= Z=)
⟦weaken⟧Ty=' k (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  SumStrNat qq^₀
  ∙ ap-irr-SumStr Z=
                  (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=)
⟦weaken⟧Ty=' k (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  PiStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-PiStr refl
                 (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
                 (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))
⟦weaken⟧Ty=' k (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  SigStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-SigStr refl
                  (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))
⟦weaken⟧Ty=' k empty _ X+= X= Z= = EmptyStrNat (qq^₀ ∙ Z=)
⟦weaken⟧Ty=' k unit _ X+= X= Z= = UnitStrNat (qq^₀ ∙ Z=)
⟦weaken⟧Ty=' k nat _ X+= X= Z= =
  NatStrNat (qq^₀ ∙ Z=)
⟦weaken⟧Ty=' k (id A u v) (Aᵈ , A= , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  IdStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-IdStr refl (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) (⟦weaken⟧Tm=' k u uᵈ X+= X= Z=) (⟦weaken⟧Tm=' k v vᵈ X+= X= Z=)


⟦weaken⟧Tm=' {n = 0} k (var ())
⟦weaken⟧Tm=' {n = suc n} last (var x) tt X+= refl refl = star-varCL'' {g₀ = pp^₀ x _} ∙ ap ss (ap-irr-comp refl qq^last ∙ ! ((pp^prev {k = x} X+=)))
⟦weaken⟧Tm=' {n = suc n} (prev k) (var last) tt X+= refl Z= = star-varCL' ∙ ap ss qq^prev ∙ ap ss (! (id-left qq₀) ∙ ap-irr-comp refl (ap idC Z=) {f₁' = id₁ ∙ ! Z=}) ∙ ! ss-comp
⟦weaken⟧Tm=' {n = suc n} (prev k) (var (prev x)) tt X+= refl Z= = star-varCL'' {g₀ = pp^₀ (prev x) _} ∙ ap ss (ap-irr-comp (pp^prev refl) qq^prev ∙ assoc ∙ ap-irr-comp refl (pp-qq ∙ ap-irr-comp refl (ap pp Z=)) ∙ ! (assoc {f₁ = pp₁ ∙ ap ft (! Z=) ∙ ft-star ∙ qq^₀} {g₀ = qq^₀} {h₀ = pp^₀ x _})) ∙ ! (star-varCL'' {g₀ = comp₀ ∙ qq^₀}) ∙ ap ss (ap-irr-comp (! star-varCL'' ∙ ⟦weaken⟧Tm=' k (var x) tt X+= refl refl) refl) ∙ star-varCL'' ∙ ap ss (! (pp^prev {k = weakenVar' k x} (ap ft (! Z=) ∙ ft-star ∙ qq^₀)))

⟦weaken⟧Tm=' k (uu i) tt X+= X= Z= =
  uuStrNat (qq^₀ ∙ Z=)


⟦weaken⟧Tm=' k (sum i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  sumStrNat qq^₀
  ∙ ap-irr-sumStr Z=
                  (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)
                  (⟦weaken⟧Tm=' k b bᵈ X+= X= Z=)
⟦weaken⟧Tm=' k (inl A B a) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , tt) X+= X= Z= =
  inlStrNat qq^₀
  ∙ ap-irr-inlStr Z=
                  (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=)
                  (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)
⟦weaken⟧Tm=' k (inr A B b) (Aᵈ , A= , Bᵈ , B= , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  inrStrNat qq^₀
  ∙ ap-irr-inrStr Z=
                  (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=)
                  (⟦weaken⟧Tm=' k b bᵈ X+= X= Z=)

⟦weaken⟧Tm=' k (match A B C da db u) (Aᵈ , A= , Bᵈ , B= , Cᵈ , C= , daᵈ , daₛ , da₁ , dbᵈ , dbₛ , db₁ , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  matchStrNat qq^₀
  ∙ ap-irr-matchStr Z=
                    (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
                    (⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=)
                    (⟦weaken⟧Ty+=' k C Cᵈ X+= X= SumStr= (⟦weaken⟧Ty=' k (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z=))
                    (⟦weaken⟧Tm+=' k da daᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) )
                    (⟦weaken⟧Tm+=' k db dbᵈ X+= X= (⟦⟧Ty-ft B) (⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=))
                    (⟦weaken⟧Tm=' k u uᵈ X+= X= Z=)

⟦weaken⟧Tm=' k (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  piStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-piStr refl
                 (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)
                 (⟦weaken⟧Tm+=' k b bᵈ X+= X= ElStr= (ElStrNat qq^₀ ∙ ap-irr-ElStr Z= (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)))
⟦weaken⟧Tm=' k (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  lamStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-lamStr refl
                  (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))
                  (⟦weaken⟧Tm+=' k u uᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))
⟦weaken⟧Tm=' k (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) X+= X= Z= =
  appStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-appStr refl
                  (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))
                  (⟦weaken⟧Tm=' k f fᵈ X+= X= Z=)
                  (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)

⟦weaken⟧Tm=' k (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  sigStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-sigStr refl
                  (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)
                  (⟦weaken⟧Tm+=' k b bᵈ X+= X= ElStr= (ElStrNat qq^₀ ∙ ap-irr-ElStr Z= (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)))
⟦weaken⟧Tm=' k (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  pairStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-pairStr refl
                   (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
                   (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))
                   (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)
                   (⟦weaken⟧Tm=' k b bᵈ X+= X= Z=)
⟦weaken⟧Tm=' k (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  pr1StrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-pr1Str refl
                  (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))
                  (⟦weaken⟧Tm=' k u uᵈ X+= X= Z=)
⟦weaken⟧Tm=' k (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  pr2StrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-pr2Str refl
                  (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))
                  (⟦weaken⟧Tm=' k u uᵈ X+= X= Z=)

⟦weaken⟧Tm=' k (empty i) tt X+= X= Z= =
  emptyStrNat (qq^₀ ∙ Z=)
⟦weaken⟧Tm=' k (emptyelim A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  emptyelimStrNat (qq^₀ ∙ Z=) ∙ ap-irr-emptyelimStr refl (⟦weaken⟧Ty+=' k A Aᵈ X+= X= EmptyStr= (EmptyStrNat (qq^₀ ∙ Z=))) (⟦weaken⟧Tm=' k u uᵈ X+= X= Z=)
⟦weaken⟧Tm=' k (unit i) tt X+= X= Z= =
  unitStrNat (qq^₀ ∙ Z=)
⟦weaken⟧Tm=' k tt tt X+= X= Z= =
  ttStrNat (qq^₀ ∙ Z=)
⟦weaken⟧Tm=' k (unitelim A dtt u) (Aᵈ , A= , dttᵈ , dttₛ , dtt₁ , uᵈ , uₛ , u₁) X+= X= Z= =
  unitelimStrNat (qq^₀ ∙ Z=) ∙ ap-irr-unitelimStr refl (⟦weaken⟧Ty+=' k A Aᵈ X+= X= UnitStr= (UnitStrNat (qq^₀ ∙ Z=))) (⟦weaken⟧Tm=' k dtt dttᵈ X+= X= Z=) (⟦weaken⟧Tm=' k u uᵈ X+= X= Z=)

⟦weaken⟧Tm=' k (nat i) tt X+= X= Z= =
  natStrNat (qq^₀ ∙ Z=)
⟦weaken⟧Tm=' k zero tt X+= X= Z= =
  zeroStrNat (qq^₀ ∙ Z=)
⟦weaken⟧Tm=' k (suc u) (uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  sucStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-sucStr refl (⟦weaken⟧Tm=' k u uᵈ X+= X= Z=)
⟦weaken⟧Tm=' k (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  natelimStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-natelimStr refl
                      (⟦weaken⟧Ty+=' k P Pᵈ X+= X= NatStr= (NatStrNat (qq^₀ ∙ Z=)))
                      (⟦weaken⟧Tm=' k dO dOᵈ X+= X= Z=)
                      (⟦weaken⟧Tm++=' k dS dSᵈ X+= X= (⟦⟧Ty-ft P) NatStr= (⟦weaken⟧Ty+=' k P Pᵈ X+= X= NatStr= (NatStrNat (qq^₀ ∙ Z=))))
                      (⟦weaken⟧Tm=' k u uᵈ X+= X= Z=)

⟦weaken⟧Tm=' k (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  idStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-idStr refl
                 (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)
                 (⟦weaken⟧Tm=' k u uᵈ X+= X= Z=)
                 (⟦weaken⟧Tm=' k v vᵈ X+= X= Z=)
⟦weaken⟧Tm=' k (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  reflStrNat (qq^₀ ∙ Z=)
  ∙ ap-irr-reflStr refl
                   (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
                   (⟦weaken⟧Tm=' k u uᵈ X+= X= Z=)
⟦weaken⟧Tm=' k (jj A P d a b p) (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt) X+= X= Z= =
  jjStrNat (qq^₀ ∙ Z=) ∙ ap-irr-jjStr refl
                                      (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
                                      (⟦weaken⟧Ty+++=' k P Pᵈ X+= X= T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (qq^₀ ∙ Z=) ∙ ap-irr (T-ftP _) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)))
                                      (⟦weaken⟧Tm+=' k d dᵈ X+= X= A= (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))
                                      (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=)
                                      (⟦weaken⟧Tm=' k b bᵈ X+= X= Z=)
                                      (⟦weaken⟧Tm=' k p pᵈ X+= X= Z=)


⟦⟧TyEq Γᵈ (TySymm dA=) = ! (⟦⟧TyEq Γᵈ dA=)
⟦⟧TyEq Γᵈ (TyTran dB dA= dB=) = ⟦⟧TyEq Γᵈ dA= {A'ᵈ = ⟦⟧Tyᵈ Γᵈ dB} ∙ ⟦⟧TyEq Γᵈ dB=

⟦⟧TyEq Γᵈ UUCong = refl
⟦⟧TyEq Γᵈ (ElCong dv=) = ap-irr-ElStr refl (⟦⟧TmEq Γᵈ dv=)
⟦⟧TyEq Γᵈ {A = sum A B} (SumCong dA= dB=) = ap-irr-SumStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq Γᵈ dB=)
⟦⟧TyEq Γᵈ {A = sig A B} (SigCong dA dA= dB=) = ap-irr-SigStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TyEq Γᵈ {A = pi A B} (PiCong dA dA= dB=) = ap-irr-PiStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TyEq Γᵈ EmptyCong = refl
⟦⟧TyEq Γᵈ UnitCong = refl
⟦⟧TyEq Γᵈ NatCong = refl
⟦⟧TyEq Γᵈ (IdCong dA du dv) = ap-irr-IdStr refl (⟦⟧TyEq Γᵈ dA) (⟦⟧TmEq Γᵈ du) (⟦⟧TmEq Γᵈ dv)

⟦⟧TyEq Γᵈ ElUU= = eluuStr
⟦⟧TyEq Γᵈ (ElSum= da db) = elsumStr
⟦⟧TyEq Γᵈ (ElPi= da db) = elpiStr
⟦⟧TyEq Γᵈ (ElSig= da db) = elsigStr
⟦⟧TyEq Γᵈ ElEmpty= = elemptyStr
⟦⟧TyEq Γᵈ ElUnit= = elunitStr
⟦⟧TyEq Γᵈ ElNat= = elnatStr
⟦⟧TyEq Γᵈ (ElId= da du dv) = elidStr

⟦⟧TmEq Γᵈ (VarLastCong dA) = refl
⟦⟧TmEq (Γᵈ , Bᵈ , tt) (VarPrevCong {B = B} {k = k} {k' = k'} dA dx) = ap ss (pp^prev (⟦⟧Ty-ft B)) ∙ (! star-varCL'' ∙ ap-irr-starTm refl (⟦⟧TmEq Γᵈ dx) ∙ star-varCL'') ∙ ! (ap ss (pp^prev (⟦⟧Ty-ft B)))
⟦⟧TmEq Γᵈ (TmSymm du=) = ! (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq Γᵈ (TmTran dv du= du'=) = ⟦⟧TmEq Γᵈ du= {u'ᵈ = ⟦⟧Tmᵈ Γᵈ dv} ∙ ⟦⟧TmEq Γᵈ du'=
⟦⟧TmEq Γᵈ (ConvEq dA' du= dA=) = ⟦⟧TmEq Γᵈ du=

⟦⟧TmEq Γᵈ UUUUCong = refl

⟦⟧TmEq Γᵈ {u = sum i a b} (SumUUCong da= db=) = ap-irr-sumStr refl (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq Γᵈ db=)
⟦⟧TmEq Γᵈ {u = inl A B a} (InlCong dA= dB= da=) = ap-irr-inlStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq Γᵈ dB=) (⟦⟧TmEq Γᵈ da=)
⟦⟧TmEq Γᵈ {u = inr A B b} (InrCong dA= dB= db=) = ap-irr-inrStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq Γᵈ dB=) (⟦⟧TmEq Γᵈ db=)
⟦⟧TmEq Γᵈ {u = match A B C da db u} (MatchCong dA= dB= dC= dA da= dB db= du=) =
       ap-irr-matchStr refl
                       (⟦⟧TyEq Γᵈ dA=)
                       (⟦⟧TyEq Γᵈ dB=)
                       (⟦⟧TyEq+ (Γᵈ , (⟦⟧Tyᵈ Γᵈ dA , ⟦⟧Ty-ft A , ⟦⟧Tyᵈ Γᵈ dB , ⟦⟧Ty-ft B , tt) , tt) dC=
                                (ap-irr-SumStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq Γᵈ dB=)))
                       (⟦⟧TmEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) da= (⟦⟧TyEq Γᵈ dA=))
                       (⟦⟧TmEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dB , tt) db= (⟦⟧TyEq Γᵈ dB=))
                       (⟦⟧TmEq Γᵈ du=) 
⟦⟧TmEq Γᵈ {u = pi i a b} (PiUUCong da da= db=) {uᵈ = (aᵈ , aₛ , a₁ , _)} = ap-irr-piStr refl (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq+ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db= (ap-irr-ElStr refl (⟦⟧TmEq Γᵈ da=)))
⟦⟧TmEq Γᵈ {u = lam A B u} (LamCong dA dA= dB= du=) = ap-irr-lamStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) du= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TmEq Γᵈ {u = app A B f a} (AppCong dA dA= dB= df= da=) = ap-irr-appStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ df=) (⟦⟧TmEq Γᵈ da=)

⟦⟧TmEq Γᵈ {u = sig i a b} (SigUUCong da da= db=) {uᵈ = (aᵈ , aₛ , a₁ , bᵈ , _)} {u'ᵈ = (a'ᵈ , _ , _ , b'ᵈ , _)} = ap-irr-sigStr refl (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq+ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db= (ap-irr-ElStr refl (⟦⟧TmEq Γᵈ da=)))
⟦⟧TmEq Γᵈ {u = pair A B a b} (PairCong dA dA= dB= da= db=) = ap-irr-pairStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq Γᵈ db=)
⟦⟧TmEq Γᵈ {u = pr1 A B u} (Pr1Cong dA dA= dB= du=) = ap-irr-pr1Str refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq Γᵈ {u = pr2 A B u} (Pr2Cong dA dA= dB= du=) = ap-irr-pr2Str refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ du=)

⟦⟧TmEq Γᵈ EmptyUUCong = refl
⟦⟧TmEq Γᵈ (EmptyelimCong dA= du=) = ap-irr-emptyelimStr refl (⟦⟧TyEq (Γᵈ , tt , tt) dA=) (⟦⟧TmEq Γᵈ du=)

⟦⟧TmEq Γᵈ UnitUUCong = refl
⟦⟧TmEq Γᵈ TTCong = refl
⟦⟧TmEq Γᵈ (UnitelimCong dA= ddtt= du=) = ap-irr-unitelimStr refl (⟦⟧TyEq (Γᵈ , tt , tt) dA=) (⟦⟧TmEq Γᵈ ddtt=) (⟦⟧TmEq Γᵈ du=)

⟦⟧TmEq Γᵈ NatUUCong = refl
⟦⟧TmEq Γᵈ ZeroCong = refl
⟦⟧TmEq Γᵈ (SucCong du) = ap-irr-sucStr refl (⟦⟧TmEq Γᵈ du)
⟦⟧TmEq Γᵈ {u = natelim P dO dS u} (NatelimCong dP dP= ddO= ddS= du=) =
  ap-irr-natelimStr
    refl
    (⟦⟧TyEq (Γᵈ , tt , tt) dP=)
    (⟦⟧TmEq Γᵈ ddO=)
    (⟦⟧TmEq+ ((Γᵈ , (tt , tt)) , ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP , tt) ddS= (⟦⟧TyEq (Γᵈ , tt , tt) dP=))
    (⟦⟧TmEq Γᵈ du=)

⟦⟧TmEq Γᵈ (IdUUCong da= du= dv=) = ap-irr-idStr refl (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq Γᵈ du=) (⟦⟧TmEq Γᵈ dv=)
⟦⟧TmEq Γᵈ (ReflCong dA= du=) = ap-irr-reflStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq {Γ = Γ}  Γᵈ {u = jj A P d a b p} {u' = jj A' P' d' a' b' p'} (JJCong dA dA= dP= dd= da= db= dp=) {uᵈ = (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt)} = ap-irr-jjStr refl
                                                                                  (⟦⟧TyEq Γᵈ dA=)
                                                                                  (ap-irr (λ z p → ⟦ P ⟧Ty z $ p) (! id=) {b' = Pᵈ'} ∙ ⟦⟧TyEq+ (((Γᵈ , (Aᵈ , tt)) , (wAᵈ , tt)) , (idᵈ , tt)) dP= (id= ∙ ap-irr-IdStr wA=wA' wwA=wwA' (ap ss (ap pp wA=wA')) (ap ss (ap idC wA=wA'))))
                                                                                  (⟦⟧TmEq+ (Γᵈ , ((⟦⟧Tyᵈ Γᵈ dA) , tt)) dd= (⟦⟧TyEq Γᵈ dA=))
                                                                                  (⟦⟧TmEq Γᵈ da=)
                                                                                  (⟦⟧TmEq Γᵈ db=)
                                                                                  (⟦⟧TmEq Γᵈ dp=)
                                                               where
                                                                 X = ⟦ Γ ⟧Ctx $ Γᵈ                                                               
                                                                 [A] = ⟦ A ⟧Ty X $ Aᵈ
                                                                 wAᵈ : isDefined (⟦ weakenTy A ⟧Ty [A])
                                                                 wAᵈ = ⟦weaken⟧Tyᵈ A Aᵈ A=
                                                                 wA= = ⟦weaken⟧Ty= A Aᵈ A=
                                                                 A=A' = ⟦⟧TyEq Γᵈ dA=
                                                                 wA=wA' = ap-irr-star (ap pp A=A') A=A'
                                                                 wwA=wwA' = ap-irr-star (ap pp wA=wA') wA=wA'
                                                                 [wA] = ⟦ weakenTy A ⟧Ty [A] $ wAᵈ
                                                                 [wA]-ft : ft [wA] ≡ [A]
                                                                 [wA]-ft = ⟦⟧Ty-ft (weakenTy A)
                                                                 wwAᵈ : isDefined (⟦ weakenTy (weakenTy A) ⟧Ty [wA])
                                                                 wwAᵈ = ⟦weaken⟧Tyᵈ (weakenTy A) wAᵈ [wA]-ft
                                                                 wwA= = ⟦weaken⟧Ty= (weakenTy A) wAᵈ [wA]-ft
                                                                 [wwA] = ⟦ weakenTy (weakenTy A) ⟧Ty [wA] $ wwAᵈ
                                                                 [wwA]-ft : ft [wwA] ≡ [wA]
                                                                 [wwA]-ft = ⟦⟧Ty-ft (weakenTy (weakenTy A))
                                                                 idᵈ : isDefined (⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [wA])
                                                                 idᵈ = (wwAᵈ , [wwA]-ft , tt , varCₛ (prev last) [wA] , (varC+₁ last [wA]-ft (varCL₁ ∙ wA=) ∙ wwA=) , tt , varCₛ last [wA] , (varCL₁ ∙ wwA=) , tt)
                                                                 id= = ap-irr-IdStr (!  wA=) (! wwA= ∙ ap-irr-star (ap pp (! wA=)) (! wA=)) (ap ss (ap pp (! wA=))) (ap ss (ap idC (! wA=))) {v'ₛ = ssₛ} {v'₁ = ss₁ id₁ ∙ ap-irr-star (id-left pp₀) refl}
                                                                 [id] = ⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [wA] $ idᵈ
                                                                 Pᵈ' : isDefined (⟦ P ⟧Ty [id])
                                                                 Pᵈ' = cong⟦⟧Tyᵈ {A = P} id= Pᵈ
      
⟦⟧TmEq Γᵈ {u = match A B C da' db (inl A B a)} (BetaInl dA dB dC dda ddb da) = betaInlStr ∙ ! (⟦subst⟧Tm= da' (⟦⟧Tmᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dda) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))
⟦⟧TmEq Γᵈ {u = match A B C da db' (inr A B b)} (BetaInr dA dB dC dda ddb db) = betaInrStr ∙ ! (⟦subst⟧Tm= db' (⟦⟧Tmᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dB , tt) ddb) b (⟦⟧Tmᵈ Γᵈ db) (⟦⟧Tm₁ Γᵈ db))

⟦⟧TmEq Γᵈ {u = app A B (lam A B u) a} (BetaPi dA dB du da) = betaPiStr ∙ ! (⟦subst⟧Tm= u (⟦⟧Tmᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) du) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))
⟦⟧TmEq Γᵈ (BetaSig1 dA dB da db) = betaSig1Str
⟦⟧TmEq Γᵈ (BetaSig2 dA dB da db) = betaSig2Str
⟦⟧TmEq Γᵈ (BetaUnit dA dtt) = betaUnitStr
⟦⟧TmEq Γᵈ (BetaNatZero dP ddO ddS) = betaNatZeroStr
⟦⟧TmEq {Γ = Γ} Γᵈ {u = natelim P dO dS (suc u)} (BetaNatSuc dP ddO ddS du) =
  betaNatSucStr ∙ ! (⟦subst2⟧Tm= (⟦⟧Ty-ft P) NatStr= dS dSᵈ u uᵈ (⟦⟧Tm₁ Γᵈ du) (natelim P dO dS u) natelimᵈ natelimStr₁)
    where
      Pᵈ = ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP
      dOᵈ = ⟦⟧Tmᵈ Γᵈ ddO
      dO₁ = ⟦⟧Tm₁ Γᵈ ddO ∙ ⟦subst⟧Ty= P Pᵈ zero tt zeroStr₁
      dSᵈ = ⟦⟧Tmᵈ ((Γᵈ , tt , tt) , Pᵈ , tt) ddS
      dS₁ : ∂₁ (⟦ dS ⟧Tm (⟦ P ⟧Ty (NatStr (⟦ Γ ⟧Ctx $ Γᵈ)) $ Pᵈ) $ dSᵈ)
            ≡ T-dS₁ (⟦ Γ ⟧Ctx $ Γᵈ) (⟦ P ⟧Ty (NatStr (⟦ Γ ⟧Ctx $ Γᵈ)) $ ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP) (⟦⟧Ty-ft P)
      dS₁ = ⟦⟧Tm₁ ((Γᵈ , tt , tt) , Pᵈ , tt) ddS
            ∙ ⟦subst⟧Ty= (weakenTy' (prev last) (weakenTy' (prev last) P))
                         (⟦weaken⟧Ty+ᵈ (weakenTy' (prev last) P) (⟦weaken⟧Ty+ᵈ P Pᵈ NatStr= NatStr= (NatStrNat pp₀)) (⟦⟧Ty-ft P) NatStr= (NatStrNat pp₀))
                         (suc (var (prev last)))
                         (tt , ssₛ , (varC+₁ last (⟦⟧Ty-ft P) varCL₁ ∙ ! (star-comp {g₀ = pp₀}) ∙ NatStrNat (comp₀ ∙ pp₀)) , tt)
                         sucStr₁
            ∙ ap-irr-star refl (! (ap-irr-star (ap-irr-qq refl (NatStrNat pp₀))
                                               (⟦weaken⟧Ty+= P Pᵈ NatStr= NatStr= (NatStrNat pp₀))
                                  ∙ ⟦weaken⟧Ty+= (weakenTy' (prev last) P) (⟦weaken⟧Ty+ᵈ P Pᵈ NatStr= NatStr= (NatStrNat pp₀)) (⟦⟧Ty-ft P) NatStr= (NatStrNat pp₀)))
      uᵈ = ⟦⟧Tmᵈ Γᵈ du
      natelimᵈ = (Pᵈ , ⟦⟧Ty-ft P , dOᵈ , ⟦⟧Tmₛ dO , dO₁ , dSᵈ , ⟦⟧Tmₛ dS , dS₁ , uᵈ , ⟦⟧Tmₛ u , ⟦⟧Tm₁ Γᵈ du , tt)
⟦⟧TmEq {Γ = Γ} Γᵈ {u = jj A P d a a (refl A a)} (BetaIdRefl dA dP dd da) =
  betaIdStr ∙ ! (⟦subst⟧Tm= d (⟦⟧Tmᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dd) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))
    

⟦⟧TmEq Γᵈ {u = u} {u' = match A B _ _ _ _} (EtaSum dA dB du) =
  etaSumStr {uₛ = ⟦⟧Tmₛ u} {u₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = (⟦⟧Tyᵈ Γᵈ dA , ⟦⟧Ty-ft A , ⟦⟧Tyᵈ Γᵈ dB , ⟦⟧Ty-ft B , tt)} du}
  ∙ ap-irr-matchStr refl refl refl
                    (⟦weaken⟧Ty= (sum A B) (⟦⟧Tyᵈ Γᵈ dA , ⟦⟧Ty-ft A , ⟦⟧Tyᵈ Γᵈ dB , ⟦⟧Ty-ft B , tt) SumStr=)
                    (ap-irr-inlStr refl (⟦weaken⟧Ty= A (⟦⟧Tyᵈ Γᵈ dA) (⟦⟧Ty-ft A)) (⟦weaken⟧Ty= B (⟦⟧Tyᵈ Γᵈ dB) (⟦⟧Ty-ft A)) refl)
                    (ap-irr-inrStr refl (⟦weaken⟧Ty= A (⟦⟧Tyᵈ Γᵈ dA) (⟦⟧Ty-ft B)) (⟦weaken⟧Ty= B (⟦⟧Tyᵈ Γᵈ dB) (⟦⟧Ty-ft B)) refl) refl
⟦⟧TmEq Γᵈ {u = f} {u' = lam A B _} (EtaPi dA dB df) =
  etaPiStr {fₛ = ⟦⟧Tmₛ f} {f₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = ⟦⟧Tyᵈ Γᵈ dA , ⟦⟧Ty-ft A , ⟦⟧Tyᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB , ⟦⟧Ty-ft B , tt} df}
  ∙ ap-irr-lamStr refl refl refl
     (ap-irr-appStr refl (⟦weaken⟧Ty= A (⟦⟧Tyᵈ Γᵈ dA) (⟦⟧Ty-ft A))
                         (⟦weaken⟧Ty+= B (⟦⟧Tyᵈ (Γᵈ , (⟦⟧Tyᵈ Γᵈ dA) , tt) dB) (⟦⟧Ty-ft A) (⟦⟧Ty-ft A) (⟦weaken⟧Ty= A (⟦⟧Tyᵈ Γᵈ dA) (⟦⟧Ty-ft A)))
                         (⟦weaken⟧Tm= f (⟦⟧Tmᵈ Γᵈ df) (⟦⟧Ty-ft A))
                         refl)
⟦⟧TmEq Γᵈ (EtaSig dA dB du) =
  etaSigStr

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
  , (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ UUStrNat (⟦⟧Mor₀ δ))
  , ⟦tsubst⟧Tmᵈ b bᵈ δ δᵈ
  , ⟦⟧Tmₛ (b [ δ ]Tm)
  , (⟦tsubst⟧Tm₁ b bᵈ b₁ δ δᵈ ∙ UUStrNat (⟦⟧Mor₀ δ))
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
⟦tsubst⟧Tmᵈ (match A B C da db u) (Aᵈ , A= , Bᵈ , B= , Cᵈ , C= , daᵈ , daₛ , da₁ , dbᵈ , dbₛ , db₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ = {- Termination? -}
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ
  , ⟦⟧Ty-ft (A [ δ ]Ty)
  , ⟦tsubst⟧Tyᵈ B Bᵈ δ δᵈ
  , ⟦⟧Ty-ft (B [ δ ]Ty)
  , ⟦tsubst⟧Ty+ᵈ C Cᵈ δ δᵈ SumStr= (⟦tsubst⟧Ty= (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ)
  , ⟦⟧Ty-ft (C [ weakenMor+ δ ]Ty)
  , ⟦tsubst⟧Tm+ᵈ da daᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
  , ⟦⟧Tmₛ (da [ weakenMor+ δ ]Tm)
  , (⟦tsubst⟧Tm+₁ da daᵈ da₁ δ δᵈ T-da₁= (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ∙ T-da₁Nat (⟦⟧Mor₀ δ) ∙ ap-irr-T-da₁ refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) (⟦tsubst⟧Ty= B Bᵈ δ δᵈ) (⟦tsubst⟧Ty+= C Cᵈ δ δᵈ SumStr= (⟦tsubst⟧Ty= (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ)))
  , ⟦tsubst⟧Tm+ᵈ db dbᵈ δ δᵈ B= (⟦tsubst⟧Ty= B Bᵈ δ δᵈ)
  , ⟦⟧Tmₛ (db [ weakenMor+ δ ]Tm)
  , (⟦tsubst⟧Tm+₁ db dbᵈ db₁ δ δᵈ T-db₁= (⟦⟧Ty-ft B) (⟦tsubst⟧Ty= B Bᵈ δ δᵈ) ∙ T-db₁Nat (⟦⟧Mor₀ δ) ∙ ap-irr-T-db₁ refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) (⟦tsubst⟧Ty= B Bᵈ δ δᵈ) (⟦tsubst⟧Ty+= C Cᵈ δ δᵈ SumStr= (⟦tsubst⟧Ty= (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ)))
  , ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ
  , ⟦⟧Tmₛ (u [ δ ]Tm)
  , (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ)
  , tt)

⟦tsubst⟧Tmᵈ (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ UUStrNat (⟦⟧Mor₀ δ)) ,
  ⟦tsubst⟧Tm+ᵈ b bᵈ δ δᵈ ElStr= (ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)) ,
  ⟦⟧Tmₛ (b [ weakenMor+ δ ]Tm) ,
  (⟦tsubst⟧Tm+₁ b bᵈ b₁ δ δᵈ UUStr= ElStr= (ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)) ∙ UUStrNat (qq₀ ∙ ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ))) , tt)
  
⟦tsubst⟧Tmᵈ (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tm+ᵈ u uᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦⟧Tmₛ (u [ weakenMor+ δ ]Tm) ,
   (⟦tsubst⟧Tm+₁ u uᵈ u₁ δ δᵈ B= A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ∙ ⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) , tt)
     
⟦tsubst⟧Tmᵈ (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ f fᵈ δ δᵈ ,
   ⟦⟧Tmₛ (f [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ f fᵈ f₁ δ δᵈ ∙ PiStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-PiStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) ,
   ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
   ⟦⟧Tmₛ (a [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) , tt)

⟦tsubst⟧Tmᵈ (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ ⟦tsubst⟧Ty= (uu i) tt δ δᵈ) ,
  ⟦tsubst⟧Tm+ᵈ b bᵈ δ δᵈ ElStr= (ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)) ,
  ⟦⟧Tmₛ (b [ weakenMor+ δ ]Tm) ,
  (⟦tsubst⟧Tm+₁ b bᵈ b₁ δ δᵈ UUStr= ElStr= (ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)) ∙ UUStrNat (qq₀ ∙ ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ))) , tt)

⟦tsubst⟧Tmᵈ (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦⟧Ty-ft (A [ δ ]Ty) ,
  ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
  ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
  ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
  ⟦tsubst⟧Tmᵈ b bᵈ δ δᵈ ,
  ⟦⟧Tmₛ (b [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ b bᵈ b₁ δ δᵈ ∙ starstar A= aₛ ∙ ap-irr-star (⟦tsubst⟧Tm= a aᵈ δ δᵈ) (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) , tt ) 

⟦tsubst⟧Tmᵈ (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦⟧Ty-ft (A [ δ ]Ty) ,
  ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
  ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
  ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
  ⟦⟧Tmₛ (u [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ SigStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-SigStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) , tt)

⟦tsubst⟧Tmᵈ (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦⟧Ty-ft (A [ δ ]Ty) ,
  ⟦tsubst⟧Ty+ᵈ B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
  ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
  ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
  ⟦⟧Tmₛ (u [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ SigStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-SigStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) , tt)

⟦tsubst⟧Tmᵈ (empty i) tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ (emptyelim A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ EmptyStr= (EmptyStrNat (⟦⟧Mor₀ δ)) ,
   ⟦⟧Ty-ft (A [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ EmptyStrNat (⟦⟧Mor₀ δ)) , tt)

⟦tsubst⟧Tmᵈ (unit i) tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ tt tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ (unitelim A dtt u) (Aᵈ , A= , dttᵈ , dttₛ , dtt₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ UnitStr= (UnitStrNat (⟦⟧Mor₀ δ)) ,
   ⟦⟧Ty-ft (A [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ dtt dttᵈ δ δᵈ ,
   ⟦⟧Tmₛ (dtt [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ dtt dttᵈ dtt₁ δ δᵈ ∙ starstar UnitStr= ttStrₛ ∙ ap-irr-star (ttStrNat (⟦⟧Mor₀ δ)) (⟦tsubst⟧Ty+= A Aᵈ δ δᵈ UnitStr= (UnitStrNat (⟦⟧Mor₀ δ)))) , 
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ UnitStrNat (⟦⟧Mor₀ δ)) , tt)

⟦tsubst⟧Tmᵈ (nat i) tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ zero tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ (suc u) (uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ NatStrNat (⟦⟧Mor₀ δ)) , tt)
⟦tsubst⟧Tmᵈ {X = X} (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (Pᵈs , P=s , dOᵈs , dOₛs , dO₁s , dSᵈs , dSₛs , dS₁s , uᵈs , uₛs , u₁s , tt)
    where
      naturalityNat = NatStrNat (⟦⟧Mor₀ δ)      
      sP= = ⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= naturalityNat
      Pᵈs = ⟦tsubst⟧Ty+ᵈ P Pᵈ δ δᵈ NatStr= naturalityNat
      P=s = ⟦⟧Ty-ft (P [ weakenMor+ δ ]Ty)
      dOᵈs = ⟦tsubst⟧Tmᵈ dO dOᵈ δ δᵈ
      dOₛs = ⟦⟧Tmₛ (dO [ δ ]Tm)
      dO₁s = ⟦tsubst⟧Tm₁ dO dOᵈ dO₁ δ δᵈ ∙ starstar NatStr= zeroStrₛ ∙ ap-irr-star (zeroStrNat (⟦⟧Mor₀ δ)) sP= 
      dSᵈs = ⟦tsubst⟧Tm++ᵈ dS dSᵈ δ δᵈ P= NatStr= sP=
      dSₛs = ⟦⟧Tmₛ (dS [ weakenMor+ (weakenMor+ δ) ]Tm)
      dS₁s = ⟦tsubst⟧Tm++₁ dS dSᵈ dS₁ δ δᵈ T-dS₁= P= NatStr= sP=
             ∙ T-dS₁Nat (⟦⟧Mor₀ δ) ∙ ap-irr-T-dS₁ refl sP=
      uᵈs = ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ
      uₛs = ⟦⟧Tmₛ (u [ δ ]Tm)
      u₁s = ⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ naturalityNat

⟦tsubst⟧Tmᵈ (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
   ⟦⟧Tmₛ (a [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ UUStrNat (⟦⟧Mor₀ δ)) ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)) ,
   ⟦tsubst⟧Tmᵈ v vᵈ δ δᵈ ,
   ⟦⟧Tmₛ (v [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ v vᵈ v₁ δ δᵈ ∙ ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)) , tt)
⟦tsubst⟧Tmᵈ (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) , tt)
⟦tsubst⟧Tmᵈ (jj A P d a b p) (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt) δ δᵈ =
  (Aᵈs , A=s , Pᵈs , P=s , dᵈs , dₛs , d₁s , aᵈs , aₛs , a₁s , bᵈs , bₛs , b₁s , pᵈs , pₛs , p₁s , tt)
    where
      Aᵈs = ⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ
      A=s = ⟦⟧Ty-ft (A [ δ ]Ty)
      sA= = ⟦tsubst⟧Ty= A Aᵈ δ δᵈ
      Pᵈs = ⟦tsubst⟧Ty+++ᵈ P Pᵈ δ δᵈ T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (⟦⟧Mor₀ δ) ∙ ap-irr (T-ftP _) sA=)
      P=s = ⟦⟧Ty-ft (P [ weakenMor+ (weakenMor+ (weakenMor+ δ)) ]Ty)
      sP= = ⟦tsubst⟧Ty+++= P Pᵈ δ δᵈ T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (⟦⟧Mor₀ δ) ∙ ap-irr (T-ftP _) sA=)
      dᵈs = ⟦tsubst⟧Tm+ᵈ d dᵈ δ δᵈ A= sA=
      dₛs = ⟦⟧Tmₛ (d [ weakenMor+ δ ]Tm)
      d₁s = ⟦tsubst⟧Tm+₁ d dᵈ d₁ δ δᵈ T-d₁= A= sA= ∙ T-d₁Nat (⟦⟧Mor₀ δ) ∙ ap-irr-T-d₁ refl sA= sP= 
      aᵈs = ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ
      aₛs = ⟦⟧Tmₛ (a [ δ ]Tm)
      a₁s = ⟦tsubst⟧Tm₁ a aᵈ a₁ δ δᵈ ∙ sA=
      bᵈs = ⟦tsubst⟧Tmᵈ b bᵈ δ δᵈ
      bₛs = ⟦⟧Tmₛ (b [ δ ]Tm)
      b₁s = ⟦tsubst⟧Tm₁ b bᵈ b₁ δ δᵈ ∙ sA=
      pᵈs = ⟦tsubst⟧Tmᵈ p pᵈ δ δᵈ
      pₛs = ⟦⟧Tmₛ (p [ δ ]Tm)
      p₁s = ⟦tsubst⟧Tm₁ p pᵈ p₁ δ δᵈ ∙ IdStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-IdStr refl sA= (⟦tsubst⟧Tm= a aᵈ δ δᵈ) (⟦tsubst⟧Tm= b bᵈ δ δᵈ)
  

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
                      (⟦tsubst⟧Tm+= b bᵈ δ δᵈ ElStr= (ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)))
                      
⟦tsubst⟧Tm= (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  lamStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-lamStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                       (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                       (⟦tsubst⟧Tm+= u uᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
⟦tsubst⟧Tm= (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) δ δᵈ =
  appStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-appStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                       (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                       (⟦tsubst⟧Tm= f fᵈ δ δᵈ)
                       (⟦tsubst⟧Tm= a aᵈ δ δᵈ)

⟦tsubst⟧Tm= (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  sigStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-sigStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                       (⟦tsubst⟧Tm+= b bᵈ δ δᵈ ElStr= (ElStrNat (⟦⟧Mor₀ δ) ∙ ap-irr-ElStr refl (⟦tsubst⟧Tm= a aᵈ δ δᵈ)))

⟦tsubst⟧Tm= (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  pairStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-pairStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                        (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                        (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                        (⟦tsubst⟧Tm= b bᵈ δ δᵈ)

⟦tsubst⟧Tm= (pr1 A B u) (Aᵈ , A= , Bᵈ  , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  pr1StrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-pr1Str refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                       (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                       (⟦tsubst⟧Tm= u uᵈ δ δᵈ)

⟦tsubst⟧Tm= (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  pr2StrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-pr2Str refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                       (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                       (⟦tsubst⟧Tm= u uᵈ δ δᵈ)

⟦tsubst⟧Tm= (empty i) tt δ δᵈ =
  emptyStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= (emptyelim A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  emptyelimStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-emptyelimStr refl (⟦tsubst⟧Ty+= A Aᵈ δ δᵈ EmptyStr= (EmptyStrNat (⟦⟧Mor₀ δ))) (⟦tsubst⟧Tm= u uᵈ δ δᵈ)

⟦tsubst⟧Tm= (unit i) tt δ δᵈ =
  unitStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= tt tt δ δᵈ =
  ttStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= (unitelim A dtt u) (Aᵈ , A= , dttᵈ , dttₛ , dtt₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  unitelimStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-unitelimStr refl (⟦tsubst⟧Ty+= A Aᵈ δ δᵈ UnitStr= (UnitStrNat (⟦⟧Mor₀ δ))) (⟦tsubst⟧Tm= dtt dttᵈ δ δᵈ) (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
  
⟦tsubst⟧Tm= (nat i) tt δ δᵈ =
  natStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= zero tt δ δᵈ =
  zeroStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= (suc u) (uᵈ , uₛ , u₁ , tt) δ δᵈ =
  sucStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-sucStr refl (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
⟦tsubst⟧Tm= (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  natelimStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-natelimStr refl (⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= (NatStrNat (⟦⟧Mor₀ δ)))
                           (⟦tsubst⟧Tm= dO dOᵈ δ δᵈ)
                           (⟦tsubst⟧Tm++= dS dSᵈ δ δᵈ P= NatStr= (⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= (NatStrNat (⟦⟧Mor₀ δ))))
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
  ∙ ap-irr-jjStr refl (⟦tsubst⟧Ty= A Aᵈ δ δᵈ )
                      (⟦tsubst⟧Ty+++= P Pᵈ δ δᵈ T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat (⟦⟧Mor₀ δ) ∙ ap-irr (T-ftP _) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)))
                      (⟦tsubst⟧Tm+= d dᵈ δ δᵈ A= (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                      (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                      (⟦tsubst⟧Tm= b bᵈ δ δᵈ)
                      (⟦tsubst⟧Tm= p pᵈ δ δᵈ)



{- To conclude, we prove a few more additional properties, needed for initiality -}

{- Totality of the interpretation function on derivable contexts -}

⟦⟧Ctxᵈ : {Γ : Ctx n} (dΓ : ⊢ Γ) → isDefined (⟦ Γ ⟧Ctx)
⟦⟧Ctxᵈ tt = tt
⟦⟧Ctxᵈ (dΓ , dA) = let Γᵈ = ⟦⟧Ctxᵈ dΓ in (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt)

{- Interpretation of context equalities -}

⟦⟧CtxEq : {Γ Γ' : Ctx n} (dΓ= : ⊢ Γ == Γ') {Γᵈ : isDefined (⟦ Γ ⟧Ctx)} {Γ'ᵈ : isDefined (⟦ Γ' ⟧Ctx)}
        → ⟦ Γ ⟧Ctx $ Γᵈ ≡ ⟦ Γ' ⟧Ctx $ Γ'ᵈ
⟦⟧CtxEq tt = refl
⟦⟧CtxEq (dΓ= , dA=) {Γᵈ = Γᵈ , Aᵈ , tt}
  = ⟦⟧TyEq+ Γᵈ (ConvTyEq dA= (CtxSymm dΓ=)) (⟦⟧CtxEq dΓ=)

{- Interpretation of morphism equalities -}

⟦⟧MorEq : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {Y : Ob m} (dδ= : Γ ⊢ δ == δ' ∷> Δ) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} {δ'ᵈ : isDefined (⟦ δ' ⟧Mor X Y)}
        → ⟦ δ ⟧Mor X Y $ δᵈ ≡ ⟦ δ' ⟧Mor X Y $ δ'ᵈ
⟦⟧MorEq Γᵈ tt = refl
⟦⟧MorEq Γᵈ (dδ= , du=) = ap-irr-comp (ap-irr-qq (⟦⟧MorEq Γᵈ dδ=) refl) (⟦⟧TmEq Γᵈ du=)

{- Interpretation of morphism substitution -}

⟦tsubst⟧Morᵈ : {X : Ob n} {Y Y' : Ob m} {Z : Ob k} (Y= : Y ≡ Y') (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (θ : Mor m k) (θᵈ : isDefined (⟦ θ ⟧Mor Y' Z)) → isDefined (⟦ θ [ δ ]Mor ⟧Mor X Z)
⟦tsubst⟧Mor= : {X : Ob n} {Y Y' : Ob m} {Z : Ob k} (Y= : Y ≡ Y') (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (θ : Mor m k) (θᵈ : isDefined (⟦ θ ⟧Mor Y' Z))
             → ⟦ θ [ δ ]Mor ⟧Mor X Z $ (⟦tsubst⟧Morᵈ Y= δ δᵈ θ θᵈ) ≡ comp (⟦ θ ⟧Mor Y' Z $ θᵈ) (⟦ δ ⟧Mor X Y $ δᵈ) (⟦⟧Mor₀ θ) (⟦⟧Mor₁ δ ∙ Y=)

⟦tsubst⟧Morᵈ refl δ δᵈ ◇ tt = tt
⟦tsubst⟧Morᵈ refl δ δᵈ (θ , u) (θᵈ , uᵈ , θ₁ , u₁ , tt) = (⟦tsubst⟧Morᵈ refl δ δᵈ θ θᵈ , ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ , ⟦⟧Mor₁ (θ [ δ ]Mor) , (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ! (ap-irr-star (⟦tsubst⟧Mor= refl δ δᵈ θ θᵈ) refl ∙ star-comp)) , tt)

⟦tsubst⟧Mor= refl δ δᵈ ◇ θᵈ = ! (ptmor-unique _ _ (comp₀ ∙ ⟦⟧Mor₀ δ) (comp₁ ∙ ptmor₁))
⟦tsubst⟧Mor= refl δ δᵈ (θ , u) (θᵈ , uᵈ , θ₁ , u₁ , tt) =
 let thing = ! assoc ∙ ap-irr-comp (is-section= (ap ft (comp₁ {f = idC _} {g₀ = ⟦⟧Tm₀ u} {f₁ = id₁} ∙ u₁) ∙ ft-star ∙ ⟦⟧Mor₀ θ) (⟦⟧Tmₛ u) (! comp₁)) refl ∙ id-right (⟦⟧Mor₁ δ) in
  ap-irr-comp (ap-irr-qq (⟦tsubst⟧Mor= refl δ δᵈ θ θᵈ) refl ∙ qq-comp) (! (⟦tsubst⟧Tm= u uᵈ δ δᵈ))
  ∙ assoc {f₁ = starTm₁ _ (ft-star ∙ ⟦⟧Mor₀ θ) _ (⟦⟧Tmₛ u) u₁ _} {g₀ = qq₀}
  ∙ ! (assoc ∙ ap-irr-comp refl (ss-qq ∙ ap-irr-comp (ap-irr-qq thing (comp₁ ∙ u₁)) refl))
