{-# OPTIONS --rewriting --prop --without-K --allow-unsolved-metas #-}

open import common
open import typetheory
open import syntx
open import rules
open import contextualcat

module _ (sC : StructuredCCat) where

open StructuredCCat sC
open CCat+ ccat renaming (Mor to MorC; id to idC)

open import partialinterpretation sC

{-- We start by stating the types of the main properties that we are going to prove by mutual induction

Unfortunately we cannot define ⟦weaken⟧ᵈ in terms of ⟦tsubst⟧ᵈ because ⟦tsubst⟧Ty+ᵈ calls
⟦weakenMor+⟧ᵈ on δ, whereas the induction defining ⟦tsubst⟧Tyᵈ is on A.  There is no similar issue
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

⟦weakenTy⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} {Y : Ob (n -F' k)} (A : TyExpr n)
             → isDefined (⟦ A ⟧Ty X)
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → isDefined (⟦ weakenTy' k A ⟧Ty Z)

⟦weakenTm⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} {Y : Ob (n -F' k)} (u : TmExpr n)
             → isDefined (⟦ u ⟧Tm X)
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → isDefined (⟦ weakenTm' k u ⟧Tm Z)

⟦weakenTy⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} {Y : Ob (n -F' k)} (A : TyExpr n)
             → (Aᵈ : isDefined (⟦ A ⟧Ty X))
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → star (qq^ k X+= X=) (⟦ A ⟧Ty X $ Aᵈ) (⟦⟧Ty-ft A) qq^₁ ≡ ⟦ weakenTy' k A ⟧Ty Z $ ⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Z=

⟦weakenTm⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} {Y : Ob (n -F' k)} (u : TmExpr n)
             → (uᵈ : isDefined (⟦ u ⟧Tm X))
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → starTm (qq^ k X+= X=) (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' k u ⟧Tm Z $ ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Z=

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



{-- We now prove a ton of lemmas, mainly special cases of the properties above… -}

{- Type of a weakening -}

⟦weakenTm⟧₁' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} {Y : Ob (n -F' k)} (u : TmExpr n)
             → (uᵈ : isDefined (⟦ u ⟧Tm X))
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Y : Ob (suc n)} (Y= : star^ k X+ X X+= X= ≡ Y)
             → {Z : Ob (suc n)} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Z)
             → ∂₁ (⟦ weakenTm' k u ⟧Tm Y $ ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Y=) ≡ star (qq^ k X+= X=) Z (⟦⟧Tm₁-ft u u₁) qq^₁
⟦weakenTm⟧₁' k u uᵈ X+= X= Y= u₁ = ap ∂₁ (! (⟦weakenTm⟧=' k u uᵈ X+= X= Y=)) ∙ starTm₁ _ (⟦⟧Tm₁-ft u u₁) _ (⟦⟧Tmₛ u) u₁ qq^₁

{- Weakening at [last] -}

⟦weakenTm⟧ᵈ : {X+ : Ob (suc n)} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ X)
            → isDefined (⟦ weakenTm u ⟧Tm X+)
⟦weakenTm⟧ᵈ u uᵈ X= = ⟦weakenTm⟧ᵈ' last u uᵈ X= refl refl

⟦weakenTm⟧= : {X+ : Ob (suc n)} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ X)
            → starTm (pp X+) (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) (pp₁ ∙ X=) ≡ ⟦ weakenTm u ⟧Tm X+ $ ⟦weakenTm⟧ᵈ u uᵈ X=
⟦weakenTm⟧= u uᵈ X= = ap-irr-starTm (! qq^last) refl ∙ ⟦weakenTm⟧=' last u uᵈ X= refl refl

⟦weakenTy⟧ᵈ : {X+ : Ob (suc n)} {X : Ob n} (A : TyExpr n)
            → (Aᵈ : isDefined (⟦ A ⟧Ty X))
            → (X= : ft X+ ≡ X)
            → isDefined (⟦ weakenTy A ⟧Ty X+)
⟦weakenTy⟧ᵈ A Aᵈ X= = ⟦weakenTy⟧ᵈ' last A Aᵈ X= refl refl

⟦weakenTy⟧= : {X+ : Ob (suc n)} {X : Ob n} (A : TyExpr n)
            → (Aᵈ : isDefined (⟦ A ⟧Ty X))
            → (X= : ft X+ ≡ X)
            → star (pp X+) (⟦ A ⟧Ty X $ Aᵈ) (⟦⟧Ty-ft A) (pp₁ ∙ X=) ≡ ⟦ weakenTy A ⟧Ty X+ $ ⟦weakenTy⟧ᵈ A Aᵈ X=
⟦weakenTy⟧= A Aᵈ X= = ap-irr-star (! qq^last) refl ∙ ⟦weakenTy⟧=' last A Aᵈ X= refl refl

⟦weakenTm⟧₁ : {X+ : Ob (suc n)} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ X)
            → {Z : Ob (suc n)} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Z)
            → ∂₁ (⟦ weakenTm u ⟧Tm X+ $ ⟦weakenTm⟧ᵈ u uᵈ X=) ≡ star (pp X+) Z (⟦⟧Tm₁-ft u u₁) (pp₁ ∙ X=)
⟦weakenTm⟧₁ u uᵈ X= refl = ⟦weakenTm⟧₁' last u uᵈ X= refl refl refl ∙ ap3-irr2 star qq^last refl refl

{- Weakening at [prev k] -}

⟦weakenTy+⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -F' k)} (A : TyExpr (suc n))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
              → isDefined (⟦ weakenTy' (prev k) A ⟧Ty Z)
⟦weakenTy+⟧ᵈ' k A Aᵈ X+= X= refl Y= = ⟦weakenTy⟧ᵈ' (prev k) A Aᵈ X+= X= Y=

⟦weakenTm+⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -F' k)} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
              → isDefined (⟦ weakenTm' (prev k) u ⟧Tm Z)
⟦weakenTm+⟧ᵈ' k u uᵈ X+= X= refl Y= = ⟦weakenTm⟧ᵈ' (prev k) u uᵈ X+= X= Y=

⟦weakenTy+⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -F' k)} (A : TyExpr (suc n))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
              → star+ (qq^ k X+= X=) (⟦ A ⟧Ty X' $ Aᵈ) (⟦⟧Ty-ft A) p qq^₁ ≡ ⟦ weakenTy' (prev k) A ⟧Ty Z $ ⟦weakenTy+⟧ᵈ' k A Aᵈ X+= X= p Y=
⟦weakenTy+⟧=' k A Aᵈ X+= X= refl Y= = ap-irr-star (! qq^prev) refl ∙ ⟦weakenTy⟧=' (prev k) A Aᵈ X+= X= Y=

⟦weakenTm+⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -F' k)} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
              → starTm+ (qq^ k X+= X=) p (⟦ u ⟧Tm X' $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' (prev k) u ⟧Tm Z $ ⟦weakenTm+⟧ᵈ' k u uᵈ X+= X= p Y=
⟦weakenTm+⟧=' k u uᵈ X+= X= refl Y= = ap ss (ap-irr-comp refl (! qq^prev)) ∙ ⟦weakenTm⟧=' (prev k) u uᵈ X+= X= Y=

⟦weakenTm+⟧₁' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} {Y : Ob (n -F' k)} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X+= : ft X+ ≡ Y) (X''= : ft^ k X'' ≡ Y) {Z : Ob (suc (suc n))}
              → (X= : ft X ≡ X')
              → (X'= : ft X' ≡ X'')
              → (Z= : star (qq^ k X+= X''=) X' X'= qq^₁ ≡ Z)
              → (u₁ : ∂₁ (⟦ u ⟧Tm X' $ uᵈ) ≡ X)
              → ∂₁ (⟦ weakenTm' (prev k) u ⟧Tm Z $ ⟦weakenTm+⟧ᵈ' k u uᵈ X+= X''= X'= Z=) ≡ star (qq (qq^ k X+= X''=) X' X'= qq^₁) X X= qq₁
⟦weakenTm+⟧₁' k u uᵈ X+= X''= refl refl Z= u₁ = ⟦weakenTm⟧₁' (prev k) u uᵈ X+= X''= Z= u₁ ∙ ap-irr-star qq^prev refl

{- Weakening at [prev (prev k)] -}

⟦weakenTm++⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {Y : Ob (n -F' k)} {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} (u : TmExpr (suc (suc n)))
               → (uᵈ : isDefined (⟦ u ⟧Tm X))
               → (X+= : ft X+ ≡ Y) (X''= : ft^ k X'' ≡ Y) {Z : Ob (suc (suc (suc n)))} (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (Y= : star+ (qq^ k X+= X''=) X X= X'= qq^₁ ≡ Z)
               → isDefined (⟦ weakenTm' (prev (prev k)) u ⟧Tm Z)
⟦weakenTm++⟧ᵈ' k u uᵈ X+= X''= refl refl Y= = ⟦weakenTm+⟧ᵈ' (prev k) u uᵈ X+= X''= refl (ap-irr-star qq^prev refl ∙ Y=)

⟦weakenTm++⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {Y : Ob (n -F' k)} {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} (u : TmExpr (suc (suc n)))
               → (uᵈ : isDefined (⟦ u ⟧Tm X))
               → (X+= : ft X+ ≡ Y) (X''= : ft^ k X'' ≡ Y) {Z : Ob (suc (suc (suc n)))} (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (Y= : star+ (qq^ k X+= X''=) X X= X'= qq^₁ ≡ Z)
               → starTm++ (qq^ k X+= X''=) X= X'= (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' (prev (prev k)) u ⟧Tm Z $ ⟦weakenTm++⟧ᵈ' k u uᵈ X+= X''= X= X'= Y=
⟦weakenTm++⟧=' k u uᵈ X+= X''= refl refl Y= = ap ss (ap-irr-comp refl (ap-irr-qq (! qq^prev) refl)) ∙ ⟦weakenTm+⟧=' (prev k) u uᵈ X+= X''= refl (ap-irr-star qq^prev refl ∙ Y=)

⟦weakenTm++⟧₁' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {Y : Ob (n -F' k)} {X : Ob (suc (suc (suc n))) } {X' : Ob (suc (suc n))} {X'' : Ob (suc n)} {X''' : Ob n} (u : TmExpr (suc (suc n)))
               → (uᵈ : isDefined (⟦ u ⟧Tm X'))
               → (X+= : ft X+ ≡ Y) (X'''= : ft^ k X''' ≡ Y) {Z : Ob (suc (suc (suc n)))}
               → (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (X''= : ft X'' ≡ X''')
               → (Y= : star+ (qq^ k X+= X'''=) X' X'= X''= qq^₁ ≡ Z)
               → (u₁ : ∂₁ (⟦ u ⟧Tm X' $ uᵈ) ≡ X)
               → ∂₁ (⟦ weakenTm' (prev (prev k)) u ⟧Tm Z $ ⟦weakenTm++⟧ᵈ' k u uᵈ X+= X'''= X'= X''= Y=) ≡ star++ (qq^ k X+= X'''=) X X= X'= X''= qq^₁
⟦weakenTm++⟧₁' k u uᵈ X+= X'''= refl refl refl Y= u₁ = ⟦weakenTm+⟧₁' (prev k) u uᵈ X+= X'''= refl refl (ap-irr-star qq^prev refl ∙ Y=) u₁ ∙ ap-irr-star (ap-irr-qq qq^prev refl) refl

{- Weakening at [prev last] -}

⟦weakenTy+⟧ᵈ : {X+ : Ob (suc n)} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc n))
             → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
             → (X= : ft X+ ≡ X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (pp X+) X' p (pp₁ ∙ X=) ≡ Y)
             → isDefined (⟦ weakenTy' (prev last) A ⟧Ty Y)
⟦weakenTy+⟧ᵈ A Aᵈ X= p Y= = ⟦weakenTy+⟧ᵈ' last A Aᵈ X= refl p (ap-irr-star qq^last refl ∙ Y=)

⟦weakenTy+⟧= : {X+ : Ob (suc n)} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc n))
             → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
             → (X= : ft X+ ≡ X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (pp X+) X' p (pp₁ ∙ X=) ≡ Y)
             → star (qq (pp X+) X' p (pp₁ ∙ X=)) (⟦ A ⟧Ty X' $ Aᵈ) (⟦⟧Ty-ft A) qq₁ ≡ ⟦ weakenTy' (prev last) A ⟧Ty Y $ ⟦weakenTy+⟧ᵈ A Aᵈ X= p Y=
⟦weakenTy+⟧= A Aᵈ X= refl Y= = ap-irr-star (ap-irr-qq (! qq^last) refl) refl ∙ ⟦weakenTy+⟧=' last A Aᵈ X= refl refl (ap-irr-star qq^last refl ∙ Y=)

{- Weakening of morphisms -}

⟦weakenMor⟧ᵈ : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y : Ob m} (δ : Mor n m)
           → isDefined (⟦ δ ⟧Mor X Y)
           → isDefined (⟦ weakenMor δ ⟧Mor X+ Y)
⟦weakenMor⟧= : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y : Ob m} (δ : Mor n m)
           → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
           → ⟦ weakenMor δ ⟧Mor X+ Y $ ⟦weakenMor⟧ᵈ X= δ δᵈ ≡ comp (⟦ δ ⟧Mor X Y $ δᵈ) (pp X+) (⟦⟧Mor₀ δ ∙ ! X=) pp₁

⟦weakenMor⟧ᵈ refl ◇ tt = tt
⟦weakenMor⟧ᵈ {X+ = X+} refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = (⟦weakenMor⟧ᵈ refl δ δᵈ , ⟦weakenTm⟧ᵈ u uᵈ refl , ⟦⟧Mor₁ (weakenMor δ) , (⟦weakenTm⟧₁ u uᵈ refl u₁ ∙ ! star-comp ∙ ! (ap3-irr2 star (⟦weakenMor⟧= refl δ δᵈ) refl refl)) , tt)

⟦weakenMor⟧= refl ◇ tt = ! (ptmor-unique _ _ (comp₀ ∙ pp₀) (comp₁ ∙ pt-unique _))
⟦weakenMor⟧= refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) =
  ap-irr-comp
    (ap-irr-qq
      (⟦weakenMor⟧= refl δ δᵈ)
      refl
     ∙ qq-comp
     ∙ ap-irr-comp refl
       ((ap-irr-qq (! (! assoc ∙ ap-irr-comp (is-section= (ft-star ∙ ⟦⟧Mor₀ δ) (⟦⟧Tmₛ u) u₁) refl ∙ id-right pp₁)) refl)))
    (! ((⟦weakenTm⟧= u uᵈ refl)))
  ∙ assoc {g₁ = qq₁} {h₀ = qq₀}
  ∙ ! (ap-irr-comp refl (ss-qq {f₁ = comp₁ ∙ u₁}))
  ∙ ! assoc

⟦weakenMor+⟧ᵈ : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y+ : Ob (suc m)} {Y : Ob m} (Y= : ft Y+ ≡ Y) (δ : Mor n m)
              → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
              → (_ : star (⟦ δ ⟧Mor X Y $ δᵈ) Y+ Y= (⟦⟧Mor₁ δ) ≡ X+)
              → isDefined (⟦ weakenMor+ δ ⟧Mor X+ Y+)
⟦weakenMor+⟧ᵈ refl refl δ δᵈ p = (⟦weakenMor⟧ᵈ refl δ δᵈ , (tt , (⟦⟧Mor₁ (weakenMor δ) , (varCL₁ {X= = refl} ∙ ap-irr-star refl (! p) ∙ ! star-comp ∙ ap-irr-star (! (⟦weakenMor⟧= refl δ δᵈ)) refl) , tt)))

⟦weakenMor+⟧= : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y+ : Ob (suc m)} {Y : Ob m} (Y= : ft Y+ ≡ Y) (δ : Mor n m)
           → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
           → (p : star (⟦ δ ⟧Mor X Y $ δᵈ) Y+ Y= (⟦⟧Mor₁ δ) ≡ X+)
           → ⟦ weakenMor+ δ ⟧Mor X+ Y+ $ ⟦weakenMor+⟧ᵈ X= Y= δ δᵈ p ≡ qq (⟦ δ ⟧Mor X Y $ δᵈ) Y+ Y= (⟦⟧Mor₁ δ)
⟦weakenMor+⟧= refl refl δ δᵈ p = ap-irr-comp (ap-irr-qq (⟦weakenMor⟧= refl δ δᵈ ∙ refl) refl ∙ qq-comp) refl {f₁' = varCL₁ {X= = refl}} ∙ assoc {g₀ = qq₀ ∙ ap-irr-star refl p} ∙ ap-irr-comp refl (ap-irr-comp (ap-irr-qq (! (id-left pp₀)) p) refl ∙ (! ss-qq)) ∙ id-left (qq₀ ∙ p)


{- Type of a substitution -}

⟦tsubst⟧Tm₁ : {X : Ob n} {Y : Ob m} (u : TmExpr m)
            → (uᵈ : isDefined (⟦ u ⟧Tm Y))
            → (δ : Mor n m)
            → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            → {Z : Ob (suc m)}
            → (u₁ : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ Z)
            → ∂₁ (⟦ u [ δ ]Tm ⟧Tm X $ ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ)
              ≡ star (⟦ δ ⟧Mor X Y $ δᵈ) Z (⟦⟧Tm₁-ft u u₁) (⟦⟧Mor₁ δ)
⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ = ap ∂₁ (! (⟦tsubst⟧Tm= u uᵈ δ δᵈ)) ∙ starTm₁ _ (⟦⟧Tm₁-ft u u₁) _ (⟦⟧Tmₛ u) u₁ (⟦⟧Mor₁ δ)

{- Substitution by a weakenMor+ -}

⟦tsubst⟧Ty+ᵈ : {X+ : Ob (suc n)} {X : Ob n} {Y+ : Ob (suc m)} {Y : Ob m} (A : TyExpr (suc m))
               (Aᵈ : isDefined (⟦ A ⟧Ty Y+))
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (X= : ft X+ ≡ X)
               (Y= : ft Y+ ≡ Y)
               (p : star (⟦ δ ⟧Mor X Y $ δᵈ) Y+ Y= (⟦⟧Mor₁ δ) ≡ X+)
             → isDefined (⟦ A [ weakenMor+ δ ]Ty ⟧Ty X+)
⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ X= Y= p = ⟦tsubst⟧Tyᵈ A Aᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ X= Y= δ δᵈ p)

⟦tsubst⟧Ty+= : {X+ : Ob (suc n)} {X : Ob n} {Y+ : Ob (suc m)} {Y : Ob m} (A : TyExpr (suc m))
               (Aᵈ : isDefined (⟦ A ⟧Ty Y+))
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (X= : ft X+ ≡ X)
               (Y= : ft Y+ ≡ Y)
               (p : star (⟦ δ ⟧Mor X Y $ δᵈ) Y+ Y= (⟦⟧Mor₁ δ) ≡ X+)
             → star+ (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y+ $ Aᵈ) (⟦⟧Ty-ft A) Y= (⟦⟧Mor₁ δ)
               ≡ ⟦ A [ weakenMor+ δ ]Ty ⟧Ty X+ $ ⟦tsubst⟧Ty+ᵈ A Aᵈ δ δᵈ X= Y= p
⟦tsubst⟧Ty+= A Aᵈ δ δᵈ X= Y= p =
  ap-irr-star (! (⟦weakenMor+⟧= X= Y= δ δᵈ p)) refl
  ∙ ⟦tsubst⟧Ty= A Aᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ X= Y= δ δᵈ p)

⟦tsubst⟧Tm+ᵈ : {X+ : Ob (suc n)} {X : Ob n} {Y+ : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc m))
               (uᵈ : isDefined (⟦ u ⟧Tm Y+))
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (X= : ft X+ ≡ X)
               (Y= : ft Y+ ≡ Y)
               (p : star (⟦ δ ⟧Mor X Y $ δᵈ) Y+ Y= (⟦⟧Mor₁ δ) ≡ X+)
              → isDefined (⟦ u [ weakenMor+ δ ]Tm ⟧Tm X+)
⟦tsubst⟧Tm+ᵈ u uᵈ δ δᵈ X= Y= p = ⟦tsubst⟧Tmᵈ u uᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ X= Y= δ δᵈ p)

⟦tsubst⟧Tm+= : {X+ : Ob (suc n)} {X : Ob n} {Y+ : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc m))
               (uᵈ : isDefined (⟦ u ⟧Tm Y+))
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (X= : ft X+ ≡ X)
               (Y= : ft Y+ ≡ Y)
               (p : star (⟦ δ ⟧Mor X Y $ δᵈ) Y+ Y= (⟦⟧Mor₁ δ) ≡ X+)
             → starTm+ (⟦ δ ⟧Mor X Y $ δᵈ) Y= (⟦ u ⟧Tm Y+ $ uᵈ) (⟦⟧Tm₀ u) (⟦⟧Mor₁ δ)
               ≡ ⟦ u [ weakenMor+ δ ]Tm ⟧Tm X+ $ ⟦tsubst⟧Tm+ᵈ u uᵈ δ δᵈ X= Y= p
⟦tsubst⟧Tm+= u uᵈ δ δᵈ X= Y= p =
  ap ss (ap-irr-comp refl (! (⟦weakenMor+⟧= X= Y= δ δᵈ p)))
  ∙ ⟦tsubst⟧Tm= u uᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ X= Y= δ δᵈ p)

⟦tsubst⟧Tm+₁ : {X+ : Ob (suc n)} {X : Ob n} {Y+ : Ob (suc m)} {Y : Ob m} (u : TmExpr (suc m))
               (uᵈ : isDefined (⟦ u ⟧Tm Y+))
               (δ : Mor n m)
               (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
               (X= : ft X+ ≡ X)
               (Y= : ft Y+ ≡ Y)
               (p : star (⟦ δ ⟧Mor X Y $ δᵈ) Y+ Y= (⟦⟧Mor₁ δ) ≡ X+)
              → {Z : Ob (suc (suc m))} (Z= : ft Z ≡ Y+) (u₁ : ∂₁ (⟦ u ⟧Tm Y+ $ uᵈ) ≡ Z)
              → ∂₁ (⟦ u [ weakenMor+ δ ]Tm ⟧Tm X+ $ ⟦tsubst⟧Tm+ᵈ u uᵈ δ δᵈ X= Y= p) ≡ star+ (⟦ δ ⟧Mor X Y $ δᵈ) Z Z= Y= (⟦⟧Mor₁ δ)
⟦tsubst⟧Tm+₁ u uᵈ δ δᵈ X= Y= p Z= u₁ = ! (ap ∂₁ (⟦tsubst⟧Tm+= u uᵈ δ δᵈ X= Y= p)) ∙ starTm+₁ (⟦ δ ⟧Mor _ _ $ δᵈ) Z= Y= (⟦ u ⟧Tm _ $ uᵈ) (⟦⟧Tmₛ u) u₁ (⟦⟧Mor₁ δ)

{- Substitution by a weakenMor+ ^2 -}

{-
-- Unused
-- ⟦tsubst⟧Ty++= : {X+ : Ob (suc (suc n))} {X : Ob n} {Y+ : Ob (suc (suc m))} {Y : Ob m} (A : TyExpr (suc (suc m)))
--                 (Aᵈ : isDefined (⟦ A ⟧Ty Y+))
--                 (δ : Mor n m)
--                 (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
--                 (X= : ft (ft X+) ≡ X)
--                 (Y= : ft (ft Y+) ≡ Y)
--               → star++ (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y+ $ Aᵈ) (⟦⟧Ty-ft A) refl (⟦⟧Mor₁ δ ∙ ! Y=)
--                 ≡ ⟦ A [ weakenMor+ (weakenMor+ δ) ]Ty ⟧Ty X+ $ ⟦tsubst⟧Tyᵈ A Aᵈ (weakenMor+ (weakenMor+ δ)) (⟦weakenMor+⟧ᵈ refl refl (weakenMor+ δ) (⟦weakenMor+⟧ᵈ X= Y= δ δᵈ {!!}) (ap2-irr star (⟦weakenMor+⟧= X= Y= δ δᵈ {!!}) refl ∙ {!!}))
-- ⟦tsubst⟧Ty++= A Aᵈ δ δᵈ X= Y= = {!!}
-}

⟦tsubst⟧Tm++ᵈ : {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} {Y : Ob (suc (suc m))} {Y' : Ob (suc m)} {Y'' : Ob m} (u : TmExpr (suc (suc m)))
              → (uᵈ : isDefined (⟦ u ⟧Tm Y))
              → (δ : Mor n m)
              → (δᵈ : isDefined (⟦ δ ⟧Mor X'' Y''))
              → (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (Y= : ft Y ≡ Y') (Y'= : ft Y' ≡ Y'')
              → (p : star+ (⟦ δ ⟧Mor X'' Y'' $ δᵈ) Y Y= Y'= (⟦⟧Mor₁ δ) ≡ X)
              → isDefined (⟦ u [ weakenMor+ (weakenMor+ δ) ]Tm ⟧Tm X)
⟦tsubst⟧Tm++ᵈ u uᵈ δ δᵈ X= X'= Y= Y'= p = let q = ! qq₀ ∙ ! ft-star ∙ ap ft p ∙ X= in ⟦tsubst⟧Tm+ᵈ u uᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ X'= Y'= δ δᵈ q) X= Y= (ap-irr-star (⟦weakenMor+⟧= X'= Y'= δ δᵈ q) refl ∙ p)

-- TODO : make something prettier
⟦tsubst⟧Tm++= : {X+ : Ob (suc (suc n))} {X : Ob n} {Y+ : Ob (suc (suc m))} {Y : Ob m} (u : TmExpr (suc (suc m)))
                (uᵈ : isDefined (⟦ u ⟧Tm Y+))
                (δ : Mor n m)
                (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
                {X' : Ob (suc n)}
                (X= : ft X+ ≡ X')
                (X'= : ft X' ≡ X)
                {Y+' : Ob (suc m)}
                (Y'= : ft Y+ ≡ Y+')
                (Y= : ft Y+' ≡ Y)
                (p : star (qq (⟦ δ ⟧Mor X Y $ δᵈ) Y+' Y= (⟦⟧Mor₁ δ)) Y+ Y'= qq₁ ≡ X+)
                {w : _}
              → starTm++ (⟦ δ ⟧Mor X Y $ δᵈ) Y'= Y= (⟦ u ⟧Tm Y+ $ uᵈ) (⟦⟧Tm₀ u) (⟦⟧Mor₁ δ)
                ≡ ⟦ u [ weakenMor+ (weakenMor+ δ) ]Tm ⟧Tm X+ $ w
⟦tsubst⟧Tm++= u uᵈ δ δᵈ X= X'= Y+= Y= p =
  let q = ! qq₀ ∙ ! ft-star ∙ ap ft p
  in
  ap ss (ap-irr-comp refl (ap-irr-qq (! (⟦weakenMor+⟧= X'= Y= δ δᵈ (q ∙ X=))) refl))
  ∙ ⟦tsubst⟧Tm+= u uᵈ (weakenMor+ δ) ((⟦weakenMor+⟧ᵈ X'= Y= δ δᵈ (q ∙ X=))) X= Y+= (ap-irr-star (⟦weakenMor+⟧= X'= Y= δ δᵈ (q ∙ X=)) refl ∙ p)

⟦tsubst⟧Tm++₁ : {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} {Y : Ob (suc (suc m))} {Y' : Ob (suc m)} {Y'' : Ob m} (u : TmExpr (suc (suc m)))
              → (uᵈ : isDefined (⟦ u ⟧Tm Y))
              → (δ : Mor n m)
              → (δᵈ : isDefined (⟦ δ ⟧Mor X'' Y''))
              → (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (Y= : ft Y ≡ Y') (Y'= : ft Y' ≡ Y'')
              → (p : star+ (⟦ δ ⟧Mor X'' Y'' $ δᵈ) Y Y= Y'= (⟦⟧Mor₁ δ) ≡ X)
              → {Z : Ob (suc (suc (suc m)))} (Z= : ft Z ≡ Y) (u₁ : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ Z)
              → ∂₁ (⟦ u [ weakenMor+ (weakenMor+ δ) ]Tm ⟧Tm X $ ⟦tsubst⟧Tm++ᵈ u uᵈ δ δᵈ X= X'= Y= Y'= p) ≡ star++ (⟦ δ ⟧Mor X'' Y'' $ δᵈ) Z Z= Y= Y'= (⟦⟧Mor₁ δ)
⟦tsubst⟧Tm++₁ u uᵈ δ δᵈ X= X'= Y= Y'= p Z= u₁ = ap ∂₁ (! (⟦tsubst⟧Tm++= u uᵈ δ δᵈ X= X'= Y= Y'= p)) ∙ starTm++₁ (⟦ δ ⟧Mor _ _ $ δᵈ) Z= Y= Y'= (⟦ u ⟧Tm _ $ uᵈ) (⟦⟧Tmₛ u) u₁ (⟦⟧Mor₁ δ)

{- Interpretation of the identity morphism -}

⟦idMor⟧ᵈ : {X Y : Ob n} → Y ≡ X → isDefined (⟦ idMor n ⟧Mor X Y)
⟦idMor⟧= : {X Y : Ob n} (p : Y ≡ X) → ⟦ idMor n ⟧Mor X Y $ ⟦idMor⟧ᵈ p ≡ idC X

⟦idMor⟧ᵈ {zero} Y= = tt
⟦idMor⟧ᵈ {suc n} {Y = Y} Y= = ⟦weakenMor+⟧ᵈ refl refl (idMor n) (⟦idMor⟧ᵈ {n = n} (ap ft Y=)) (ap-irr-star (⟦idMor⟧= (ap ft Y=)) Y= ∙ star-id {p = refl})

⟦idMor⟧= {zero} Y= = ! (ptmor-unique _ (idC _) id₀ (id₁ ∙ pt-unique _))
⟦idMor⟧= {suc n} {Y = Y} Y= = ⟦weakenMor+⟧= refl refl (idMor n) (⟦idMor⟧ᵈ {n = n} (ap ft Y=)) (ap-irr-star (⟦idMor⟧= (ap ft Y=)) Y= ∙ star-id {p = refl}) ∙ ap-irr-qq (⟦idMor⟧= (ap ft Y=)) Y= ∙ qq-id {p = refl}

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

⟦subst⟧Tyᵈ : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (B : TyExpr (suc n))
           → isDefined (⟦ B ⟧Ty X)
           → (u : TmExpr n)
           → (uᵈ : isDefined (⟦ u ⟧Tm Y))
           → (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
           → isDefined (⟦ substTy B u ⟧Ty Y)
⟦subst⟧Tyᵈ p B Bᵈ u uᵈ q = ⟦tsubst⟧Tyᵈ B Bᵈ _ (⟦idMor+⟧ᵈ p u uᵈ q)

⟦subst⟧Tmᵈ : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (v : TmExpr (suc n))
            → isDefined (⟦ v ⟧Tm X)
            → (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm Y))
            → (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → isDefined (⟦ substTm v u ⟧Tm Y)
⟦subst⟧Tmᵈ p v vᵈ u uᵈ q = ⟦tsubst⟧Tmᵈ v vᵈ _ (⟦idMor+⟧ᵈ p u uᵈ q)

⟦subst⟧Ty= : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (B : TyExpr (suc n))
             (Bᵈ : isDefined (⟦ B ⟧Ty X))
             (u : TmExpr n)
             (uᵈ : isDefined (⟦ u ⟧Tm Y))
             (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → ⟦ substTy B u ⟧Ty Y $ ⟦subst⟧Tyᵈ p B Bᵈ u uᵈ q ≡ star (⟦ u ⟧Tm Y $ uᵈ) (⟦ B ⟧Ty X $ Bᵈ) (⟦⟧Ty-ft B) q
⟦subst⟧Ty= p B Bᵈ u uᵈ q = ! (⟦tsubst⟧Ty= B Bᵈ _ (⟦idMor+⟧ᵈ p u uᵈ q)) ∙ ap-irr-star (⟦idMor+⟧= p u uᵈ q) refl

⟦subst⟧Tm= : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (v : TmExpr (suc n))
             (vᵈ : isDefined (⟦ v ⟧Tm X))
             (u : TmExpr n)
             (uᵈ : isDefined (⟦ u ⟧Tm Y))
             (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → ⟦ substTm v u ⟧Tm Y $ ⟦subst⟧Tmᵈ p v vᵈ u uᵈ q ≡ starTm (⟦ u ⟧Tm Y $ uᵈ) (⟦ v ⟧Tm X $ vᵈ) (⟦⟧Tm₀ v) q
⟦subst⟧Tm= p v vᵈ u uᵈ q = ! (⟦tsubst⟧Tm= v vᵈ _ (⟦idMor+⟧ᵈ p u uᵈ q)) ∙ ap-irr-starTm (⟦idMor+⟧= p u uᵈ q) refl

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
                                               (star (qq (⟦ u ⟧Tm X''' $ uᵈ) X' X'= u₁)
                                                  X
                                                  X=
                                                  qq₁)
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

cong⟦⟧Ty : {X Y : Ob n} {A : TyExpr n} → X ≡ Y → isDefined (⟦ A ⟧Ty X) → isDefined (⟦ A ⟧Ty Y)
cong⟦⟧Ty refl Aᵈ = Aᵈ

cong⟦⟧Mor : {X : Ob n} {Y Y' : Ob m} {δ : Mor n m} → Y ≡ Y' → isDefined (⟦ δ ⟧Mor X Y) → isDefined (⟦ δ ⟧Mor X Y')
cong⟦⟧Mor refl δᵈ = δᵈ

⟦⟧TyEq+ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {X' : Ob n} {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A'))
          {Aᵈ : isDefined (⟦ A ⟧Ty X)} {A'ᵈ : isDefined (⟦ A' ⟧Ty X')} → X ≡ X' → ⟦ A ⟧Ty X $ Aᵈ ≡ ⟦ A' ⟧Ty X' $ A'ᵈ
⟦⟧TyEq+ Γᵈ dA= refl = ⟦⟧TyEq Γᵈ dA=

⟦⟧TmEq+ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {X' : Ob n} {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A))
          {uᵈ : isDefined (⟦ u ⟧Tm X)} {u'ᵈ : isDefined (⟦ u' ⟧Tm X')} → X ≡ X' → ⟦ u ⟧Tm X $ uᵈ ≡ ⟦ u' ⟧Tm X' $ u'ᵈ
⟦⟧TmEq+ Γᵈ du= refl = ⟦⟧TmEq Γᵈ du=


{-- We can now finally define our main properties --}

⟦⟧Tyᵈ Γᵈ UU = tt
⟦⟧Tyᵈ Γᵈ {A = el i v} (El dv) =
  (⟦⟧Tmᵈ Γᵈ dv ,
   ⟦⟧Tmₛ v ,
   ⟦⟧Tm₁ Γᵈ dv , tt)
⟦⟧Tyᵈ Γᵈ {A = pi A B} (Pi dA dB) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA in
  (Aᵈ ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB ,
   ⟦⟧Ty-ft B , tt)
⟦⟧Tyᵈ Γᵈ {A = sig A B} (Sig dA dB) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA in
  (Aᵈ ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB ,
   ⟦⟧Ty-ft B , tt)
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

⟦⟧Tmᵈ Γᵈ {u = pi i a b} (PiUU da db) =
  let aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da
      bᵈ = ⟦⟧Tmᵈ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
  in
  (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)
⟦⟧Tmᵈ Γᵈ {u = lam A B u} (Lam dA dB du) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
  in
  (Aᵈ ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt ) dB ,
   ⟦⟧Ty-ft B ,
   ⟦⟧Tmᵈ (Γᵈ , Aᵈ , tt) du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ (Γᵈ , Aᵈ , tt) du , tt)
⟦⟧Tmᵈ Γᵈ {u = app A B f a} (App dA dB df da) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B
  in
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

⟦⟧Tmᵈ Γᵈ {u = sig i a b} (SigUU da db) =
  let aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da
      bᵈ = ⟦⟧Tmᵈ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
  in (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)
⟦⟧Tmᵈ Γᵈ {u = pair A B a b} (Pair dA dB da db) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
  in
  (Aᵈ ,
   A= ,
   Bᵈ ,
   ⟦⟧Ty-ft B ,
   aᵈ ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da ,
   ⟦⟧Tmᵈ Γᵈ db ,
   ⟦⟧Tmₛ b ,
   (⟦⟧Tm₁ Γᵈ db ∙ ⟦subst⟧Ty= (⟦⟧Ty-ft A) B Bᵈ a aᵈ (⟦⟧Tm₁ Γᵈ da)) , tt)
⟦⟧Tmᵈ Γᵈ {u = pr1 A B u} (Pr1 dA dB du) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B
  in
  (Aᵈ ,
   A= ,
   Bᵈ ,
   B= ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ {A = sig A B} {Aᵈ = (Aᵈ , A= , Bᵈ , B= , tt)} du , tt)
⟦⟧Tmᵈ Γᵈ {u = pr2 A B u} (Pr2 dA dB du) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B
  in
  (Aᵈ ,
   A= ,
   Bᵈ ,
   B= ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ {A = sig A B} {Aᵈ = (Aᵈ , A= , Bᵈ , B= , tt)} du , tt)

⟦⟧Tmᵈ Γᵈ {u = nat i} NatUU = tt
⟦⟧Tmᵈ Γᵈ {u = zero} Zero = tt
⟦⟧Tmᵈ Γᵈ {u = suc u} (Suc du) =
  (⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ du , tt)
⟦⟧Tmᵈ Γᵈ {u = natelim P dO dS u} (Natelim dP ddO ddS du) =
  let Pᵈ  = ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP
      P=  = ⟦⟧Ty-ft P
      dOᵈ = ⟦⟧Tmᵈ Γᵈ ddO
      dOₛ = ⟦⟧Tmₛ dO
      dO₁ = ⟦⟧Tm₁ Γᵈ ddO
            ∙ ⟦subst⟧Ty= NatStr= P Pᵈ zero tt zeroStr₁
      dSᵈ = ⟦⟧Tmᵈ ((Γᵈ , (tt , tt)) , Pᵈ , tt) ddS
      dSₛ = ⟦⟧Tmₛ dS
      natthing = NatStrNat pp₀
      auxauxᵈ = ⟦weakenTy+⟧ᵈ P Pᵈ NatStr= NatStr= natthing
      auxᵈ = ⟦subst⟧Tyᵈ NatStr= (weakenTy' (prev last) P) auxauxᵈ (suc (var last)) (tt , (ssₛ , (varCL₁ ∙ natthing) , tt)) sucStr₁
      dS₁ = ⟦⟧Tm₁ ((Γᵈ , (tt , tt)) , Pᵈ , tt) ddS
            ∙ ! (⟦weakenTy⟧= (substTy (weakenTy' (prev last) P) (suc (var last))) auxᵈ (⟦⟧Ty-ft P))
            ∙ ap-irr-star refl (⟦subst⟧Ty= NatStr= (weakenTy' (prev last) P) auxauxᵈ (suc (var last)) (tt , (ssₛ , (varCL₁ ∙ natthing) , tt)) sucStr₁
              ∙ ap-irr-star refl (! (⟦weakenTy+⟧= P Pᵈ NatStr= NatStr= natthing)))
      uᵈ  = ⟦⟧Tmᵈ Γᵈ du
      uₛ  = ⟦⟧Tmₛ u
      u₁  = ⟦⟧Tm₁ Γᵈ du
  in (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt)

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
⟦⟧Tmᵈ {Γ = Γ} Γᵈ {u = jj A P d a b p} (JJ dA dP dd da db dp) = {!#J#!} {-
  let X = ⟦ Γ ⟧Ctx $ Γᵈ
      Aᵈ : isDefined (⟦ A ⟧Ty X)
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      [A] = ⟦ A ⟧Ty X $ Aᵈ
      [A]-ft : ft [A] ≡ X
      [A]-ft = ⟦⟧Ty-ft A
      wAᵈ : isDefined (⟦ weakenTy A ⟧Ty [A])
      wAᵈ = ⟦weakenTy⟧ᵈ A Aᵈ [A]-ft
      wA= = ⟦weakenTy⟧= A Aᵈ [A]-ft
      [wA] = ⟦ weakenTy A ⟧Ty [A] $ wAᵈ
      [wA]-ft : ft [wA] ≡ [A]
      [wA]-ft = ⟦⟧Ty-ft (weakenTy A)
      wwAᵈ : isDefined (⟦ weakenTy (weakenTy A) ⟧Ty [wA])
      wwAᵈ = ⟦weakenTy⟧ᵈ (weakenTy A) wAᵈ [wA]-ft
      wwA= = ⟦weakenTy⟧= (weakenTy A) wAᵈ [wA]-ft
      [wwA] = ⟦ weakenTy (weakenTy A) ⟧Ty [wA] $ wwAᵈ
      [wwA]-ft : ft [wwA] ≡ [wA]
      [wwA]-ft = ⟦⟧Ty-ft (weakenTy (weakenTy A))
      idᵈ : isDefined (⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [wA])
      idᵈ = (wwAᵈ , [wwA]-ft , tt , varCₛ (prev last) [wA] , (varC+₁ last [wA]-ft (varCL₁ ∙ wA=) ∙ wwA=) , tt , varCₛ last [wA] , (varCL₁ ∙ wwA=) , tt) 
      [id] = ⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [wA] $ idᵈ
      [id]-ft : ft [id] ≡ [wA]
      [id]-ft = ⟦⟧Ty-ft (id (weakenTy (weakenTy A)) (var (prev last)) (var last)) {Aᵈ = idᵈ}
      Pᵈ' : isDefined (⟦ P ⟧Ty [id])
      Pᵈ' = ⟦⟧Tyᵈ (((Γᵈ , (Aᵈ , tt)) , wAᵈ , tt) , (idᵈ , tt)) dP
      Pᵈ : isDefined (⟦ P ⟧Ty (T-ftP X (⟦ A ⟧Ty X $ Aᵈ) [A]-ft))
      Pᵈ = cong⟦⟧Ty {A = P} (ap-irr-IdStr (! wA=) (! wwA= ∙ ap-irr-star (ap pp (! wA=)) (! wA=)) (ap (varC (prev last)) (! wA=)) (ap (varC last) (! wA=))) Pᵈ' 
      P= = ⟦⟧Ty-ft P
      [varL] = ⟦ var last ⟧Tm [A] $ tt
      varL₁ : ∂₁ [varL] ≡ [wA]
      varL₁ = varCL₁ ∙ wA=
      wwA'ᵈ : isDefined (⟦ weakenTy' (prev last) (weakenTy A) ⟧Ty [wA])
      wwA'ᵈ = ⟦weakenTy⟧ᵈ' (prev last) (weakenTy A) wAᵈ [A]-ft [A]-ft (ap-irr-star {!!} refl ∙ wA=)
      [wwA'] = ⟦ weakenTy' (prev last) (weakenTy A) ⟧Ty [wA] $ wwA'ᵈ
      wwA= = ⟦weakenTy⟧=' (prev last) (weakenTy A) wAᵈ [A]-ft {!!} {!!}
      wwA'=' : star (qq (pp [A]) [A] [A]-ft (pp₁ ∙ [A]-ft)) [wA] (⟦⟧Ty-ft (weakenTy A)) qq₁ ≡ [wwA']
      wwA'=' = ap-irr-star (ap-irr-qq (! qq^last) refl ∙ ! qq^prev) refl ∙ ⟦weakenTy⟧=' (prev last) (weakenTy A) wAᵈ refl refl (ap-irr-star qq^last refl ∙ wA=)
      [wwA']-ft : ft [wwA'] ≡ [wA]
      [wwA']-ft = ⟦⟧Ty-ft (weakenTy' (prev last) (weakenTy A))
      -- varL₁' : ∂₁ [varL] ≡ star [varL] [wwA'] [wwA']-ft varL₁
      -- varL₁' = varL₁ ∙ ! (ap-irr-star (varCL-qq [A]-ft) refl ∙ star-id) ∙ star-comp  ∙ ap-irr-star refl wwA'= -- ! (star-id {p = ⟦⟧Ty-ft (weakenTy A)}) ∙ ap-irr-star (ss-qq ∙ ap-irr-comp (ap-irr-qq (id-left pp₀) refl) refl {g₀' = qq₀} {f₁' = ss₁ id₁ ∙ ap-irr-star (id-left pp₀) refl}) refl ∙ star-comp ∙ ap-irr-star refl wwA'= 
      wwwAᵈ : isDefined (⟦ weakenTy (weakenTy' (prev last) (weakenTy A)) ⟧Ty [wwA'])
      wwwAᵈ = ⟦weakenTy⟧ᵈ (weakenTy' (prev last) (weakenTy A)) wwA'ᵈ [wwA']-ft
      wwwA= = ⟦weakenTy⟧= (weakenTy' (prev last) (weakenTy A)) wwA'ᵈ [wwA']-ft
      [wwwA] = ⟦ weakenTy (weakenTy' (prev last) (weakenTy A)) ⟧Ty [wwA'] $ wwwAᵈ
      widᵈ : isDefined (⟦ weakenTy' (prev (prev last)) (id (weakenTy (weakenTy A)) (var (prev last)) (var last)) ⟧Ty [wwA'])
      widᵈ = ⟦weakenTy⟧ᵈ' (prev (prev last))
               (id (weakenTy (weakenTy A)) (var (prev last)) (var last)) idᵈ [A]-ft {!!} {!!} --(wwwAᵈ , ⟦⟧Ty-ft (weakenTy (weakenTy' (prev last) (weakenTy A))) , tt , varCₛ (prev last) [wwA'] , (varC+₁ last (⟦⟧Ty-ft (weakenTy' (prev last) (weakenTy A))) (varCL₁ {Y = [A]} {X= = ⟦⟧Ty-ft (weakenTy A)} ∙  ap-irr-star (ap pp (! wA=)) (! wA=) ∙ ! star-comp ∙ ap-irr-star (! pp-qq) refl ∙ star-comp ∙ ap-irr-star refl wA= ∙ wwA'=) ∙ wwwA=) , tt , varCₛ last [wwA'] , (varCL₁ ∙ wwwA=) , tt)
      [wid] = ⟦ weakenTy' (prev (prev last)) (id (weakenTy (weakenTy A)) (var (prev last)) (var last)) ⟧Ty [wwA'] $ widᵈ
      wid= = ⟦weakenTy⟧=' (prev (prev last))
               (id (weakenTy (weakenTy A)) (var (prev last)) (var last)) idᵈ [A]-ft {!!} {!!}
      wid=' : star (qq (qq (pp [A]) [A] [A]-ft (pp₁ ∙ [A]-ft)) [wA] [wA]-ft qq₁) [id] IdStr= qq₁ ≡ [wid]
      wid=' = {!!} --ap-irr-star (ap-irr-qq (ap-irr-qq (ap pp (! [wA]-ft) ∙ ! qq^last) (! [wA]-ft) ∙ ! qq^prev) refl ∙ ! qq^prev) refl ∙ wid=
      [wid]-ft : ft [wid] ≡ [wwA']
      [wid]-ft = ⟦⟧Ty-ft (weakenTy' (prev (prev last)) (id (weakenTy (weakenTy A)) (var (prev last)) (var last)))
      -- reflᵈ : isDefined (⟦ refl (weakenTy A) (var last) ⟧Tm [A])
      -- reflᵈ = (wAᵈ , ⟦⟧Ty-ft (weakenTy A) , tt , varCₛ last [A] , (varCL₁ ∙ wA=) , tt)
      -- refl₁ : ∂₁ (⟦ refl (weakenTy A) (var last) ⟧Tm [A] $ reflᵈ) ≡ star [varL] (star (qq [varL] [wwA'] [wwA']-ft varL₁) [wid] [wid]-ft qq₁) (ft-star ∙ qq₀) varL₁'
      -- refl₁ = reflStr₁ ∙ {!!} --reflStr₁ ∙ ! (! (star-comp {g₀ = qq₀}) ∙ IdStrNat (comp₀ ∙ ss₀ ∙ id₀) ∙ ap-irr-IdStr refl (ap-irr-star refl (! wwwA=) ∙ ! star-comp ∙ ap-irr-star refl (! wwA'=) {f₁' = comp₁ ∙ pp₁ ∙ (⟦⟧Ty-ft (weakenTy' (prev last) (weakenTy A))) ∙ ! wA=} ∙ ! (star-comp {g₀ = qq₀}) ∙ ap-irr-star refl (! wA=) ∙ ! star-comp ∙ ap-irr-star (! assoc ∙ ap-irr-comp pp-qq refl {f₁' = comp₁ ∙ pp₁} ∙ (assoc {g₀ = pp₀ ∙ wA= ∙ (! (⟦⟧Ty-ft (weakenTy' (prev last) (weakenTy A))))} ∙ ap-irr-comp refl (ap-irr-comp refl (! assoc ∙ ap-irr-comp pp-qq refl ∙  assoc ∙ ap-irr-comp refl (is-section= (ft-star ∙ ss₀ ∙ id₀) ssₛ varL₁') ∙ id-left (ss₀ ∙ id₀)) ∙ is-section= (ft-star ∙ pp₀) ssₛ varCL₁) ∙ id-left pp₀)) refl ∙ wA=) (ss-comp ∙ ap ss (! assoc ∙ ap-irr-comp (! (ss-qq {f₁ = pp₁ ∙ (⟦⟧Ty-ft (weakenTy' (prev last) (weakenTy A)))})) refl ∙ ! assoc ∙ ap-irr-comp pp-qq refl ∙ assoc ∙ ap-irr-comp refl (is-section= (ft-star ∙ ss₀ ∙ id₀) ssₛ (varCL₁ {X= = [A]-ft} ∙ ! (ap-irr-star refl (! wwA'=) {f₁' = varCL₁}∙ ! (star-comp {g₀ = qq₀}) ∙ ap-irr-star refl (! wA=) ∙ ! star-comp ∙ ap-irr-star (! assoc ∙ ap-irr-comp pp-qq refl ∙ assoc ∙ ap-irr-comp refl (is-section= (ft-star ∙ pp₀) ssₛ (ss₁ id₁ ∙ ap-irr-star (id-left pp₀) refl)) ∙ id-left pp₀) refl))) ∙ id-left (ss₀ ∙ id₀)) ∙ ss-of-section (ss (idC (⟦ A ⟧Ty (⟦ Γ ⟧Ctx $ Γᵈ) $ ⟦⟧Tyᵈ Γᵈ dA))) ssₛ) (ss-comp ∙ ap ss (! assoc ∙ ap-irr-comp (! (ss-qq  {f₁ = id₁})) refl ∙ id-right (comp₁ ∙ qq₁)) ∙ ss-comp ∙ ap ss (! (assoc {g₁ = qq₁ ∙ ! wwA'= ∙ ap-irr-star refl (! wA=) ∙ ! star-comp ∙ ap-irr-star pp-qq refl ∙ star-comp {g₁ = pp₁ ∙ [A]-ft}}) ∙ ap-irr-comp (ap-irr-comp refl (ap-irr-qq refl (! (star-comp ∙ ap-irr-star refl wA= ∙ wwA'=) ∙ ap-irr-star pp-qq refl {q' = [A]-ft} ∙ star-comp)) ∙ ! qq-comp ∙  ap-irr-qq (is-section= (ft-star ∙ pp₀) ssₛ (ss₁ id₁ ∙ ap-irr-star (id-left pp₀) refl)) refl {q' = ft-star ∙ pp₀} ∙ qq-id) refl ∙ id-right (ss₁ id₁ ∙ ap-irr-star (id-left pp₀) refl)) ∙ ss-of-section _ ssₛ))
      wPᵈ : isDefined (⟦ weakenTy' (prev (prev (prev last))) P ⟧Ty [wid])
      wPᵈ = ⟦weakenTy⟧ᵈ' (prev (prev (prev last))) P Pᵈ' [A]-ft {!!} ({!? !} ∙ wid=)
      -- wPsubst3ᵈ : isDefined (⟦ subst3Ty (weakenTy' (prev (prev (prev last))) P) (var last) (var last) (refl (weakenTy A) (var last)) ⟧Ty [A])
      -- wPsubst3ᵈ = ⟦subst3⟧Tyᵈ [wid]-ft [wwA']-ft [wA]-ft (weakenTy' (prev (prev (prev last))) P) {!!} (var last) tt varL₁ (var last) tt varL₁' (refl (weakenTy A) (var last)) reflᵈ refl₁
      -- wPsubst3= = ⟦subst3⟧Ty= IdStr= (⟦⟧Ty-ft (weakenTy' (prev last) (weakenTy A))) (⟦⟧Ty-ft (weakenTy A)) (weakenTy' (prev (prev (prev last))) P) {!!} (var last) tt varL₁ (var last) tt varL₁' (refl (weakenTy A) (var last)) reflᵈ refl₁
      dᵈ : isDefined (⟦ d ⟧Tm (⟦ A ⟧Ty X $ Aᵈ))
      dᵈ = ⟦⟧Tmᵈ (Γᵈ , Aᵈ , tt) dd
      dₛ = ⟦⟧Tmₛ d
      --  δ = ((idMor _ , var last) , refl (weakenTy A) (var last))
      -- tᵈ : isDefined (⟦ P [ δ ]Ty ⟧Ty (⟦ A ⟧Ty (⟦ Γ ⟧Ctx $ Γᵈ) $ ⟦⟧Tyᵈ Γᵈ dA))
      -- tᵈ = ⟦subst2⟧Tyᵈ (IdStr= ∙ ft-star ∙ pp₀) (ft-star ∙ pp₀) P Pᵈ (var last) tt varCL₁ (refl (weakenTy A) (var last)) reflᵈ refl₁
      -- d₁ = ⟦⟧Tm₁ {Γ = Γ , A} (Γᵈ , Aᵈ , tt) {u = d} {uᵈ = dᵈ} {A = P [ δ ]Ty} {Aᵈ = tᵈ} dd
      --      ∙ ⟦subst2⟧Ty= (IdStr= ∙ ft-star ∙ pp₀) (ft-star ∙ pp₀) P Pᵈ (var last) tt varCL₁ (refl (weakenTy A) (var last)) reflᵈ refl₁ ∙ ap2-irr star (ap-irr-reflStr (! wA=) refl) refl
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
      pₛ = ⟦⟧Tmₛ p
      p₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = (Aᵈ , [A]-ft , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)} dp
      in (Aᵈ , [A]-ft , Pᵈ , P= , dᵈ , dₛ , {!!} {-! dd ∙ ⟦subst3⟧Ty= {!!} {!!} (ft-star ∙ pp₀) (weakenTy' (prev (prev (prev last))) P) (⟦weakenTy⟧ᵈ' (prev (prev (prev last))) P Pᵈ' A= {!!} {!IdStrNat ? ∙ ?!}) (var last) tt (varCL₁ ∙ {!!}) (var last) tt (varCL₁ ∙ {!wA=!}) (refl (weakenTy A) (var last)) reflᵈ {!refl₁!} ∙ {!!}!})-} , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt)-}


⟦⟧Morᵈ {Δ = ◇} _ _ {◇} tt = tt
⟦⟧Morᵈ {Δ = Δ , B} Γᵈ (Δᵈ , Bᵈ , tt) {δ , u} (dδ , du) =
  let δᵈ' = ⟦⟧Morᵈ Γᵈ Δᵈ dδ
      δᵈ = cong⟦⟧Mor {δ = δ} (! (⟦⟧Ty-ft B)) δᵈ'
      uᵈ = ⟦⟧Tmᵈ Γᵈ du
      δ₁ = ⟦⟧Mor₁ δ
      u₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = ⟦tsubst⟧Tyᵈ B Bᵈ δ δᵈ'} du ∙ ! (⟦tsubst⟧Ty= B Bᵈ δ δᵈ') ∙ ap-irr-star (ap-irr (λ x z → ⟦ δ ⟧Mor _ x $ z) (! (⟦⟧Ty-ft B))) refl
  in (δᵈ , uᵈ , δ₁ , u₁ , tt)

⟦⟧Tm₁ {Γ = Γ , _} (Γᵈ , Aᵈ , tt) (VarLast {A = A} dA) = varCL₁ ∙ ⟦weakenTy⟧= A Aᵈ (⟦⟧Ty-ft A)
⟦⟧Tm₁ {Γ = Γ , _} (Γᵈ , Bᵈ , tt) {u = var (prev k)} (VarPrev {B = B} {A = A} dA dk) = varC+₁ k (⟦⟧Ty-ft B) (⟦⟧Tm₁ Γᵈ dk) ∙ ⟦weakenTy⟧= A (⟦⟧Tyᵈ Γᵈ dA) (⟦⟧Ty-ft B)
⟦⟧Tm₁ Γᵈ (Conv dA du dA=) = ⟦⟧Tm₁ Γᵈ du ∙ ⟦⟧TyEq Γᵈ dA= {Aᵈ = ⟦⟧Tyᵈ Γᵈ dA}

⟦⟧Tm₁ Γᵈ {u = uu i} UUUU = uuStr₁

⟦⟧Tm₁ Γᵈ {u = pi i a b} (PiUU da db) = piStr₁
⟦⟧Tm₁ Γᵈ {u = lam A B u} (Lam dA dB du) = lamStr₁
⟦⟧Tm₁ Γᵈ {u = app A B f a} (App dA dB df da) = appStr₁ ∙ ! (⟦subst⟧Ty= (⟦⟧Ty-ft A) B (⟦⟧Tyᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))

⟦⟧Tm₁ Γᵈ {u = sig i a b} (SigUU da db) = sigStr₁
⟦⟧Tm₁ Γᵈ {u = pair A B a b} (Pair dA dB da db) = pairStr₁
⟦⟧Tm₁ Γᵈ {u = pr1 A B u} (Pr1 dA dB du) = pr1Str₁
⟦⟧Tm₁ Γᵈ {u = pr2 A B u} (Pr2 dA dB du) =
  let Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B
  in
  pr2Str₁ ∙ ! (⟦subst⟧Ty= A= B Bᵈ (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , ⟦⟧Tmᵈ Γᵈ du , ⟦⟧Tmₛ u , ⟦⟧Tm₁ Γᵈ {A = sig A B} {Aᵈ = Aᵈ , A= , Bᵈ , B= , tt} du , tt) pr1Str₁)

⟦⟧Tm₁ Γᵈ {u = nat i} NatUU = natStr₁
⟦⟧Tm₁ Γᵈ {u = zero} Zero = zeroStr₁
⟦⟧Tm₁ Γᵈ {u = suc u} (Suc du) = sucStr₁
⟦⟧Tm₁ Γᵈ {u = natelim P dO dS u} (Natelim dP ddO ddS du) = natelimStr₁ ∙ ! (⟦subst⟧Ty= NatStr= P (⟦⟧Tyᵈ (Γᵈ , tt , tt) dP) u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ du))

⟦⟧Tm₁ Γᵈ {u = id i a u v} (IdUU da du dv) = idStr₁
⟦⟧Tm₁ Γᵈ {u = refl A a} (Refl dA da) = reflStr₁
⟦⟧Tm₁ Γᵈ {u = jj A P d a b p} (JJ dA dP dd da db dp) = {!#J# -- jjStr₁ ∙ {!! (⟦subst3⟧Ty= (IdStr= ∙ ⟦⟧Ty-ft (weakenTy (weakenTy A))) (⟦⟧Ty-ft (weakenTy A)) (⟦⟧Ty-ft A) P (⟦⟧Tyᵈ {!Γᵈ !} dP) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da) b (⟦⟧Tmᵈ Γᵈ db) (⟦⟧Tm₁ Γᵈ db ∙ {!!}) p (⟦⟧Tmᵈ Γᵈ dp) (⟦⟧Tm₁ Γᵈ dp ∙ {!!}))!}!}


⟦weakenTy⟧ᵈ' k (uu i) Aᵈ _ _ _ = tt
⟦weakenTy⟧ᵈ' k (el i v) (vᵈ , vₛ , v₁ , tt) X+= X= Y= =
  (⟦weakenTm⟧ᵈ' k v vᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weakenTm⟧₁' k v vᵈ X+= X= Y= v₁ ∙ UUStrNat (qq^₀ ∙ Y=)) , tt)
⟦weakenTy⟧ᵈ' k (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Y= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) , tt)
⟦weakenTy⟧ᵈ' k (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Y= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) , tt)
⟦weakenTy⟧ᵈ' k nat Aᵈ _ _ _ = tt
⟦weakenTy⟧ᵈ' k (id A u v) (Aᵈ , A= , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Y= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X+= X= Y= u₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) ,
   ⟦weakenTm⟧ᵈ' k v vᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weakenTm⟧₁' k v vᵈ X+= X= Y= v₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) , tt)

⟦weakenTm⟧ᵈ' k (var x) tt X+= X= Y= = tt

⟦weakenTm⟧ᵈ' k (uu i) tt X+= X= Y= = tt

⟦weakenTm⟧ᵈ' k (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Y= =
  (⟦weakenTm⟧ᵈ' k a aᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X+= X= Y= a₁ ∙ UUStrNat (qq^₀ ∙ Y=)) ,
   ⟦weakenTm+⟧ᵈ' k b bᵈ X+= X= ElStr= (ElStrNat (qq^₀ ∙ Y=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Y=)) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) b) ,
   (⟦weakenTm+⟧₁' k b bᵈ X+= X= UUStr= ElStr= (ElStrNat (qq^₀ ∙ Y=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Y=)) b₁ ∙ UUStrNat (qq₀ ∙ ElStrNat (qq^₀ ∙ Y=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Y=))) , tt)
⟦weakenTm⟧ᵈ' k (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Y= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weakenTm+⟧ᵈ' k u uᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) u) ,
   (⟦weakenTm+⟧₁' k u uᵈ X+= X= (⟦⟧Ty-ft B) (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) u₁ ∙ ⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=)) , tt)
⟦weakenTm⟧ᵈ' k (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) X+= X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Y= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weakenTm⟧ᵈ' k f fᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k f) ,
   (⟦weakenTm⟧₁' k f fᵈ X+= X= Y= f₁ ∙ PiStrNat qq^₀ ∙ ap-irr-PiStr Y= (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=))) ,
   ⟦weakenTm⟧ᵈ' k a aᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X+= X= Y= a₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) , tt)

⟦weakenTm⟧ᵈ' k (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Y= =
  (⟦weakenTm⟧ᵈ' k a aᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X+= X= Y= a₁ ∙ UUStrNat (qq^₀ ∙ Y=) ) ,
   (⟦weakenTm+⟧ᵈ' k b bᵈ X+= X= ElStr= (ElStrNat (qq^₀ ∙ Y=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Y=))) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) b) ,
   (⟦weakenTm+⟧₁' k b bᵈ X+= X= UUStr= ElStr= (ElStrNat (qq^₀ ∙ Y=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Y=)) b₁ ∙ UUStrNat (qq₀ ∙ ElStrNat qq^₀ ∙ ap-irr-ElStr Y= (⟦weakenTm⟧=' k a aᵈ X+= X= Y=))) , tt)
⟦weakenTm⟧ᵈ' k (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Y= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weakenTm⟧ᵈ' k a aᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X+= X= Y= a₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) ,
   ⟦weakenTm⟧ᵈ' k b bᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k b) ,
   (⟦weakenTm⟧₁' k b bᵈ X+= X= Y= b₁ ∙ starstar (⟦⟧Ty-ft A) aₛ ∙ ap-irr-star (⟦weakenTm⟧=' k a aᵈ X+= X= Y=) (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=))) , tt)
⟦weakenTm⟧ᵈ' k (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Y= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X+= X= Y= u₁ ∙ SigStrNat qq^₀ ∙ ap-irr-SigStr Y= (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=))) , tt)
⟦weakenTm⟧ᵈ' k (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Y= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTy+⟧ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X+= X= Y= u₁ ∙ SigStrNat qq^₀ ∙ ap-irr-SigStr Y= (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=))) , tt)

⟦weakenTm⟧ᵈ' k (nat i) tt X+= X= Y= = tt
⟦weakenTm⟧ᵈ' k zero tt X+= X= Y= = tt
⟦weakenTm⟧ᵈ' k (suc u) (uᵈ , uₛ , u₁ , tt) X+= X= Y= =
  (⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X+= X= Y= u₁ ∙ NatStrNat qq^₀ ∙ ap NatStr Y=) , tt)

⟦weakenTm⟧ᵈ' k (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) X+= X= {Z = Y} Y= =
  (Pᵈw ,
   P=w ,
   dOᵈw ,
   dOₛw ,
   dO₁w ,
   dSᵈw ,
   dSₛw ,
   dS₁w ,
   uᵈw ,
   uₛw ,
   u₁w , tt)  where
  
      naturalityNat : star (qq^ k X+= X=) (NatStr _) _ _ ≡ NatStr Y
      naturalityNat = NatStrNat (qq^₀ ∙ Y=)

      wP= : _
      wP= = ! (⟦weakenTy+⟧=' k P Pᵈ X+= X= NatStr= naturalityNat)

      Pᵈw : isDefined (⟦ weakenTy' (prev k) P ⟧Ty (NatStr Y))
      Pᵈw = ⟦weakenTy+⟧ᵈ' k P Pᵈ X+= X= NatStr= naturalityNat

      P=w : ft (⟦ weakenTy' (prev k) P ⟧Ty (NatStr Y) $ Pᵈw) ≡ NatStr Y
      P=w = # (⟦⟧Ty-ft (weakenTy' (prev k) P))

      dOᵈw : isDefined (⟦ weakenTm' k dO ⟧Tm Y)
      dOᵈw = # (⟦weakenTm⟧ᵈ' k dO dOᵈ X+= X= Y=)

      dOₛw : is-section (⟦ weakenTm' k dO ⟧Tm Y $ dOᵈw)
      dOₛw = # (⟦⟧Tmₛ (weakenTm' k dO))

      dO₁w : ∂₁ (⟦ weakenTm' k dO ⟧Tm Y $ dOᵈw) ≡ _
      dO₁w = ⟦weakenTm⟧₁' k dO dOᵈ X+= X= Y= dO₁ ∙ starstar NatStr= zeroStrₛ ∙ ap-irr-star (zeroStrNat (qq^₀ ∙ Y=)) (! wP=)

      dSᵈw : isDefined
             (⟦ weakenTm' (prev (prev k)) dS ⟧Tm
              (⟦ weakenTy' (prev k) P ⟧Ty (NatStr Y) $ Pᵈw))
      dSᵈw = ⟦weakenTm++⟧ᵈ' k dS dSᵈ X+= X= (⟦⟧Ty-ft P) NatStr= (⟦weakenTy+⟧=' k P Pᵈ X+= X= NatStr= naturalityNat)

      dSₛw : is-section (⟦ weakenTm' (prev (prev k)) dS ⟧Tm
              (⟦ weakenTy' (prev k) P ⟧Ty (NatStr Y) $ Pᵈw) $ dSᵈw)
      dSₛw = ⟦⟧Tmₛ (weakenTm' (prev (prev k)) dS)

      dS₁w : ∂₁ (⟦ weakenTm' (prev (prev k)) dS ⟧Tm (⟦ weakenTy' (prev k) P ⟧Ty (NatStr Y) $ Pᵈw) $ dSᵈw)
           ≡ star (pp (⟦ weakenTy' (prev k) P ⟧Ty (NatStr Y) $ Pᵈw)) (star (sucStr (NatStr Y) (varC last (NatStr Y)) _ _) (star (qq (pp (NatStr Y)) (NatStr Y) NatStr= (pp₁ ∙ NatStr=)) (⟦ weakenTy' (prev k) P ⟧Ty (NatStr Y) $ Pᵈw) _ _) _ _) _ _
      dS₁w = ⟦weakenTm++⟧₁' k dS dSᵈ X+= X= (ft-star ∙ pp₀) (⟦⟧Ty-ft P) NatStr= (⟦weakenTy+⟧=' k P Pᵈ X+= X= NatStr= naturalityNat) dS₁
             ∙ star-pp
             ∙ ap-irr-star
               (ap pp (⟦weakenTy+⟧=' k P Pᵈ X+= X= NatStr= naturalityNat))
               (starstar NatStr= sucStrₛ
                ∙ ap-irr-star (sucStrNat (qq₀ ∙ naturalityNat) ∙ ap-irr-sucStr refl (star-varCL ∙ ap ss (ap idC naturalityNat)))
                              (star-qqpp' (NatStrNat pp₀) ∙ ap-irr-star (ap-irr-qq (ap pp naturalityNat) naturalityNat) (⟦weakenTy+⟧=' k P Pᵈ X+= X= NatStr= naturalityNat)))

      uᵈw : isDefined (⟦ weakenTm' k u ⟧Tm Y)
      uᵈw = ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Y=

      uₛw : is-section (⟦ weakenTm' k u ⟧Tm Y $ uᵈw)
      uₛw = ⟦⟧Tmₛ (weakenTm' k u)

      u₁w : ∂₁ (⟦ weakenTm' k u ⟧Tm Y $ uᵈw) ≡ _
      u₁w = ⟦weakenTm⟧₁' k u uᵈ X+= X= Y= u₁ ∙ naturalityNat

⟦weakenTm⟧ᵈ' k (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Y= =
  (⟦weakenTm⟧ᵈ' k a aᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X+= X= Y= a₁ ∙ UUStrNat (qq^₀ ∙ Y=)) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X+= X= Y= u₁ ∙ ElStrNat (qq^₀ ∙ Y=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Y=)) ,
   ⟦weakenTm⟧ᵈ' k v vᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weakenTm⟧₁' k v vᵈ X+= X= Y= v₁ ∙ ElStrNat (qq^₀ ∙ Y=) ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k a aᵈ X+= X= Y=)) , tt)
⟦weakenTm⟧ᵈ' k (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X+= X= Y= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X+= X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X+= X= Y= u₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) , tt)
⟦weakenTm⟧ᵈ' k (jj A P d a b p) uᵈ X+= X= Y= =
  {!#J#!}

⟦weakenTy⟧=' k (uu i) _ X+= X= Y= =
  UUStrNat (qq^₀ ∙ Y=)
⟦weakenTy⟧=' k (el i v) (vᵈ , vₛ , v₁ , tt) X+= X= Y= =
  ElStrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-ElStr refl (⟦weakenTm⟧=' k v vᵈ X+= X= Y=)
⟦weakenTy⟧=' k (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Y= =
  PiStrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-PiStr refl
                 (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=)
                 (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=))
⟦weakenTy⟧=' k (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Y= =
  SigStrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-SigStr refl
                  (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=)
                  (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=))
⟦weakenTy⟧=' k nat _ X+= X= Y= =
  NatStrNat (qq^₀ ∙ Y=)
⟦weakenTy⟧=' k (id A u v) (Aᵈ , A= , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Y= =
  IdStrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-IdStr refl (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=) (⟦weakenTm⟧=' k u uᵈ X+= X= Y=) (⟦weakenTm⟧=' k v vᵈ X+= X= Y=)


⟦weakenTm⟧=' {n = 0} k (var ())
⟦weakenTm⟧=' {n = suc n} last (var x) tt X+= refl refl = star-varCL'' {g₀ = pp^₀ x _} ∙ ap ss (ap-irr-comp refl qq^last ∙ ! ((pp^prev {k = x} X+=)))
⟦weakenTm⟧=' {n = suc n} (prev k) (var last) tt X+= refl Z= = star-varCL' ∙ ap ss qq^prev ∙ ap ss (! (id-left qq₀) ∙ ap-irr-comp refl (ap idC Z=) {f₁' = id₁ ∙ ! Z=}) ∙ ! ss-comp
⟦weakenTm⟧=' {n = suc n} (prev k) (var (prev x)) tt X+= refl Z= = star-varCL'' {g₀ = pp^₀ (prev x) _} ∙ ap ss (ap-irr-comp (pp^prev refl) qq^prev ∙ assoc ∙ ap-irr-comp refl (pp-qq ∙ ap-irr-comp refl (ap pp Z=)) ∙ ! (assoc {f₁ = pp₁ ∙ ap ft (! Z=) ∙ ft-star ∙ qq^₀} {g₀ = qq^₀} {h₀ = pp^₀ x _})) ∙ ! (star-varCL'' {g₀ = comp₀ ∙ qq^₀}) ∙ ap ss (ap-irr-comp (! star-varCL'' ∙ ⟦weakenTm⟧=' k (var x) tt X+= refl refl) refl) ∙ star-varCL'' ∙ ap ss (! (pp^prev {k = weakenVar' k x} (ap ft (! Z=) ∙ ft-star ∙ qq^₀)))

⟦weakenTm⟧=' k (uu i) tt X+= X= Y= =
  uuStrNat (qq^₀ ∙ Y=)

⟦weakenTm⟧=' k (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Y= =
  piStrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-piStr refl
                 (⟦weakenTm⟧=' k a aᵈ X+= X= Y=)
                 (⟦weakenTm+⟧=' k b bᵈ X+= X= ElStr= (ElStrNat qq^₀ ∙ ap-irr-ElStr Y= (⟦weakenTm⟧=' k a aᵈ X+= X= Y=)))
⟦weakenTm⟧=' k (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Y= =
  lamStrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-lamStr refl
                  (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=)
                  (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=))
                  (⟦weakenTm+⟧=' k u uᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=))
⟦weakenTm⟧=' k (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) X+= X= Y= =
  appStrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-appStr refl
                  (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=)
                  (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=))
                  (⟦weakenTm⟧=' k f fᵈ X+= X= Y=)
                  (⟦weakenTm⟧=' k a aᵈ X+= X= Y=)

⟦weakenTm⟧=' k (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Y= =
  sigStrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-sigStr refl
                  (⟦weakenTm⟧=' k a aᵈ X+= X= Y=)
                  (⟦weakenTm+⟧=' k b bᵈ X+= X= ElStr= (ElStrNat qq^₀ ∙ ap-irr-ElStr Y= (⟦weakenTm⟧=' k a aᵈ X+= X= Y=)))
⟦weakenTm⟧=' k (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Y= =
  pairStrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-pairStr refl
                   (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=)
                   (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=))
                   (⟦weakenTm⟧=' k a aᵈ X+= X= Y=)
                   (⟦weakenTm⟧=' k b bᵈ X+= X= Y=)
⟦weakenTm⟧=' k (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Y= =
  pr1StrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-pr1Str refl
                  (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=)
                  (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=))
                  (⟦weakenTm⟧=' k u uᵈ X+= X= Y=)
⟦weakenTm⟧=' k (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Y= =
  pr2StrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-pr2Str refl
                  (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=)
                  (⟦weakenTy+⟧=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=))
                  (⟦weakenTm⟧=' k u uᵈ X+= X= Y=)

⟦weakenTm⟧=' k (nat i) tt X+= X= Y= =
  natStrNat (qq^₀ ∙ Y=)
⟦weakenTm⟧=' k zero tt X+= X= Y= =
  zeroStrNat (qq^₀ ∙ Y=)
⟦weakenTm⟧=' k (suc u) (uᵈ , uₛ , u₁ , tt) X+= X= Y= =
  sucStrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-sucStr refl (⟦weakenTm⟧=' k u uᵈ X+= X= Y=)
⟦weakenTm⟧=' k (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) X+= X= Y= =
  natelimStrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-natelimStr refl
                      (⟦weakenTy+⟧=' k P Pᵈ X+= X= NatStr= (NatStrNat (qq^₀ ∙ Y=)))
                      (⟦weakenTm⟧=' k dO dOᵈ X+= X= Y=)
                      (⟦weakenTm++⟧=' k dS dSᵈ X+= X= (⟦⟧Ty-ft P) NatStr= (⟦weakenTy+⟧=' k P Pᵈ X+= X= NatStr= (NatStrNat (qq^₀ ∙ Y=))))
                      (⟦weakenTm⟧=' k u uᵈ X+= X= Y=)

⟦weakenTm⟧=' k (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Y= =
  idStrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-idStr refl
                 (⟦weakenTm⟧=' k a aᵈ X+= X= Y=)
                 (⟦weakenTm⟧=' k u uᵈ X+= X= Y=)
                 (⟦weakenTm⟧=' k v vᵈ X+= X= Y=)
⟦weakenTm⟧=' k (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Y= =
  reflStrNat (qq^₀ ∙ Y=)
  ∙ ap-irr-reflStr refl
                   (⟦weakenTy⟧=' k A Aᵈ X+= X= Y=)
                   (⟦weakenTm⟧=' k u uᵈ X+= X= Y=)
⟦weakenTm⟧=' k (jj A P d a b p) uᵈ X+= X= Y= =
  {!#J#!}


⟦⟧TyEq Γᵈ (TySymm dA=) = ! (⟦⟧TyEq Γᵈ dA=)
⟦⟧TyEq Γᵈ (TyTran dB dA= dB=) = ⟦⟧TyEq Γᵈ dA= {A'ᵈ = ⟦⟧Tyᵈ Γᵈ dB} ∙ ⟦⟧TyEq Γᵈ dB=

⟦⟧TyEq Γᵈ UUCong = refl
⟦⟧TyEq Γᵈ (ElCong dv=) = ap-irr-ElStr refl (⟦⟧TmEq Γᵈ dv=)
⟦⟧TyEq Γᵈ {A = sig A B} (SigCong dA dA= dB=) = ap-irr-SigStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TyEq Γᵈ {A = pi A B} (PiCong dA dA= dB=) = ap-irr-PiStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TyEq Γᵈ NatCong = refl
⟦⟧TyEq Γᵈ (IdCong dA du dv) = ap-irr-IdStr refl (⟦⟧TyEq Γᵈ dA) (⟦⟧TmEq Γᵈ du) (⟦⟧TmEq Γᵈ dv)

⟦⟧TyEq Γᵈ ElUU= = eluuStr
⟦⟧TyEq Γᵈ (ElPi= da db) = elpiStr
⟦⟧TyEq Γᵈ (ElSig= da db) = elsigStr
⟦⟧TyEq Γᵈ ElNat= = elnatStr
⟦⟧TyEq Γᵈ (ElId= da du dv) = elidStr

⟦⟧TmEq Γᵈ (VarLastCong dA) = refl
⟦⟧TmEq (Γᵈ , Bᵈ , tt) (VarPrevCong {B = B} {k = k} {k' = k'} dA dx) = ap ss (pp^prev (⟦⟧Ty-ft B)) ∙ (! star-varCL'' ∙ ap-irr-starTm refl (⟦⟧TmEq Γᵈ dx) ∙ star-varCL'') ∙ ! (ap ss (pp^prev (⟦⟧Ty-ft B)))
⟦⟧TmEq Γᵈ (TmSymm du=) = ! (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq Γᵈ (TmTran dv du= du'=) = ⟦⟧TmEq Γᵈ du= {u'ᵈ = ⟦⟧Tmᵈ Γᵈ dv} ∙ ⟦⟧TmEq Γᵈ du'=
⟦⟧TmEq Γᵈ (ConvEq dA' du= dA=) = ⟦⟧TmEq Γᵈ du=

⟦⟧TmEq Γᵈ UUUUCong = refl

⟦⟧TmEq Γᵈ {u = pi i a b} (PiUUCong da da= db=) {uᵈ = (aᵈ , aₛ , a₁ , _)} = ap-irr-piStr refl (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq+ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db= (ap-irr-ElStr refl (⟦⟧TmEq Γᵈ da=)))
⟦⟧TmEq Γᵈ {u = lam A B u} (LamCong dA dA= dB= du=) = ap-irr-lamStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) du= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TmEq Γᵈ {u = app A B f a} (AppCong dA dA= dB= df= da=) = ap-irr-appStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ df=) (⟦⟧TmEq Γᵈ da=)

⟦⟧TmEq Γᵈ {u = sig i a b} (SigUUCong da da= db=) {uᵈ = (aᵈ , aₛ , a₁ , bᵈ , _)} {u'ᵈ = (a'ᵈ , _ , _ , b'ᵈ , _)} = ap-irr-sigStr refl (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq+ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db= (ap-irr-ElStr refl (⟦⟧TmEq Γᵈ da=)))
⟦⟧TmEq Γᵈ {u = pair A B a b} (PairCong dA dA= dB= da= db=) = ap-irr-pairStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq Γᵈ db=)
⟦⟧TmEq Γᵈ {u = pr1 A B u} (Pr1Cong dA dA= dB= du=) = ap-irr-pr1Str refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq Γᵈ {u = pr2 A B u} (Pr2Cong dA dA= dB= du=) = ap-irr-pr2Str refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=)) (⟦⟧TmEq Γᵈ du=)

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
⟦⟧TmEq Γᵈ {u = jj A P d a b p} (JJCong dA dA= dP= dd= da= db= dp=) = {!#J#!}

⟦⟧TmEq Γᵈ {u = app A B (lam A B u) a} (BetaPi dA dB du da) = betaPiStr ∙ ! (⟦subst⟧Tm= (⟦⟧Ty-ft A) u _ a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))
⟦⟧TmEq Γᵈ (BetaSig1 dA dB da db) = betaSig1Str
⟦⟧TmEq Γᵈ (BetaSig2 dA dB da db) = betaSig2Str
⟦⟧TmEq Γᵈ (BetaNatZero dP ddO ddS) = betaNatZero
⟦⟧TmEq {Γ = Γ} Γᵈ {u = natelim P dO dS (suc u)} (BetaNatSuc dP ddO ddS du) =
  let
    Pᵈ : isDefined (⟦ P ⟧Ty (NatStr (⟦ Γ ⟧Ctx $ Γᵈ)))
    Pᵈ = ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP

    dOᵈ : isDefined (⟦ dO ⟧Tm (⟦ Γ ⟧Ctx $ Γᵈ))
    dOᵈ = ⟦⟧Tmᵈ Γᵈ ddO

    dO₁ : ∂₁ (⟦ dO ⟧Tm (⟦ Γ ⟧Ctx $ Γᵈ) $ dOᵈ) ≡ star (zeroStr (⟦ Γ ⟧Ctx $ Γᵈ))
                                                     (⟦ P ⟧Ty (NatStr (⟦ Γ ⟧Ctx $ Γᵈ)) $ ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP)
                                                     (⟦⟧Ty-ft P)
                                                     zeroStr₁
    dO₁ = ⟦⟧Tm₁ Γᵈ ddO ∙ ⟦subst⟧Ty= NatStr= P Pᵈ zero tt zeroStr₁

    dSᵈ : isDefined (⟦ dS ⟧Tm (⟦ (Γ , nat) , P ⟧Ctx $ ((Γᵈ , tt , tt) , Pᵈ , tt)))
    dSᵈ = ⟦⟧Tmᵈ ((Γᵈ , tt , tt) , Pᵈ , tt) ddS

    dS₁ : ∂₁ (⟦ dS ⟧Tm (⟦ P ⟧Ty (NatStr (⟦ Γ ⟧Ctx $ Γᵈ)) $ Pᵈ) $ dSᵈ)
          ≡ T-dS₁ ccatsuc (⟦ Γ ⟧Ctx $ Γᵈ) (⟦ P ⟧Ty (NatStr (⟦ Γ ⟧Ctx $ Γᵈ)) $ ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP) (⟦⟧Ty-ft P)
    dS₁ = ⟦⟧Tm₁ ((Γᵈ , tt , tt) , Pᵈ , tt) ddS
          ∙ ! (⟦weakenTy⟧= (substTy (weakenTy' (prev last) P) (suc (var last))) (⟦subst⟧Tyᵈ NatStr= (weakenTy' (prev last) P) (⟦weakenTy+⟧ᵈ P Pᵈ NatStr= NatStr= (NatStrNat pp₀)) (suc (var last)) (tt , ssₛ , (varCL₁ ∙ NatStrNat pp₀) , tt) sucStr₁) (⟦⟧Ty-ft P))
          ∙ ap-irr-star refl (⟦subst⟧Ty= NatStr= (weakenTy' (prev last) P) (⟦weakenTy+⟧ᵈ P Pᵈ NatStr= NatStr= (NatStrNat pp₀)) (suc (var last)) (tt , ssₛ , (varCL₁ ∙ NatStrNat pp₀) , tt) sucStr₁
            ∙ ap-irr-star refl (! (⟦weakenTy+⟧= P Pᵈ NatStr= NatStr= (NatStrNat pp₀))))

    uᵈ : isDefined (⟦ u ⟧Tm (⟦ Γ ⟧Ctx $ Γᵈ))
    uᵈ = ⟦⟧Tmᵈ Γᵈ du
  in
  betaNatSuc ∙ {!!}
  ∙ ! (⟦subst2⟧Tm= (⟦⟧Ty-ft P) NatStr= dS dSᵈ u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ du) (natelim P dO dS u) (Pᵈ , ⟦⟧Ty-ft P , dOᵈ , ⟦⟧Tmₛ dO , dO₁ , dSᵈ , ⟦⟧Tmₛ dS , dS₁ , uᵈ , ⟦⟧Tmₛ u , ⟦⟧Tm₁ Γᵈ du , tt) natelimStr₁)
⟦⟧TmEq Γᵈ (BetaIdRefl dA dP dd da) = {!#J#!}

⟦tsubst⟧Tyᵈ (uu i) tt δ δᵈ = tt
⟦tsubst⟧Tyᵈ (el i v) (vᵈ , vₛ , v₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ v vᵈ δ δᵈ ,
   ⟦⟧Tmₛ (v [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ v vᵈ δ δᵈ v₁ ∙ UUStrNat (⟦⟧Mor₀ δ)) , tt)
⟦tsubst⟧Tyᵈ (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) , tt)
⟦tsubst⟧Tyᵈ (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) , tt)
⟦tsubst⟧Tyᵈ nat tt δ δᵈ = tt
⟦tsubst⟧Tyᵈ (id A u v) (Aᵈ , A= , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
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
  let δ+ᵈ = ⟦weakenMor+⟧ᵈ ElStr= ElStr= δ δᵈ (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ) in
 (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ δ δᵈ a₁ ∙ ⟦tsubst⟧Ty= (uu i) tt δ δᵈ) ,
  ⟦tsubst⟧Tmᵈ b bᵈ (weakenMor+ δ) δ+ᵈ ,
  ⟦⟧Tmₛ (b [ weakenMor+ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ b bᵈ (weakenMor+ δ) δ+ᵈ b₁ ∙ UUStrNat (⟦⟧Mor₀ (weakenMor+ δ) {δᵈ = δ+ᵈ})) , tt)
⟦tsubst⟧Tmᵈ (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ u uᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
   ⟦⟧Tmₛ (u [ weakenMor+ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) u₁
     ∙ ⟦tsubst⟧Ty= B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) , tt)
⟦tsubst⟧Tmᵈ (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
   ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ f fᵈ δ δᵈ ,
   ⟦⟧Tmₛ (f [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ f fᵈ δ δᵈ f₁ ∙ ⟦tsubst⟧Ty= (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ) ,
   ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
   ⟦⟧Tmₛ (a [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ a aᵈ δ δᵈ a₁ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) , tt)

⟦tsubst⟧Tmᵈ (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  let δ+ᵈ = ⟦weakenMor+⟧ᵈ ElStr= ElStr= δ δᵈ (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ) in
 (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ δ δᵈ a₁ ∙ ⟦tsubst⟧Ty= (uu i) tt δ δᵈ) ,
  ⟦tsubst⟧Tmᵈ b bᵈ (weakenMor+ δ) δ+ᵈ ,
  ⟦⟧Tmₛ (b [ weakenMor+ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ b bᵈ (weakenMor+ δ) δ+ᵈ b₁ ∙ UUStrNat (⟦⟧Mor₀ (weakenMor+ δ) {δᵈ = δ+ᵈ})) , tt)
⟦tsubst⟧Tmᵈ (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦⟧Ty-ft (A [ δ ]Ty) ,
  ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
  ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
  ⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
  ⟦⟧Tmₛ (a [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ a aᵈ δ δᵈ a₁ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ,
  ⟦tsubst⟧Tmᵈ b bᵈ δ δᵈ ,
  ⟦⟧Tmₛ (b [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ b bᵈ δ δᵈ b₁ ∙ starstar (⟦⟧Ty-ft A) aₛ ∙ ap-irr-star (⟦tsubst⟧Tm= a aᵈ δ δᵈ) (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) , tt)
⟦tsubst⟧Tmᵈ (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦⟧Ty-ft (A [ δ ]Ty) ,
  ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
  ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
  ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
  ⟦⟧Tmₛ (u [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ ∙ ⟦tsubst⟧Ty= (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ) , tt)
⟦tsubst⟧Tmᵈ (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
 (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
  ⟦⟧Ty-ft (A [ δ ]Ty) ,
  ⟦tsubst⟧Tyᵈ B Bᵈ (weakenMor+ δ) (⟦weakenMor+⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
  ⟦⟧Ty-ft (B [ weakenMor+ δ ]Ty) ,
  ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
  ⟦⟧Tmₛ (u [ δ ]Tm) ,
  (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ ∙ ⟦tsubst⟧Ty= (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ) , tt)

⟦tsubst⟧Tmᵈ (nat i) tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ zero tt δ δᵈ = tt
⟦tsubst⟧Tmᵈ (suc u) (uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ ∙ ⟦tsubst⟧Ty= nat tt δ δᵈ) , tt)
⟦tsubst⟧Tmᵈ {X = X} (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (Pᵈs ,
   P=s ,
   dOᵈs ,
   dOₛs ,
   dO₁s ,
   dSᵈs ,
   dSₛs ,
   dS₁s ,
   uᵈs ,
   uₛs ,
   u₁s , tt)  where
      naturalityNat : star (⟦ δ ⟧Mor X _ $ δᵈ) (NatStr _) NatStr= (⟦⟧Mor₁ δ) ≡ NatStr X
      naturalityNat = NatStrNat (⟦⟧Mor₀ δ)

      sP= : _
      sP= = ! (⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= NatStr= naturalityNat)

      Pᵈs : isDefined (⟦ P [ weakenMor+ δ ]Ty ⟧Ty (NatStr X))
      Pᵈs = ⟦tsubst⟧Ty+ᵈ P Pᵈ δ δᵈ NatStr= NatStr= naturalityNat

      P=s : ft (⟦ P [ weakenMor+ δ ]Ty ⟧Ty (NatStr X) $ Pᵈs) ≡ NatStr X
      P=s = # (⟦⟧Ty-ft (P [ weakenMor+ δ ]Ty))

      dOᵈs : isDefined (⟦ dO [ δ ]Tm ⟧Tm X)
      dOᵈs = # (⟦tsubst⟧Tmᵈ dO dOᵈ δ δᵈ)

      dOₛs : is-section (⟦ dO [ δ ]Tm ⟧Tm X $ dOᵈs)
      dOₛs = # (⟦⟧Tmₛ (dO [ δ ]Tm))

      dO₁s : ∂₁ (⟦ dO [ δ ]Tm ⟧Tm X $ dOᵈs) ≡ _
      dO₁s = ⟦tsubst⟧Tm₁ dO dOᵈ δ δᵈ dO₁ ∙ starstar NatStr= zeroStrₛ ∙ ap-irr-star (zeroStrNat (⟦⟧Mor₀ δ)) (! sP=) 

      dSᵈs : isDefined
             (⟦ dS [ weakenMor+ (weakenMor+ δ) ]Tm ⟧Tm
              (⟦ P [ weakenMor+ δ ]Ty ⟧Ty (NatStr X) $ Pᵈs))
      dSᵈs = ⟦tsubst⟧Tm++ᵈ dS dSᵈ δ δᵈ (⟦⟧Ty-ft (P [ weakenMor+ δ ]Ty)) NatStr= (⟦⟧Ty-ft P) NatStr= (⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= NatStr= naturalityNat)

      dSₛs : is-section (⟦ dS [ weakenMor+ (weakenMor+ δ) ]Tm ⟧Tm
              (⟦ P [ weakenMor+ δ ]Ty ⟧Ty (NatStr X) $ Pᵈs) $ dSᵈs)
      dSₛs = ⟦⟧Tmₛ (dS [ weakenMor+ (weakenMor+ δ) ]Tm)

      dS₁s : ∂₁ (⟦ dS [ weakenMor+ (weakenMor+ δ) ]Tm ⟧Tm (⟦ P [ weakenMor+ δ ]Ty ⟧Ty (NatStr X) $ Pᵈs) $ dSᵈs)
           ≡ star (pp (⟦ P [ weakenMor+ δ ]Ty ⟧Ty (NatStr X) $ Pᵈs)) (star (sucStr (NatStr X) (varC last (NatStr X)) _ _) (star (qq (pp (NatStr X)) (NatStr X) NatStr= (pp₁ ∙ NatStr=)) (⟦ P [ weakenMor+ δ ]Ty ⟧Ty (NatStr X) $ Pᵈs) _ _) _ _) _ _
      dS₁s = ⟦tsubst⟧Tm++₁ dS dSᵈ δ δᵈ (⟦⟧Ty-ft (P [ weakenMor+ δ ]Ty)) NatStr= (⟦⟧Ty-ft P) NatStr= (⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= NatStr= naturalityNat) (ft-star ∙ pp₀) dS₁
             ∙ star-pp
               ∙ ap-irr-star
                   (ap pp (⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= NatStr= naturalityNat))
                   (starstar NatStr= sucStrₛ
                     ∙ ap-irr-star
                        (sucStrNat (qq₀ ∙ naturalityNat) ∙ ap-irr-sucStr refl (star-varCL ∙ ap ss (ap idC naturalityNat)))
                        (star-qqpp' (NatStrNat pp₀) ∙ ap-irr-star (ap-irr-qq (ap pp naturalityNat) naturalityNat) (⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= NatStr= naturalityNat)))

      uᵈs : isDefined (⟦ u [ δ ]Tm ⟧Tm X)
      uᵈs = ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ

      uₛs : is-section (⟦ u [ δ ]Tm ⟧Tm X $ uᵈs)
      uₛs = ⟦⟧Tmₛ (u [ δ ]Tm)

      u₁s : ∂₁ (⟦ u [ δ ]Tm ⟧Tm X $ uᵈs) ≡ _
      u₁s = ⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ ∙ naturalityNat

⟦tsubst⟧Tmᵈ (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tmᵈ a aᵈ δ δᵈ ,
   ⟦⟧Tmₛ (a [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ a aᵈ δ δᵈ a₁ ∙ ⟦tsubst⟧Ty= (uu i) tt δ δᵈ) ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ ∙ ⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ) ,
   ⟦tsubst⟧Tmᵈ v vᵈ δ δᵈ ,
   ⟦⟧Tmₛ (v [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ v vᵈ δ δᵈ v₁ ∙ ⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ) , tt)
⟦tsubst⟧Tmᵈ (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δ δᵈ ,
   ⟦⟧Ty-ft (A [ δ ]Ty) ,
   ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ ,
   ⟦⟧Tmₛ (u [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ) , tt)
⟦tsubst⟧Tmᵈ (jj A P d a b p) uᵈ X= Y= =
  {!#J#!}

⟦tsubst⟧Ty= (uu i) Aᵈ δ δᵈ =
  UUStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Ty= (el i v) (vᵈ , _) δ δᵈ =
  ElStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-ElStr refl
                 (⟦tsubst⟧Tm= v vᵈ δ δᵈ)
⟦tsubst⟧Ty= (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  PiStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-PiStr refl
                 (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                 (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
⟦tsubst⟧Ty= (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) δ δᵈ =
  SigStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-SigStr refl
                  (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                  (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
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

⟦tsubst⟧Tm= (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  piStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-piStr refl
                 (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                 (⟦tsubst⟧Tm+= b bᵈ δ δᵈ ElStr= ElStr= (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ))
⟦tsubst⟧Tm= (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  lamStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-lamStr refl
                  (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                  (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                  (⟦tsubst⟧Tm+= u uᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
⟦tsubst⟧Tm= (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) δ δᵈ =
  appStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-appStr refl
                  (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                  (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                  (⟦tsubst⟧Tm= f fᵈ δ δᵈ)
                  (⟦tsubst⟧Tm= a aᵈ δ δᵈ)

⟦tsubst⟧Tm= (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  sigStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-sigStr refl
                  (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                  (⟦tsubst⟧Tm+= b bᵈ δ δᵈ ElStr= ElStr= (⟦tsubst⟧Ty= (el i a) (aᵈ , aₛ , a₁ , tt) δ δᵈ))
⟦tsubst⟧Tm= (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) δ δᵈ =
  pairStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-pairStr refl
                   (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                   (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                   (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                   (⟦tsubst⟧Tm= b bᵈ δ δᵈ)
⟦tsubst⟧Tm= (pr1 A B u) (Aᵈ , A= , Bᵈ  , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  pr1StrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-pr1Str refl
                  (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                  (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                  (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
⟦tsubst⟧Tm= (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  pr2StrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-pr2Str refl
                  (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                  (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                  (⟦tsubst⟧Tm= u uᵈ δ δᵈ)

⟦tsubst⟧Tm= (nat i) tt δ δᵈ =
  natStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= zero tt δ δᵈ =
  zeroStrNat (⟦⟧Mor₀ δ)
⟦tsubst⟧Tm= (suc u) (uᵈ , uₛ , u₁ , tt) δ δᵈ =
  sucStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-sucStr refl
                  (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
⟦tsubst⟧Tm= (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  natelimStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-natelimStr refl
                      (⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= NatStr= (NatStrNat (⟦⟧Mor₀ δ)))
                      (⟦tsubst⟧Tm= dO dOᵈ δ δᵈ)
                      (⟦tsubst⟧Tm++= dS dSᵈ δ δᵈ (⟦⟧Ty-ft (P [ weakenMor+ δ ]Ty)) NatStr= (⟦⟧Ty-ft P) NatStr= (⟦tsubst⟧Ty+= P Pᵈ δ δᵈ NatStr= NatStr= (NatStrNat (⟦⟧Mor₀ δ))))
                      (⟦tsubst⟧Tm= u uᵈ δ δᵈ)

⟦tsubst⟧Tm= (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  idStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-idStr refl
                 (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                 (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
                 (⟦tsubst⟧Tm= v vᵈ δ δᵈ)
⟦tsubst⟧Tm= (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  reflStrNat (⟦⟧Mor₀ δ)
  ∙ ap-irr-reflStr refl
                   (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                   (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
⟦tsubst⟧Tm= (jj A P d a b p) uᵈ X= Y= =
  {!#J#!}



{-- To conclude, we prove a few more additional properties, needed for initiality -}

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
⟦⟧MorEq {Δ = ◇} {δ = ◇} {◇} Γᵈ tt = refl
⟦⟧MorEq {Γ' = Γ'} {Δ = Δ , B} {δ = δ , u} {δ' , u'} Γᵈ (dδ= , du=) = ap-irr-comp (ap-irr-qq (⟦⟧MorEq {Γ' = Γ'} {Δ' = Δ} Γᵈ dδ=) refl) (⟦⟧TmEq Γᵈ du=)

{- Interpretation of morphism substitution -}

⟦tsubst⟧Morᵈ : {X : Ob n} {Y Y' : Ob m} {Z : Ob k} (Y= : Y ≡ Y') (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (θ : Mor m k) (θᵈ : isDefined (⟦ θ ⟧Mor Y' Z)) → isDefined (⟦ θ [ δ ]Mor ⟧Mor X Z)
⟦tsubst⟧Mor= : {X : Ob n} {Y Y' : Ob m} {Z : Ob k} (Y= : Y ≡ Y') (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (θ : Mor m k) (θᵈ : isDefined (⟦ θ ⟧Mor Y' Z))
             → ⟦ θ [ δ ]Mor ⟧Mor X Z $ (⟦tsubst⟧Morᵈ Y= δ δᵈ θ θᵈ) ≡ comp (⟦ θ ⟧Mor Y' Z $ θᵈ) (⟦ δ ⟧Mor X Y $ δᵈ) (⟦⟧Mor₀ θ) (⟦⟧Mor₁ δ ∙ Y=) -- (⟦⟧Mor₁ δ ∙ Y= ∙ ! (⟦⟧Mor₀ θ))

⟦tsubst⟧Morᵈ refl δ δᵈ ◇ tt = tt
⟦tsubst⟧Morᵈ refl δ δᵈ (θ , u) (θᵈ , uᵈ , θ₁ , u₁ , tt) = (⟦tsubst⟧Morᵈ refl δ δᵈ θ θᵈ , ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ , ⟦⟧Mor₁ (θ [ δ ]Mor) , (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ u₁ ∙ ! (ap-irr-star (⟦tsubst⟧Mor= refl δ δᵈ θ θᵈ) refl ∙ star-comp)) , tt)

⟦tsubst⟧Mor= refl δ δᵈ ◇ θᵈ = ! (ptmor-unique _ _ (comp₀ ∙ ⟦⟧Mor₀ δ) (comp₁ ∙ ptmor₁))
⟦tsubst⟧Mor= refl δ δᵈ (θ , u) (θᵈ , uᵈ , θ₁ , u₁ , tt) =
 let thing = ! assoc ∙ ap-irr-comp (is-section= (ap ft (comp₁ {f = idC _} {g₀ = ⟦⟧Tm₀ u} {f₁ = id₁} ∙ u₁) ∙ ft-star ∙ ⟦⟧Mor₀ θ) (⟦⟧Tmₛ u) (! comp₁)) refl ∙ id-right (⟦⟧Mor₁ δ) in
  ap-irr-comp (ap-irr-qq (⟦tsubst⟧Mor= refl δ δᵈ θ θᵈ) refl ∙ qq-comp) (! (⟦tsubst⟧Tm= u uᵈ δ δᵈ))
  ∙ assoc {f₁ = starTm₁ _ (ft-star ∙ ⟦⟧Mor₀ θ) _ (⟦⟧Tmₛ u) u₁ _} {g₀ = qq₀}
  ∙ ! (assoc ∙ ap-irr-comp refl (ss-qq ∙ ap-irr-comp (ap-irr-qq thing (comp₁ ∙ u₁)) refl))
