{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import typetheory
open import syntx
open import rules
open import contextualcat

module _ (sC : StructuredCCat) where

open StructuredCCat sC
open preStructuredCCat presC renaming (ccat to C)
open CCat C renaming (Mor to MorC; id to idC)
open import partialinterpretation sC

ap-irr-IdStr : {A A' : Ob (suc n)} (A= : A ≡ A') {u u' : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ A} {uₛ' : is-section u'} {u₁' : ∂₁ u' ≡ A'} (u= : u ≡ u') {v v' : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ A} {vₛ' : is-section v'} {v₁' : ∂₁ v' ≡ A'} (v= : v ≡ v') → IdStr A u uₛ u₁ v vₛ v₁ ≡ IdStr A' u' uₛ' u₁' v' vₛ' v₁'
ap-irr-IdStr refl refl refl = refl

ap-irr-lamStr : {n : ℕ} {B B' : _} (B= : B ≡ B') {u u' : _} (u= : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} → lamStr {n = n} B u uₛ u₁ ≡ lamStr B' u' uₛ' u₁'
ap-irr-lamStr refl refl = refl

ap-irr-appStr : {n : ℕ} {B B' : _} (B= : B ≡ B') {f f' : _} (f= : f ≡ f') {fₛ : _} {fₛ' : _} {f₁ : _} {f₁' : _} {a a' : _} (a= : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} → appStr {n = n} B f fₛ f₁ a aₛ a₁ ≡ appStr B' f' fₛ' f₁' a' aₛ' a₁'
ap-irr-appStr refl refl refl = refl

ap-irr-piStr : {n : ℕ} {i : ℕ} {a a' : _} (a= : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} {b b' : _} (b= : b ≡ b') {bₛ : _} {bₛ' : _} {b₁ : _} {b₁' : _} → piStr {n = n} i a aₛ a₁ b bₛ b₁ ≡ piStr i a' aₛ' a₁' b' bₛ' b₁'
ap-irr-piStr refl refl = refl

ap-irr-sigStr : {n : ℕ} {i : ℕ} {a a' : _} (a= : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} {b b' : _} (b= : b ≡ b') {bₛ : _} {bₛ' : _} {b₁ : _} {b₁' : _} → sigStr {n = n} i a aₛ a₁ b bₛ b₁ ≡ sigStr i a' aₛ' a₁' b' bₛ' b₁'
ap-irr-sigStr refl refl = refl

ap-irr-pairStr : {n : ℕ} {B B' : _} (B= : B ≡ B') {a a' : _} (a= : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} {b b' : _} (b= : b ≡ b') {bₛ : _} {bₛ' : _} {b₁ : _} {b₁' : _} → pairStr {n = n} B a aₛ a₁ b bₛ b₁ ≡ pairStr B' a' aₛ' a₁' b' bₛ' b₁'
ap-irr-pairStr refl refl refl = refl

ap-irr-pr1Str : {n : ℕ} {B B' : _} (B= : B ≡ B') {u u' : _} (u= : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} → pr1Str {n = n} B u uₛ u₁ ≡ pr1Str B' u' uₛ' u₁'
ap-irr-pr1Str refl refl = refl

ap-irr-pr2Str : {n : ℕ} {B B' : _} (B= : B ≡ B') {u u' : _} (u= : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} → pr2Str {n = n} B u uₛ u₁ ≡ pr2Str B' u' uₛ' u₁'
ap-irr-pr2Str refl refl = refl

ap-irr-idStr : {n : ℕ} {i : ℕ} {a a' : _} (a= : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} {u u' : _} (u= : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} {v v' : _} (v= : v ≡ v') {vₛ : _} {vₛ' : _} {v₁ : _} {v₁' : _} → idStr {n = n} i a aₛ a₁ u uₛ u₁ v vₛ v₁ ≡ idStr {n = n} i a' aₛ' a₁' u' uₛ' u₁' v' vₛ' v₁'
ap-irr-idStr refl refl refl = refl

ap-irr-reflStr : {n : ℕ} {a a' : _} (a= : a ≡ a') {u u' : _} (u= : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} → reflStr {n = n} a u uₛ u₁ ≡ reflStr {n = n} a' u' uₛ' u₁'
ap-irr-reflStr refl refl = refl

{- Predicate saying whether an object "respects" a context in the sense that the types in Γ correspond to their interpretation in X.
   We cannot use (X ≡ ⟦ Γ ⟧) instead because it fails the termination checker somehow (not sure about that anymore, we should try again) -}

respectsCtx : (X : Ob n) (Γ : Ctx n) → Prop
respectsCtx {zero} X ◇ = Unit
respectsCtx {suc n} X (Γ , A) = respectsCtx (ft X) Γ × Σ (isDefined (⟦ A ⟧Ty (ft X))) (λ Aᵈ → ⟦ A ⟧Ty (ft X) $ Aᵈ ≡ X)

{- Totality of the partial interpretation functions -}

⟦⟧Tyᵈ  : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) → isDefined (⟦ A ⟧Ty X)
⟦⟧Tmᵈ  : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → isDefined (⟦ u ⟧Tm X)
⟦⟧Morᵈ : {Γ : Ctx n} {Δ : Ctx m} {X : Ob n} {Y : Ob m} (r : respectsCtx X Γ) (r' : respectsCtx Y Δ) {δ : Mor n m} (dδ : Γ ⊢ δ ∷> Δ) → isDefined (⟦ δ ⟧Mor X Y)


{- Interpretation of definitional equalities -}

⟦⟧TyEq : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A')) {Aᵈ : isDefined (⟦ A ⟧Ty X)} {A'ᵈ : isDefined (⟦ A' ⟧Ty X)}
        → ⟦ A ⟧Ty X $ Aᵈ ≡ ⟦ A' ⟧Ty X $ A'ᵈ
⟦⟧TmEq : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A)) {uᵈ : isDefined (⟦ u ⟧Tm X)} {u'ᵈ : isDefined (⟦ u' ⟧Tm X)}
        → ⟦ u ⟧Tm X $ uᵈ ≡ ⟦ u' ⟧Tm X $ u'ᵈ



{- Various lemmas saying that the interpretation functions are well-behaved -}

⟦⟧Tm₁ : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {u : TmExpr n} {uᵈ : isDefined (⟦ u ⟧Tm X)} {A : TyExpr n} {Aᵈ : isDefined (⟦ A ⟧Ty X)} (du : Derivable (Γ ⊢ u :> A)) → ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ ⟦ A ⟧Ty X $ Aᵈ

⟦idMor⟧ᵈ : {X Y : Ob n} → Y ≡ X → isDefined (⟦ idMor n ⟧Mor X Y)
⟦idMor⟧= : {X Y : Ob n} (p : Y ≡ X) → ⟦ idMor n ⟧Mor X Y $ ⟦idMor⟧ᵈ p ≡ idC X


cong⟦⟧Ty : {X Y : Ob n} {A : TyExpr n} → X ≡ Y → isDefined (⟦ A ⟧Ty X) → isDefined (⟦ A ⟧Ty Y)
cong⟦⟧Ty refl Aᵈ = Aᵈ

cong⟦⟧Tm : {X Y : Ob n} {u : TmExpr n} → X ≡ Y → isDefined (⟦ u ⟧Tm X) → isDefined (⟦ u ⟧Tm Y)
cong⟦⟧Tm refl uᵈ = uᵈ

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
             → star (qq^ k X=) (⟦ A ⟧Ty X $ Aᵈ) (qq^₁ k X= ∙ ! (⟦⟧Ty-ft A)) ≡ ⟦ weakenTy' k A ⟧Ty Y $ ⟦weakenTy⟧ᵈ' k A Aᵈ X= Y=

⟦weakenTm⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ ft^ k X) {Y : Ob (suc n)} (Y= : Y ≡ star^ k X+ X X=)
            → starTm (qq^ k X=) (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u ∙ ! (qq^₁ k X=)) ≡ ⟦ weakenTm' k u ⟧Tm Y $ ⟦weakenTm⟧ᵈ' k u uᵈ X= Y=

⟦weakenTy+⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc n))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
              → (X= : ft X+ ≡ ft^ k X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : Y ≡ star^ (prev k) X+ X' (X= ∙ ap (ft^ k) (! p)))
              → star+ (qq^ k X=) (⟦ A ⟧Ty X' $ Aᵈ) (ap ft (⟦⟧Ty-ft A) ∙ p ∙ ! (qq^₁ k X=)) ≡ ⟦ weakenTy' (prev k) A ⟧Ty Y $ ⟦weakenTy⟧ᵈ' (prev k) A Aᵈ (X= ∙ ap (ft^ k) (! p)) Y=

⟦weakenTm+⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X' : Ob (suc n)} {X : Ob n} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X= : ft X+ ≡ ft^ k X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : Y ≡ star^ (prev k) X+ X' (X= ∙ ap (ft^ k) (! p)))
              → starTm+ (qq^ k X=) (⟦ u ⟧Tm X' $ uᵈ) (ap ft (⟦⟧Tm₀ u) ∙ p ∙ ! (qq^₁ k X=)) ≡ ⟦ weakenTm' (prev k) u ⟧Tm Y $ ⟦weakenTm⟧ᵈ' (prev k) u uᵈ (X= ∙ ap (ft^ k) (! p)) Y=

⟦weakenTm⟧₁' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ ft^ k X) {Y : Ob (suc n)} (Y= : Y ≡ star^ k X+ X X=)
            → {Z : Ob (suc n)} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Z)
            → ∂₁ (⟦ weakenTm' k u ⟧Tm Y $ ⟦weakenTm⟧ᵈ' k u uᵈ X= Y=) ≡ star (qq^ k X=) Z (qq^₁ k X= ∙ ! (⟦⟧Tm₁-ft u) ∙ ap ft u₁)
            

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

{- Definitions -}

respectsCtxExt : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) (A : TyExpr n) {Aᵈ : isDefined (⟦ A ⟧Ty X)}
              → respectsCtx (⟦ A ⟧Ty X $ Aᵈ) (Γ , A)
respectsCtxExt r A {Aᵈ} rewrite ⟦⟧Ty-ft A {Aᵈ} = r , _ , refl

⟦⟧Tyᵈ r UU = tt
⟦⟧Tyᵈ r {A = el i v} (El dv) =
  (⟦⟧Tmᵈ r dv ,
   ⟦⟧Tmₛ v ,
   (⟦⟧Tm₁ r dv ∙ ap (UUStr i) (! (⟦⟧Tm₀ v))) , tt)
⟦⟧Tyᵈ r {A = pi A B} (Pi dA dB) =
  (⟦⟧Tyᵈ r dA ,
   ⟦⟧Tyᵈ (respectsCtxExt r A) dB , tt)
⟦⟧Tyᵈ r {A = sig A B} (Sig dA dB) =
  (⟦⟧Tyᵈ r dA ,
   ⟦⟧Tyᵈ (respectsCtxExt r A) dB , tt)
⟦⟧Tyᵈ r Nat = tt
⟦⟧Tyᵈ r {A = id A a b} (Id dA da db) =
  (⟦⟧Tyᵈ r dA ,
   ⟦⟧Tmᵈ r da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ r da ,
   ⟦⟧Tmᵈ r db ,
   ⟦⟧Tmₛ b ,
   ⟦⟧Tm₁ r db , tt)

⟦⟧Tmᵈ r (VarLast dA) = tt
⟦⟧Tmᵈ r {u = var (prev x)} (VarPrev dA dx) = (⟦⟧Tmᵈ (fst r) dx , ⟦⟧Tm₀ (var x) , tt)
⟦⟧Tmᵈ r (Conv dA du dA=) = ⟦⟧Tmᵈ r du

⟦⟧Tmᵈ r {u = uu i} UUUU = tt

⟦⟧Tmᵈ r {u = pi i a b} (PiUU da db) =
  (⟦⟧Tmᵈ r da ,
   ⟦⟧Tmₛ a ,
   (⟦⟧Tm₁ r da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))) ,
   ⟦⟧Tmᵈ (respectsCtxExt r (el i a) {Aᵈ = ⟦⟧Tmᵈ r da , ⟦⟧Tmₛ a , (⟦⟧Tm₁ r da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))) , tt}) db ,
   ⟦⟧Tmₛ b ,
   ⟦⟧Tm₁ (respectsCtxExt r (el i a) {Aᵈ = ⟦⟧Tmᵈ r da , ⟦⟧Tmₛ a , (⟦⟧Tm₁ r da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))) , tt}) db , tt)
⟦⟧Tmᵈ r {u = lam A B u} (Lam dA dB du) =
  (⟦⟧Tyᵈ r dA ,
   ⟦⟧Tyᵈ (respectsCtxExt r A) dB ,
   ⟦⟧Tmᵈ (respectsCtxExt r A) du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ (respectsCtxExt r A) du , tt)
⟦⟧Tmᵈ r {u = app A B f a} (App dA dB df da) =
  (⟦⟧Tyᵈ r dA ,
   ⟦⟧Tyᵈ (respectsCtxExt r A) dB ,
   ⟦⟧Tmᵈ r df ,
   ⟦⟧Tmₛ f ,
   ⟦⟧Tm₁ r df ,
   ⟦⟧Tmᵈ r da ,
   ⟦⟧Tmₛ a ,
   (⟦⟧Tm₁ r da ∙ ! (⟦⟧Ty-ft B)) , tt)

⟦⟧Tmᵈ r {u = sig i a b} (SigUU da db) =
  (⟦⟧Tmᵈ r da ,
   ⟦⟧Tmₛ a ,
   (⟦⟧Tm₁ r da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))) ,
   ⟦⟧Tmᵈ (respectsCtxExt r (el i a) {Aᵈ = ⟦⟧Tmᵈ r da , ⟦⟧Tmₛ a , (⟦⟧Tm₁ r da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))) , tt}) db ,
   ⟦⟧Tmₛ b ,
   ⟦⟧Tm₁ (respectsCtxExt r (el i a) {Aᵈ = ⟦⟧Tmᵈ r da , ⟦⟧Tmₛ a , (⟦⟧Tm₁ r da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))) , tt}) db , tt)
⟦⟧Tmᵈ r {u = pair A B a b} (Pair dA dB da db) =
  (⟦⟧Tyᵈ r dA ,
   ⟦⟧Tyᵈ (respectsCtxExt r A) dB ,
   ⟦⟧Tmᵈ r da ,
   ⟦⟧Tmₛ a ,
   (⟦⟧Tm₁ r da ∙ ! (⟦⟧Ty-ft B)) ,
   ⟦⟧Tmᵈ r db ,
   ⟦⟧Tmₛ b ,
   (⟦⟧Tm₁ r db ∙ ⟦subst⟧Ty= (⟦⟧Ty-ft A) B (⟦⟧Tyᵈ (respectsCtxExt r A) dB) a (⟦⟧Tmᵈ r da) (⟦⟧Tm₁ r da)) , tt)
⟦⟧Tmᵈ r {u = pr1 A B u} (Pr1 dA dB du) =
  (⟦⟧Tyᵈ r dA ,
   ⟦⟧Tyᵈ (respectsCtxExt r A) dB ,
   ⟦⟧Tmᵈ r du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ r du , tt)
⟦⟧Tmᵈ r {u = pr2 A B u} (Pr2 dA dB du) =
  (⟦⟧Tyᵈ r dA ,
   ⟦⟧Tyᵈ (respectsCtxExt r A) dB ,
   ⟦⟧Tmᵈ r du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ r du , tt)

⟦⟧Tmᵈ r {u = nat i} NatUU = tt
⟦⟧Tmᵈ r {u = zero} Zero = tt
⟦⟧Tmᵈ r {u = suc u} (Suc du) =
  (⟦⟧Tmᵈ r du ,
   ⟦⟧Tmₛ u ,
   (⟦⟧Tm₁ r du ∙ ap NatStr (! (⟦⟧Tm₀ u))) , tt)

⟦⟧Tmᵈ r {u = id i a u v} (IdUU da du dv) =
  (⟦⟧Tmᵈ r da ,
   ⟦⟧Tmₛ a ,
   (⟦⟧Tm₁ r da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))) ,
   ⟦⟧Tmᵈ r du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ r {A = el i a} {Aᵈ = ⟦⟧Tmᵈ r da , ⟦⟧Tmₛ a , (⟦⟧Tm₁ r da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))) , tt} du ,
   ⟦⟧Tmᵈ r dv ,
   ⟦⟧Tmₛ v ,
   ⟦⟧Tm₁ r {A = el i a} {Aᵈ = ⟦⟧Tmᵈ r da , ⟦⟧Tmₛ a , (⟦⟧Tm₁ r da ∙ ap (UUStr i) (! (⟦⟧Tm₀ a))) , tt} dv , tt)
⟦⟧Tmᵈ r {u = refl A a} (Refl dA da) =
  (⟦⟧Tyᵈ r dA ,
   ⟦⟧Tmᵈ r da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ r da , tt)


⟦⟧Morᵈ {Δ = ◇} r r' {◇} tt = tt
⟦⟧Morᵈ {Δ = Δ , B} r (r' , Bᵈ , B=) {δ , u} (dδ , du) =
  let δᵈ = ⟦⟧Morᵈ r r' dδ in
  (δᵈ ,
   ⟦⟧Tmᵈ r du ,
   ⟦⟧Mor₁ δ ,
   (⟦⟧Tm₁ r {Aᵈ = ⟦tsubst⟧Tyᵈ B Bᵈ δ δᵈ} du ∙ ! (⟦tsubst⟧Ty= B Bᵈ δ δᵈ) ∙ ap2-irr star refl B=) , tt)

⟦⟧Tm₁ r (VarLast {A = A} dA) =
  ss₁ ∙ ap2-irr star (ap2-irr comp (ap pp id₁) (ap idC (! pp₀)) ∙ id-left ∙ refl) (id₁ ∙ ! (snd (snd r))) {b' = pp₁ ∙ ! (⟦⟧Ty-ft A)}
      ∙ ⟦weakenTy⟧=' last A (fst (snd r)) refl refl
⟦⟧Tm₁ r {u = var (prev k)} (VarPrev {A = A} dA dk) =
  ss₁ ∙ ap2-irr star (! (assoc {q = ! (pp₀ ∙ comp₁)})
                      ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ (var k) ∙ ap idC (⟦⟧Tm₀ (var k) ∙ ! pp₁)) refl
                      ∙ id-right)
                      (comp₁ ∙ ⟦⟧Tm₁ (fst r) dk)
      ∙ ⟦weakenTy⟧=' last A (⟦⟧Tyᵈ (fst r) dA) refl refl
⟦⟧Tm₁ r (Conv dA du dA=) = ⟦⟧Tm₁ r du ∙ ⟦⟧TyEq r dA= {Aᵈ = ⟦⟧Tyᵈ r dA}

⟦⟧Tm₁ r {u = uu i} UUUU = uuStr₁

⟦⟧Tm₁ r {u = pi i a b} (PiUU da db) = piStr₁ ∙ ap (UUStr i) (⟦⟧Tm₀ a)
⟦⟧Tm₁ r {u = lam A B u} (Lam dA dB du) = lamStr₁
⟦⟧Tm₁ r {u = app A B f a} (App dA dB df da) = appStr₁ ∙ ! (⟦subst⟧Ty= (⟦⟧Ty-ft A) B (⟦⟧Tyᵈ (respectsCtxExt r A) dB) a (⟦⟧Tmᵈ r da) (⟦⟧Tm₁ r da))

⟦⟧Tm₁ r {u = sig i a b} (SigUU da db) = sigStr₁ ∙ ap (UUStr i) (⟦⟧Tm₀ a)
⟦⟧Tm₁ r {u = pair A B a b} (Pair dA dB da db) = pairStr₁
⟦⟧Tm₁ r {u = pr1 A B u} (Pr1 dA dB du) = pr1Str₁ ∙ ⟦⟧Ty-ft B
⟦⟧Tm₁ r {u = pr2 A B u} (Pr2 dA dB du) = pr2Str₁ ∙ ! (⟦subst⟧Ty= (⟦⟧Ty-ft A) B (⟦⟧Tyᵈ (respectsCtxExt r A) dB) (pr1 A B u) (⟦⟧Tyᵈ r dA , ⟦⟧Tyᵈ (respectsCtxExt r A) dB , ⟦⟧Tmᵈ r du , ⟦⟧Tmₛ u , ⟦⟧Tm₁ r du , tt) (pr1Str₁ ∙ ⟦⟧Ty-ft B))

⟦⟧Tm₁ r {u = nat i} NatUU = natStr₁
⟦⟧Tm₁ r {u = zero} Zero = zeroStr₁
⟦⟧Tm₁ r {u = suc u} (Suc du) = sucStr₁ ∙ ap NatStr (⟦⟧Tm₀ u)

⟦⟧Tm₁ r {u = id i a u v} (IdUU da du dv) = idStr₁ ∙ ap (UUStr i) (⟦⟧Tm₀ a)
⟦⟧Tm₁ r {u = refl A a} (Refl dA da) = reflStr₁

⟦idMor⟧ᵈ {zero} refl = tt
⟦idMor⟧ᵈ {suc n} {Y = Y} refl = ⟦weakenMor+⟧ᵈ refl refl (idMor n) (⟦idMor⟧ᵈ {n = n} refl) (ap2-irr star (⟦idMor⟧= refl) refl ∙ star-id)

⟦idMor⟧= {zero} refl = ! (ptmor-unique _ (idC _) id₀ (id₁ ∙ pt-unique _))
⟦idMor⟧= {suc n} {Y = Y} refl = ⟦weakenMor+⟧= {X = ft Y} refl {Y+ = Y} refl (idMor n) (⟦idMor⟧ᵈ{n = n} refl) (ap2-irr star (⟦idMor⟧= refl) refl ∙ star-id) ∙ ap2-irr qq (⟦idMor⟧= refl) refl ∙ qq-id


qq^=! : (k : Fin (suc n)) {X : Ob n} {X+ : Ob (suc (n -F' k))} (X= : ft X+ ≡ ft^ k X) (A : TyExpr n) (Aᵈ : isDefined (⟦ A ⟧Ty X)) → qq^ k X= ≡ qq^ k (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A {Aᵈ = Aᵈ})))
qq^=! k X= A Aᵈ = ap-irr (λ X → qq^ k {X = X}) (! (⟦⟧Ty-ft A)) {b = X=} {b' = X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A)) }

qq^= : (k : Fin (suc n)) {X : Ob n} {X+ : Ob (suc (n -F' k))} (X= : ft X+ ≡ ft^ k X) (A : TyExpr n) (Aᵈ : isDefined (⟦ A ⟧Ty X)) → qq^ k (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A {Aᵈ = Aᵈ}))) ≡ qq^ k X=
qq^= k X= A Aᵈ = ap-irr (λ X → qq^ k {X = X}) (⟦⟧Ty-ft A) {b = X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A)) } {b' = X=}

qq^=p : (k : Fin (suc n)) {X : Ob n} {X+ : Ob (suc (n -F' k))} (X= : ft X+ ≡ ft^ k X) {X' : Ob n} (p : X' ≡ X) → qq^ k (X= ∙ ap (ft^ k) (! p)) ≡ qq^ k X=
qq^=p k X= refl = refl

⟦weakenTm⟧ᵈ'prev : (k : Fin (suc n)) {X+ : Ob (suc (suc n -F' (prev k)))} {X : Ob (suc n)} {X' : Ob n} (u : TmExpr (suc n))
            → isDefined (⟦ u ⟧Tm X)
            → (X= : ft X+ ≡ ft^ k X') {Y : Ob (suc (suc n))}
            → (p : ft X ≡ X')
            → (Y= : star (qq^ k X=) X (qq^₁ k X= ∙ ! p) ≡ Y)
            → isDefined (⟦ weakenTm' (prev k) u ⟧Tm Y)
⟦weakenTm⟧ᵈ'prev k u uᵈ X= refl refl = ⟦weakenTm⟧ᵈ' (prev k) u uᵈ X= refl

⟦weakenTm⟧₁'prev : (k : Fin (suc n)) {X+ : Ob (suc (suc n -F' (prev k)))} {X : Ob (suc n)} {X' : Ob n} (u : TmExpr (suc n))
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ ft^ k X') {Y : Ob (suc (suc n))}
            → (p : ft X ≡ X')
            → (Y= : star (qq^ k X=) X (qq^₁ k X= ∙ ! p) ≡ Y)
            → {Z : Ob (suc (suc n))} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Z)
            → ∂₁ (⟦ weakenTm' (prev k) u ⟧Tm Y $ ⟦weakenTm⟧ᵈ'prev k u uᵈ X= p Y=) ≡ star (qq (qq^ k X=) (ft Z) (qq^₁ k X= ∙ ! p ∙ ap ft (! (⟦⟧Tm₁-ft u) ∙ ap ft u₁) )) Z qq₁
⟦weakenTm⟧₁'prev k u uᵈ X= refl refl u₁ = ⟦weakenTm⟧₁' (prev k) u uᵈ X= refl u₁ ∙ ap2-irr star (ap2-irr qq refl (! (⟦⟧Tm₁-ft u) ∙ ap ft u₁)) refl

⟦weakenTy⟧ᵈ' k (uu i) Aᵈ _ _ = tt
⟦weakenTy⟧ᵈ' k (el i v) (vᵈ , vₛ , v₁ , tt) X= Y= =
  (⟦weakenTm⟧ᵈ' k v vᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weakenTm⟧₁' k v vᵈ X= Y= v₁ ∙ UUStrNat (qq^ k X=) (⟦⟧Tm₀ v ∙ ! (qq^₁ k X=)) ∙ ap (UUStr i) (qq^₀ k X= ∙ ! (⟦⟧Tm₀ (weakenTm' k v) ∙ Y=))) , tt)
⟦weakenTy⟧ᵈ' k (pi A B) (Aᵈ , Bᵈ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy⟧ᵈ' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl) , tt)
⟦weakenTy⟧ᵈ' k (sig A B) (Aᵈ , Bᵈ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy⟧ᵈ' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl) , tt)
⟦weakenTy⟧ᵈ' k nat Aᵈ _ _ = tt
⟦weakenTy⟧ᵈ' k (id A u v) (Aᵈ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X= Y= u₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X= Y=) ,
   ⟦weakenTm⟧ᵈ' k v vᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weakenTm⟧₁' k v vᵈ X= Y= v₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X= Y=) , tt)

⟦weakenTm⟧ᵈ' last (var last) tt X= Y= = (tt , (ss₀ ∙ id₀) , tt)
⟦weakenTm⟧ᵈ' (prev k) (var last) tt X= Y= = tt
⟦weakenTm⟧ᵈ' last (var (prev x)) (xᵈ , x₀ , tt) X= Y= = (cong⟦⟧Tm {u = var x} (ap ft (! (ap ft Y= ∙ X=))) xᵈ , (⟦⟧Tm₀ (var x)) , tt) , ((ss₀ ∙ comp₀ ∙ pp₀) , tt)
⟦weakenTm⟧ᵈ' (prev k) (var (prev x)) (xᵈ , x₀ , tt) X= Y= = (⟦weakenTm⟧ᵈ' k (var x) xᵈ X= (ap ft Y= ∙ ft-star ∙ qq^₀ k X=) , ⟦⟧Tm₀ (weakenTm' k (var x)) , tt)

⟦weakenTm⟧ᵈ' k (uu i) tt X= Y= = tt

⟦weakenTm⟧ᵈ' k (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X= Y= =
  (⟦weakenTm⟧ᵈ' k a aᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X= Y= a₁ ∙ UUStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)) ∙ ap (UUStr i) (qq^₀ k X= ∙ ! (⟦⟧Tm₀ (weakenTm' k a) ∙ Y=))) ,
   ⟦weakenTm⟧ᵈ'prev k b bᵈ X= (ElStr= ∙ ⟦⟧Tm₀ a) (ElStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) b) ,
   (⟦weakenTm⟧₁'prev k b bᵈ X= (ElStr= ∙ ⟦⟧Tm₀ a) (ElStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)) b₁ ∙ UUStrNat (qq (qq^ k X=) _ (qq^₁ k X= ∙ ! (ap ft UUStr= ∙ ElStr= ∙ ⟦⟧Tm₀ a))) (! UUStr= ∙ ! qq₁) ∙ ap (UUStr i) (qq₀ ∙ ap2-irr star refl UUStr= ∙ ElStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=))) , tt)
⟦weakenTm⟧ᵈ' k (lam A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy⟧ᵈ' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl) ,
   ⟦weakenTm⟧ᵈ'prev k u uᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) u) ,
   (⟦weakenTm⟧₁'prev k u uᵈ X= (⟦⟧Ty-ft A) (⟦weakenTy⟧=' k A Aᵈ X= Y=) u₁ ∙ ap2-irr star (ap2-irr qq (qq^=! k X= A Aᵈ) (⟦⟧Ty-ft B)) refl
     ∙ ⟦weakenTy⟧=' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl)) , tt)
⟦weakenTm⟧ᵈ' k (app A B f a) (Aᵈ , Bᵈ , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy⟧ᵈ' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl) ,
   ⟦weakenTm⟧ᵈ' k f fᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k f) ,
   (⟦weakenTm⟧₁' k f fᵈ X= Y= f₁ ∙ PiStrNat (qq^ k X=) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (qq^₁ k X=)) ∙ ap PiStr (ap2-irr star (ap2-irr qq (qq^=! k X= A Aᵈ) (⟦⟧Ty-ft B)) refl ∙ ⟦weakenTy⟧=' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl))) ,
   ⟦weakenTm⟧ᵈ' k a aᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X= Y= a₁ ∙ ! (ft-star ∙ qq^₀ (prev k) (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) ∙ ap2-irr star (qq^= k X= A Aᵈ) (! (⟦⟧Ty-ft B))) ∙ ap ft (⟦weakenTy⟧=' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl))) , tt)

⟦weakenTm⟧ᵈ' k (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X= Y= =
  (⟦weakenTm⟧ᵈ' k a aᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X= Y= a₁ ∙ UUStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)) ∙ ap (UUStr i) (qq^₀ k X= ∙ ! (⟦⟧Tm₀ (weakenTm' k a) ∙ Y=))) ,
   ⟦weakenTm⟧ᵈ'prev k b bᵈ X= (ElStr= ∙ ⟦⟧Tm₀ a) (ElStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) b) ,
   (⟦weakenTm⟧₁'prev k b bᵈ X= (ElStr= ∙ ⟦⟧Tm₀ a) (ElStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)) b₁ ∙ UUStrNat (qq (qq^ k X=) _ (qq^₁ k X= ∙ ! (ap ft UUStr= ∙ ElStr= ∙ ⟦⟧Tm₀ a))) (! UUStr= ∙ ! qq₁) ∙ ap (UUStr i) (qq₀ ∙ ap2-irr star refl UUStr= ∙ ElStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=))) , tt)
⟦weakenTm⟧ᵈ' k (pair A B a b) (Aᵈ , Bᵈ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy⟧ᵈ' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl) ,
   ⟦weakenTm⟧ᵈ' k a aᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X= Y= a₁ ∙ ! (ft-star ∙ qq^₀ (prev k) (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) ∙ ap2-irr star (qq^= k X= A Aᵈ) (! (⟦⟧Ty-ft B))) ∙ ap ft (⟦weakenTy⟧=' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl))) ,
   ⟦weakenTm⟧ᵈ' k b bᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k b) ,
   (⟦weakenTm⟧₁' k b bᵈ X= Y= b₁ ∙ starstar (qq^ k X=) _ (⟦⟧Tmₛ a) _ {a₀ = ⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)} {p = ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (qq^₁ k X=)} ∙ ap2-irr star (⟦weakenTm⟧=' k a aᵈ X= Y=) (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl))) , tt)
⟦weakenTm⟧ᵈ' k (pr1 A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy⟧ᵈ' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X= Y= u₁ ∙ SigStrNat (qq^ k X=) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (qq^₁ k X=)) ∙ ap SigStr (ap2-irr star (ap2-irr qq (qq^=! k X= A Aᵈ) (⟦⟧Ty-ft B)) refl ∙ ⟦weakenTy⟧=' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl))) , tt)
⟦weakenTm⟧ᵈ' k (pr2 A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTy⟧ᵈ' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X= Y= u₁ ∙ SigStrNat (qq^ k X=) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (qq^₁ k X=)) ∙ ap SigStr (ap2-irr star (ap2-irr qq (qq^=! k X= A Aᵈ) (⟦⟧Ty-ft B)) refl ∙ ⟦weakenTy⟧=' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (⟦weakenTy⟧=' k A Aᵈ X= Y=) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl))) , tt)

⟦weakenTm⟧ᵈ' k (nat i) tt X= Y= = tt
⟦weakenTm⟧ᵈ' k zero tt X= Y= = tt
⟦weakenTm⟧ᵈ' k (suc u) (uᵈ , uₛ , u₁ , tt) X= Y= =
  (⟦weakenTm⟧ᵈ' k u uᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X= Y= u₁ ∙ NatStrNat (qq^ k X=) (⟦⟧Tm₀ u ∙ ! (qq^₁ k X=)) ∙ ap NatStr (qq^₀ k X= ∙ ! Y= ∙ ! (⟦⟧Tm₀ (weakenTm' k u)))) , tt)

⟦weakenTm⟧ᵈ' k (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X= Y= =
  (⟦weakenTm⟧ᵈ' k a aᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weakenTm⟧₁' k a aᵈ X= Y= a₁ ∙ UUStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)) ∙ ap (UUStr i) (qq^₀ k X= ∙ ! Y= ∙ ! (⟦⟧Tm₀ (weakenTm' k a)))) ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X= Y= u₁ ∙ ElStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)) ,
   ⟦weakenTm⟧ᵈ' k v vᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weakenTm⟧₁' k v vᵈ X= Y= v₁ ∙ ElStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)) ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k a aᵈ X= Y=)) , tt)
⟦weakenTm⟧ᵈ' k (refl A u) (Aᵈ , uᵈ , uₛ , u₁ , tt) X= Y= =
  (⟦weakenTy⟧ᵈ' k A Aᵈ X= Y= ,
   ⟦weakenTm⟧ᵈ' k u uᵈ X= Y= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weakenTm⟧₁' k u uᵈ X= Y= u₁ ∙ ⟦weakenTy⟧=' k A Aᵈ X= Y=) , tt)

⟦weakenTy⟧=' k (uu i) _ X= Y= =
  UUStrNat (qq^ k X=) (! (qq^₁ k X=))
  ∙ ap (UUStr i) (qq^₀ k X= ∙ ! Y=)
⟦weakenTy⟧=' k (el i v) (vᵈ , vₛ , v₁ , tt) X= Y= =
  ElStrNat (qq^ k X=) (⟦⟧Tm₀ v ∙ ! (qq^₁ k X=))
  ∙ ap-irr2 (ElStr i) (⟦weakenTm⟧=' k v vᵈ X= Y=)
⟦weakenTy⟧=' k (pi A B) (Aᵈ , Bᵈ , tt) X= Y= =
  PiStrNat (qq^ k X=) (! (qq^₁ k X= ∙ ! (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A)))
  ∙ ap PiStr (ap2-irr star (ap2-irr qq (! (qq^= k X= A Aᵈ)) (⟦⟧Ty-ft B)) refl
             ∙ ⟦weakenTy⟧=' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (ap2-irr star (! (qq^=! k X= A Aᵈ)) refl ∙ ⟦weakenTy⟧=' k A Aᵈ X= Y=)))
⟦weakenTy⟧=' k (sig A B) (Aᵈ , Bᵈ , tt) X= Y= =
  SigStrNat (qq^ k X=) (! (qq^₁ k X= ∙ ! (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A)))
  ∙ ap SigStr (ap2-irr star (ap2-irr qq (! (qq^= k X= A Aᵈ)) (⟦⟧Ty-ft B)) refl
             ∙ ⟦weakenTy⟧=' (prev k) B Bᵈ (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) (! (ap2-irr star (! (qq^=! k X= A Aᵈ)) refl ∙ ⟦weakenTy⟧=' k A Aᵈ X= Y=)))
⟦weakenTy⟧=' k nat _ X= Y= =
  NatStrNat (qq^ k X=) (! (qq^₁ k X=))
  ∙ ap NatStr (qq^₀ k X= ∙ ! Y=)
⟦weakenTy⟧=' k (id A u v) (Aᵈ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X= Y= =
  IdStrNat (qq^ k X=) (⟦⟧Ty-ft A ∙ ! (qq^₁ k X=))
  ∙ ap-irr-IdStr (⟦weakenTy⟧=' k A Aᵈ X= Y=) (⟦weakenTm⟧=' k u uᵈ X= Y=) (⟦weakenTm⟧=' k v vᵈ X= Y=)


⟦weakenTm⟧=' last (var last) tt X= refl = ! (ap ss (ap2-irr comp (ap ss (ap idC X=)) refl))
⟦weakenTm⟧=' (prev k) (var last) tt X= refl = ! (ss-comp {f₁ = id₁} ∙ ap ss (ap2-irr comp refl (ap idC (! qq₀)) ∙ id-left) ∙ ! (ss-comp {f₁ = comp₁ ∙ ss₁} ∙ ap ss (! assoc) ∙ ap ss (ap2-irr comp (! ss-qq ∙ ap idC (! qq₁)) refl) ∙ ap ss (id-right)))
⟦weakenTm⟧=' last (var (prev x)) (xᵈ , x₀ , tt) X= refl = ! (ap ss (ap2-irr comp (ap ss (ap2-irr comp (ap-irr (λ z p → ⟦ var x ⟧Tm z $ p) (ap ft X=)) (ap pp X=))) refl))
⟦weakenTm⟧=' (prev k) (var (prev x)) (xᵈ , x₀ , tt) X= refl = ! (ap ss (ap2-irr comp (ap-irr (λ z p → ⟦ var (weakenVar' k x) ⟧Tm z $ p) (ft-star ∙ qq^₀ k X=) ∙ ! (⟦weakenTm⟧=' k (var x) xᵈ X= refl)) refl {b' = pp₁ ∙ ft-star ∙ ! (ss₀ ∙ comp₀)}) ∙ ss-comp {f₁ = comp₁ ∙ ss₁} ∙ ap ss (! assoc) ∙ ap ss (ap2-irr comp (! ss-qq) refl) ∙ ap ss assoc ∙ ! (ss-comp {f₁ = comp₁ ∙ ss₁}∙ ap ss (! assoc) ∙ ap ss (ap2-irr comp (! ss-qq) refl) ∙ ap ss assoc ∙ ap ss (ap2-irr comp refl pp-qq)))

⟦weakenTm⟧=' k (uu i) tt X= refl =
  uuStrNat (qq^ k X=) (! (qq^₁ k X=))
  ∙ ap (uuStr i) (qq^₀ k X=)

⟦weakenTm⟧=' k (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X= refl =
  piStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=))
  ∙ ap-irr-piStr (⟦weakenTm⟧=' k a aᵈ X= refl)
                  (⟦weakenTm+⟧=' k b bᵈ X= (ElStr= ∙ ⟦⟧Tm₀ a) (! (ElStrNat (qq^ k (X= ∙ ap (ft^ k) (! (ElStr= ∙ ⟦⟧Tm₀ a)))) (⟦⟧Tm₀ a ∙ ! (ElStr= ∙ ⟦⟧Tm₀ a) ∙ ! (qq^₁ k (X= ∙ ap (ft^ k) (! (ElStr= ∙ ⟦⟧Tm₀ a)))))
                                                                  ∙ ap-irr2 (ElStr i) (ap2-irr starTm (qq^=p k X= (ElStr= ∙ ⟦⟧Tm₀ a)) refl {b = ⟦⟧Tm₀ a ∙ ! (ElStr= ∙ ⟦⟧Tm₀ a) ∙ ! (qq^₁ k (X= ∙ ap (ft^ k) (! (ElStr= ∙ ⟦⟧Tm₀ a))))}
                                                                                                                                           {b' = ⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)}
                                                                                       ∙ ⟦weakenTm⟧=' k a aᵈ X= refl))))
⟦weakenTm⟧=' k (lam A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) X= refl =
  lamStrNat (qq^ k X=) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (qq^₁ k X=))
  ∙ ap-irr-lamStr (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (! (⟦weakenTy⟧=' k A Aᵈ X= refl) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl))
                  (⟦weakenTm+⟧=' k u uᵈ X= (⟦⟧Ty-ft A) (! (⟦weakenTy⟧=' k A Aᵈ X= refl) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl))
⟦weakenTm⟧=' k (app A B f a) (Aᵈ , Bᵈ , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) X= refl =
  appStrNat (qq^ k X=) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (qq^₁ k X=))
  ∙ ap-irr-appStr (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (! (⟦weakenTy⟧=' k A Aᵈ X= refl) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl))
                  (⟦weakenTm⟧=' k f fᵈ X= refl)
                  (⟦weakenTm⟧=' k a aᵈ X= refl)

⟦weakenTm⟧=' k (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X= refl =
  sigStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=))
  ∙ ap-irr-sigStr (⟦weakenTm⟧=' k a aᵈ X= refl)
                  (⟦weakenTm+⟧=' k b bᵈ X= (ElStr= ∙ ⟦⟧Tm₀ a) (! (ElStrNat (qq^ k (X= ∙ ap (ft^ k) (! (ElStr= ∙ ⟦⟧Tm₀ a)))) (⟦⟧Tm₀ a ∙ ! (ElStr= ∙ ⟦⟧Tm₀ a) ∙ ! (qq^₁ k (X= ∙ ap (ft^ k) (! (ElStr= ∙ ⟦⟧Tm₀ a)))))
                                                                  ∙ ap-irr2 (ElStr i) (ap2-irr starTm (qq^=p k X= (ElStr= ∙ ⟦⟧Tm₀ a)) refl {b = ⟦⟧Tm₀ a ∙ ! (ElStr= ∙ ⟦⟧Tm₀ a) ∙ ! (qq^₁ k (X= ∙ ap (ft^ k) (! (ElStr= ∙ ⟦⟧Tm₀ a))))}
                                                                                                                                           {b' = ⟦⟧Tm₀ a ∙ ! (qq^₁ k X=)}
                                                                                       ∙ ⟦weakenTm⟧=' k a aᵈ X= refl))))
⟦weakenTm⟧=' k (pair A B a b) (Aᵈ , Bᵈ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X= refl =
  pairStrNat (qq^ k X=) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (qq^₁ k X=))
  ∙ ap-irr-pairStr (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (! (⟦weakenTy⟧=' k A Aᵈ X= refl) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl))
                   (⟦weakenTm⟧=' k a aᵈ X= refl)
                   (⟦weakenTm⟧=' k b bᵈ X= refl)
⟦weakenTm⟧=' k (pr1 A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) X= refl =
  pr1StrNat (qq^ k X=) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (qq^₁ k X=))
  ∙ ap-irr-pr1Str (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (! (⟦weakenTy⟧=' k A Aᵈ X= refl) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl))
                  (⟦weakenTm⟧=' k u uᵈ X= refl)
⟦weakenTm⟧=' k (pr2 A B u) (Aᵈ , Bᵈ , uᵈ , uₛ , u₁ , tt) X= refl =
  pr2StrNat (qq^ k X=) (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (qq^₁ k X=))
  ∙ ap-irr-pr2Str (⟦weakenTy+⟧=' k B Bᵈ X= (⟦⟧Ty-ft A) (! (⟦weakenTy⟧=' k A Aᵈ X= refl) ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl))
                  (⟦weakenTm⟧=' k u uᵈ X= refl)

⟦weakenTm⟧=' k (nat i) tt X= refl =
  natStrNat (qq^ k X=) (! (qq^₁ k X=))
  ∙ ap (natStr i) (qq^₀ k X=)
⟦weakenTm⟧=' k zero tt X= refl =
  zeroStrNat (qq^ k X=) (! (qq^₁ k X=))
  ∙ ap zeroStr (qq^₀ k X=)
⟦weakenTm⟧=' k (suc u) (uᵈ , uₛ , u₁ , tt) X= refl =
  sucStrNat (qq^ k X=) (⟦⟧Tm₀ u ∙ ! (qq^₁ k X=))
  ∙ ap-irr2 sucStr (⟦weakenTm⟧=' k u uᵈ X= refl)

⟦weakenTm⟧=' k (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X= refl =
  idStrNat (qq^ k X=) (⟦⟧Tm₀ a ∙ ! (qq^₁ k X=))
  ∙ ap-irr-idStr (⟦weakenTm⟧=' k a aᵈ X= refl)
                 (⟦weakenTm⟧=' k u uᵈ X= refl)
                 (⟦weakenTm⟧=' k v vᵈ X= refl)
⟦weakenTm⟧=' k (refl A u) (Aᵈ , uᵈ , uₛ , u₁ , tt) X= refl =
  reflStrNat (qq^ k X=) (⟦⟧Ty-ft A ∙ ! (qq^₁ k X=))
  ∙ ap-irr-reflStr (⟦weakenTy⟧=' k A Aᵈ X= refl)
                   (⟦weakenTm⟧=' k u uᵈ X= refl)


⟦weakenTy+⟧=' k A Aᵈ X= p Y= = ap2-irr star (ap2-irr qq (ap-irr (λ X → qq^ k {X = X}) (! p) {b = X=} {b' = X= ∙ ap (ft^ k) (! p)}) (⟦⟧Ty-ft A)) refl ∙ ⟦weakenTy⟧=' (prev k) A Aᵈ (X= ∙ ap (ft^ k) (! p)) Y=

⟦weakenTm+⟧=' k u uᵈ X= p Y= = ap ss (ap2-irr comp refl (ap2-irr qq (ap-irr (λ X → qq^ k {X = X}) (! p) {b = X=} {b' = X= ∙ ap (ft^ k) (! p)}) (⟦⟧Tm₀ u))) ∙ ⟦weakenTm⟧=' (prev k) u uᵈ (X= ∙ ap (ft^ k) (! p)) Y=

⟦weakenTm⟧₁' k u uᵈ X= refl refl = ap ∂₁ (! (⟦weakenTm⟧=' k u uᵈ X= refl)) ∙ ss₁ ∙  ap2-irr star (! (assoc {q = ! (pp₀ ∙ comp₁)})) refl ∙ star-comp (comp₁ ∙ pp₁) ∙ (ap2-irr star refl (ap2-irr star (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! (ap ft comp₁ ∙ ⟦⟧Tm₁-ft u))) refl ∙ star-id ∙ comp₁))


⟦weakenMor⟧ᵈ refl ◇ tt = tt
⟦weakenMor⟧ᵈ {X+ = X+} refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = (⟦weakenMor⟧ᵈ refl δ δᵈ , ⟦weakenTm⟧ᵈ' last u uᵈ refl refl , ⟦⟧Mor₁ (weakenMor δ) , (⟦weakenTm⟧₁' last u uᵈ refl refl refl ∙ ap2-irr star refl u₁ ∙ ! (star-comp δ₁) ∙ ! (ap2-irr star (⟦weakenMor⟧= refl δ δᵈ) refl)) , tt) 

⟦weakenMor⟧= refl ◇ tt = ! (ptmor-unique _ _ (comp₀ ∙ pp₀) (comp₁ ∙ pt-unique _))

⟦weakenMor⟧= refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = ap2-irr comp (ap2-irr qq (⟦weakenMor⟧= refl δ δᵈ) refl ∙ qq-comp (⟦⟧Mor₁ δ)) (! (⟦weakenTm⟧=' last u uᵈ refl refl)) ∙ assoc {p = ss₁ ∙ ! (qq₀ ∙ ap2-irr star (! (! (assoc {q = ! pp₀ ∙ ap ∂₀ (ap pp (! comp₁))}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! pp₁)) refl ∙ id-right)) (! (comp₁ ∙ u₁)))} {q = qq₁ ∙ ! qq₀} ∙ ap2-irr comp refl (ap2-irr comp (ap2-irr qq (! (! (assoc {q = ! pp₀ ∙ ap ∂₀ (ap pp (! comp₁))}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! pp₁)) refl ∙ id-right)) (! (comp₁ ∙ u₁))) refl ∙ ! ss-qq) ∙ ! assoc

⟦weakenMor+⟧ᵈ refl refl δ δᵈ p = (⟦weakenMor⟧ᵈ refl δ δᵈ , (tt , (⟦⟧Mor₁ (weakenMor δ) , ((ss₁ ∙ ap2-irr star (ap2-irr comp (ap pp (id₁ ∙ ! p)) (ap idC (! p ∙ ! pp₀)) ∙ id-left) (id₁ ∙ ! p) ∙ ! (star-comp {p = pp₁ ∙ ! (⟦⟧Mor₀ δ ∙ ap ft (! p))} (⟦⟧Mor₁ δ)) ∙ ap2-irr star (ap2-irr comp refl (ap pp p) ∙ ! (⟦weakenMor⟧= refl δ δᵈ)) refl) , tt))))


⟦weakenMor+⟧= refl refl δ δᵈ p = ap2-irr comp (ap2-irr qq (⟦weakenMor⟧= refl δ δᵈ) refl) refl {b' = ss₁ ∙ ! (qq₀ ∙ star-comp (⟦⟧Mor₁ δ) ∙ ap2-irr star (! (ap2-irr comp (ap pp id₁) (ap idC (! pp₀)) ∙ id-left)) (p ∙ ! id₁))} ∙ ap2-irr comp (qq-comp (⟦⟧Mor₁ δ)) refl ∙ (assoc {p = ss₁ ∙ ! (qq₀ ∙ ap2-irr star (! (ap2-irr comp (ap pp id₁) (ap idC (! pp₀)) ∙ id-left)) (p ∙ ! id₁))}) ∙ ap2-irr comp refl (ap2-irr comp (ap2-irr qq (! id-left ∙ ap2-irr comp (ap pp (! id₁)) (ap idC pp₀)) (p ∙ ! id₁)) refl ∙ (! ss-qq) ∙ ap idC (! (qq₀ ∙ p))) ∙ id-left

⟦⟧TyEq+ : {Γ : Ctx n} {X X' : Ob n} (r : respectsCtx X Γ) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A'))
          {Aᵈ : isDefined (⟦ A ⟧Ty X)} {A'ᵈ : isDefined (⟦ A' ⟧Ty X')} → X ≡ X' → ⟦ A ⟧Ty X $ Aᵈ ≡ ⟦ A' ⟧Ty X' $ A'ᵈ
⟦⟧TyEq+ r dA= refl = ⟦⟧TyEq r dA=

⟦⟧TmEq+ : {Γ : Ctx n} {X X' : Ob n} (r : respectsCtx X Γ) {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A))
          {uᵈ : isDefined (⟦ u ⟧Tm X)} {u'ᵈ : isDefined (⟦ u' ⟧Tm X')} → X ≡ X' → ⟦ u ⟧Tm X $ uᵈ ≡ ⟦ u' ⟧Tm X' $ u'ᵈ
⟦⟧TmEq+ r du= refl = ⟦⟧TmEq r du=

⟦⟧TyEq r (TySymm dA=) = ! (⟦⟧TyEq r dA=)
⟦⟧TyEq r (TyTran dB dA= dB=) = ⟦⟧TyEq r dA= {A'ᵈ = ⟦⟧Tyᵈ r dB} ∙ ⟦⟧TyEq r dB=

⟦⟧TyEq r UUCong = refl
⟦⟧TyEq r (ElCong dv=) = ap-irr2 (ElStr _) (⟦⟧TmEq r dv=)
⟦⟧TyEq r {A = sig A B} (SigCong dA dA= dB=) = ap SigStr (⟦⟧TyEq+ (respectsCtxExt r A) dB= (⟦⟧TyEq r dA=))
⟦⟧TyEq r {A = pi A B} (PiCong dA dA= dB=) = ap PiStr (⟦⟧TyEq+ (respectsCtxExt r A) dB= (⟦⟧TyEq r dA=))
⟦⟧TyEq r NatCong = refl
⟦⟧TyEq r (IdCong dA du dv) = ap-irr-IdStr (⟦⟧TyEq r dA) (⟦⟧TmEq r du) (⟦⟧TmEq r dv)

⟦⟧TyEq r ElUU= = eluuStr
⟦⟧TyEq r (ElPi= da db) = elpiStr
⟦⟧TyEq r (ElSig= da db) = elsigStr
⟦⟧TyEq r ElNat= = elnatStr
⟦⟧TyEq r (ElId= da du dv) = elidStr

⟦⟧TmEq r (VarLastCong dA) = refl
⟦⟧TmEq r (VarPrevCong {k = k} {k' = k'} dA dx) = ap ss (ap2-irr comp (⟦⟧TmEq (fst r) dx) refl)
⟦⟧TmEq r (TmSymm du=) = ! (⟦⟧TmEq r du=)
⟦⟧TmEq r (TmTran dv du= du'=) = ⟦⟧TmEq r du= {u'ᵈ = ⟦⟧Tmᵈ r dv} ∙ ⟦⟧TmEq r du'=
⟦⟧TmEq r (ConvEq dA' du= dA=) = ⟦⟧TmEq r du=

⟦⟧TmEq r UUUUCong = refl
⟦⟧TmEq r {u = pi i a b} (PiUUCong da da= db=) {uᵈ = (aᵈ , aₛ , a₁ , _)} = ap-irr-piStr (⟦⟧TmEq r da=) (⟦⟧TmEq+ (respectsCtxExt r (el i a) {Aᵈ = _ , aₛ , a₁ , tt}) db= (ap-irr2 (ElStr _) (⟦⟧TmEq r da=)) )
⟦⟧TmEq r {u = lam A B u} (LamCong dA dA= dB= du=) = ap-irr-lamStr (⟦⟧TyEq+ (respectsCtxExt r A) dB= (⟦⟧TyEq r dA=)) (⟦⟧TmEq+ (respectsCtxExt r A) du= (⟦⟧TyEq r dA=))
⟦⟧TmEq r {u = app A B f a} (AppCong dA dA= dB= df= da=) = ap-irr-appStr (⟦⟧TyEq+ (respectsCtxExt r A) dB= (⟦⟧TyEq r dA=)) (⟦⟧TmEq r df=) (⟦⟧TmEq r da=)

⟦⟧TmEq r {u = sig i a b} (SigUUCong da da= db=) {uᵈ = (aᵈ , aₛ , a₁ , bᵈ , _)} {u'ᵈ = (a'ᵈ , _ , _ , b'ᵈ , _)} = ap-irr-sigStr (⟦⟧TmEq r da=) (⟦⟧TmEq+ (respectsCtxExt r (el i a) {Aᵈ = aᵈ , aₛ , a₁ , tt}) db= (ap-irr2 (ElStr i) (⟦⟧TmEq r da=)))
⟦⟧TmEq r {u = pair A B a b} (PairCong dA dA= dB= da= db=) = ap-irr-pairStr (⟦⟧TyEq+ (respectsCtxExt r A) dB= (⟦⟧TyEq r dA=)) (⟦⟧TmEq r da=) (⟦⟧TmEq r db=)
⟦⟧TmEq r {u = pr1 A B u} (Pr1Cong dA dA= dB= du=) = ap-irr-pr1Str (⟦⟧TyEq+ (respectsCtxExt r A) dB= (⟦⟧TyEq r dA=)) (⟦⟧TmEq r du=)
⟦⟧TmEq r {u = pr2 A B u} (Pr2Cong dA dA= dB= du=) = ap-irr-pr2Str (⟦⟧TyEq+ (respectsCtxExt r A) dB= (⟦⟧TyEq r dA=)) (⟦⟧TmEq r du=)

⟦⟧TmEq r NatUUCong = refl
⟦⟧TmEq r ZeroCong = refl
⟦⟧TmEq r (SucCong du) = ap-irr2 sucStr (⟦⟧TmEq r du)

⟦⟧TmEq r (IdUUCong da= du= dv=) = ap-irr-idStr (⟦⟧TmEq r da=) (⟦⟧TmEq r du=) (⟦⟧TmEq r dv=)
⟦⟧TmEq r (ReflCong dA= du=) = ap-irr-reflStr (⟦⟧TyEq r dA=) (⟦⟧TmEq r du=)

⟦⟧TmEq r {u = app A B (lam A B u) a} (BetaPi dA dB du da) = betaPiStr ∙ ! (⟦subst⟧Tm= (⟦⟧Ty-ft A) u _ a (⟦⟧Tmᵈ r da) (⟦⟧Tm₁ r da))
⟦⟧TmEq r (BetaSig1 dA dB da db) = betaSig1Str
⟦⟧TmEq r (BetaSig2 dA dB da db) = betaSig2Str

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
⟦tsubst⟧Tmᵈ (var (prev x)) (xᵈ , _) (δ , u) (δᵈ , _) = ⟦tsubst⟧Tmᵈ (var x) xᵈ δ δᵈ

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
  (⟦tsubst⟧Tm₁ b bᵈ δ δᵈ b₁ ∙ starstar _ _ (⟦⟧Tmₛ a) _ {a₀ = ⟦⟧Tm₀ a ∙ ! (⟦⟧Mor₁ δ)} {p = ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ)} ∙ ap2-irr star (⟦tsubst⟧Tm= a aᵈ δ δᵈ) (⟦tsubst⟧Ty+= B Bᵈ δ δᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))) , tt)
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

⟦tsubst⟧Tm= (var ()) _ ◇ δᵈ
⟦tsubst⟧Tm= (var last) tt (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = ! (! (ss-of-section (⟦ u ⟧Tm _ $ uᵈ) (⟦⟧Tmₛ u)) ∙ ss-comp {f₁ = u₁} ∙ ap ss ((! id-right ∙ ap2-irr comp (ap idC (comp₁ ∙ qq₁) ∙ ss-qq) refl) ∙ assoc {q = ss₁ ∙ ! qq₀}) ∙ ! (ss-comp {f₁ = comp₁ ∙ ss₁}))
⟦tsubst⟧Tm= (var (prev x)) (xᵈ , _) (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = ss-comp {f₁ = comp₁ ∙ ss₁} ∙ ap ss (! (assoc {q = ss₁ ∙ ! qq₀}) ∙ ap2-irr comp (! ss-qq) refl ∙ assoc ∙ ap2-irr comp refl (! assoc ∙ ap2-irr comp pp-qq refl ∙ assoc {p = u₁ ∙ ! pp₀} {q = pp₁ ∙ ft-star} ∙ ap2-irr comp refl (ap2-irr comp (ap pp (! u₁)) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! (⟦⟧Mor₀ δ))) ∙ id-left)) ∙ ⟦tsubst⟧Tm= (var x) xᵈ δ δᵈ

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

⟦tsubst⟧Tm= (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) δ δᵈ =
  idStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (⟦⟧Tm₀ a ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr-idStr (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
                 (⟦tsubst⟧Tm= u uᵈ δ δᵈ)
                 (⟦tsubst⟧Tm= v vᵈ δ δᵈ)
⟦tsubst⟧Tm= (refl A u) (Aᵈ , uᵈ , uₛ , u₁ , tt) δ δᵈ =
  reflStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) (⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ))
  ∙ ap-irr-reflStr (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                  (⟦tsubst⟧Tm= u uᵈ δ δᵈ)





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

{- Any context respects its own interpretation -}

respects⟦⟧Ctx : {Γ : Ctx n} {Γᵈ : isDefined (⟦ Γ ⟧Ctx)} → respectsCtx (⟦ Γ ⟧Ctx $ Γᵈ) Γ
respects⟦⟧Ctx {Γ = ◇} = tt
respects⟦⟧Ctx {Γ = Γ , A} {Γᵈ = Γᵈ , Aᵈ , tt} rewrite ⟦⟧Ty-ft A {Aᵈ} = (respects⟦⟧Ctx , Aᵈ , refl)

{- Totality of the interpretation function on derivable contexts -}

⟦⟧Ctxᵈ : {Γ : Ctx n} (dΓ : ⊢ Γ) → isDefined (⟦ Γ ⟧Ctx)
⟦⟧Ctxᵈ {Γ = ◇} tt = tt
⟦⟧Ctxᵈ {Γ = Γ , A} (dΓ , dA) = let Γᵈ = ⟦⟧Ctxᵈ dΓ in (Γᵈ , ⟦⟧Tyᵈ respects⟦⟧Ctx dA , tt)

{- Interpretation of context equalities -}

⟦⟧CtxEq : {Γ Γ' : Ctx n} (dΓ= : ⊢ Γ == Γ') {Γᵈ : isDefined (⟦ Γ ⟧Ctx)} {Γ'ᵈ : isDefined (⟦ Γ' ⟧Ctx)}
        → ⟦ Γ ⟧Ctx $ Γᵈ ≡ ⟦ Γ' ⟧Ctx $ Γ'ᵈ
⟦⟧CtxEq {Γ = ◇} {◇} _ = refl
⟦⟧CtxEq {Γ = Γ , A} {Γ' , A'} (dΓ= , _ , _ , dA= , _) {Γᵈ = Γᵈ , Aᵈ , tt} {Γ'ᵈ = Γ'ᵈ , A'ᵈ , tt}
  rewrite ! (⟦⟧CtxEq dΓ= {Γᵈ} {Γ'ᵈ}) | ⟦⟧TyEq respects⟦⟧Ctx dA= {Aᵈ = Aᵈ} {A'ᵈ = A'ᵈ} = refl

{- Interpretation of morphism equalities -}

⟦⟧MorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} {X : Ob n} {Y : Ob m} (r : respectsCtx X Γ) (dδ= : Γ ⊢ δ == δ' ∷> Δ) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} {δ'ᵈ : isDefined (⟦ δ' ⟧Mor X Y)}
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

