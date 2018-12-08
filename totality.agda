{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import syntx
open import contextualcat
open import rules

module _ (sC : StructuredCCat) where

open StructuredCCat sC renaming (ccat to C)
open CCat C renaming (Mor to MorC; id to idC)
open import partialinterpretation sC

{- Predicate saying whether an object "respects" a context in the sense that the types in Γ correspond to their interpretation in X.
   We cannot use (X ≡ ⟦ Γ ⟧) instead because it fails the termination checker somehow. -}

respectsCtx : (X : Ob n) (Γ : Ctx n) → Prop
respectsCtx {zero} X ◇ = Unit
respectsCtx {suc n} X (Γ , A) = respectsCtx (ft X) Γ × Σ (isDefined (⟦ A ⟧Ty (ft X))) (λ Aᵈ → ⟦ A ⟧Ty (ft X) $ Aᵈ ≡ X)


{- Totality of the partial interpretation functions -}

⟦⟧Tyᵈ  : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) → isDefined (⟦ A ⟧Ty X)
⟦⟧Tmᵈ  : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → isDefined (⟦ u ⟧Tm X)
⟦⟧Morᵈ : {Γ : Ctx n} {Δ : Ctx m} {X : Ob n} {Y : Ob m} (r : respectsCtx X Γ) (r' : respectsCtx Y Δ) {δ : Mor n m} (dδ : Γ ⊢ δ ∷> Δ) → isDefined (⟦ δ ⟧Mor X Y)


{- Interpretation of definitional equalities -}

⟦⟧TyEq : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A')) (Aᵈ : isDefined (⟦ A ⟧Ty X)) (A'ᵈ : isDefined (⟦ A' ⟧Ty X))
        → ⟦ A ⟧Ty X $ Aᵈ ≡ ⟦ A' ⟧Ty X $ A'ᵈ
⟦⟧TmEq : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A)) (uᵈ : isDefined (⟦ u ⟧Tm X)) (u'ᵈ : isDefined (⟦ u' ⟧Tm X))
        → ⟦ u ⟧Tm X $ uᵈ ≡ ⟦ u' ⟧Tm X $ u'ᵈ



{- Various lemmas saying that the interpretation functions are well-behaved -}

⟦⟧Tm₁ : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} {A : TyExpr n} {Aᵈ : isDefined (⟦ A ⟧Ty X)} (du : Derivable (Γ ⊢ u :> A)) → ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ ⟦ A ⟧Ty X $ Aᵈ

⟦idMor⟧ᵈ : {X Y : Ob n} → Y ≡ X → isDefined (⟦ idMor n ⟧Mor X Y)
⟦idMor⟧= : {X Y : Ob n} (p : Y ≡ X) → ⟦ idMor n ⟧Mor X Y $ ⟦idMor⟧ᵈ p ≡ idC X


cong⟦⟧Ty : {X Y : Ob n} {A : TyExpr n} → X ≡ Y → isDefined (⟦ A ⟧Ty X) → isDefined (⟦ A ⟧Ty Y)
cong⟦⟧Ty refl Aᵈ = Aᵈ

cong⟦⟧Tm : {X Y : Ob n} {u : TmExpr n} → X ≡ Y → isDefined (⟦ u ⟧Tm X) → isDefined (⟦ u ⟧Tm Y)
cong⟦⟧Tm refl uᵈ = uᵈ

-- ft^ : Ob (n + m) → Ob m
-- ft^ {n = zero} X = X
-- ft^ {n = suc n} X = ft^ {n = n} (ft X)

-- weakenTyCC : {n m : ℕ} (X+ : Ob (suc m)) (X : Ob (n + m)) (X= : ft X+ ≡ ft^ {n = n} X) → Ob (suc (n + m))
-- weakenTyCC {zero} X+ X X= = X+
-- weakenTyCC {suc n} {m} X+ X X= = {!weakenTyCC {n = n} {m = suc m} (star (pp ?) X+ ?) X ?!}


⟦weakenTy⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (X= : ft X+ ≡ ft^ k X) (A : TyExpr n)
            → isDefined (⟦ A ⟧Ty X)
            → isDefined (⟦ weakenTy' k A ⟧Ty (star^ k X+ X X=))


⟦weakenTy⟧=' : (k : Fin (suc n)) {X+ : Ob (suc(n -F' k))} {X : Ob n} (X= : ft X+ ≡ ft^ k X) (A : TyExpr n)
             → (Aᵈ : isDefined (⟦ A ⟧Ty X))
             → ⟦ weakenTy' k A ⟧Ty (star^ k X+ X X=) $ ⟦weakenTy⟧ᵈ' k X= A Aᵈ ≡ star (qq^ k X=) (⟦ A ⟧Ty X $ Aᵈ) (qq^₁ k X= ∙ ! (⟦⟧Ty-ft A))

⟦weakenTm⟧ᵈ' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (X= : ft X+ ≡ ft^ k X) (u : TmExpr n)
            → isDefined (⟦ u ⟧Tm X)
            → isDefined (⟦ weakenTm' k u ⟧Tm ((star^ k X+ X X=)))


⟦weakenTm⟧=' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (X= : ft X+ ≡ ft^ k X) (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → ⟦ weakenTm' k u ⟧Tm (star^ k X+ X X=) $ ⟦weakenTm⟧ᵈ' k X= u uᵈ ≡ ss (comp (⟦ u ⟧Tm X $ uᵈ) (qq^ k X=) (qq^₁ k X= ∙ ! (⟦⟧Tm₀ u)))
            
⟦weakenTm⟧₁' : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (X= : ft X+ ≡ ft^ k X) (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → ∂₁ (⟦ weakenTm' k u ⟧Tm (star^ k X+ X X=) $ ⟦weakenTm⟧ᵈ' k X= u uᵈ) ≡ star (qq^ k X=) (∂₁ (⟦ u ⟧Tm X $ uᵈ)) (qq^₁ k X= ∙ ! (⟦⟧Tm₁-ft u))
            

⟦weakenTy⟧ᵈ : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) (A : TyExpr n)
            → isDefined (⟦ A ⟧Ty X)
            → isDefined (⟦ weakenTy A ⟧Ty X+)

⟦weakenTy⟧= : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) (A : TyExpr n)
            → (Aᵈ : isDefined (⟦ A ⟧Ty X))
            → ⟦ weakenTy A ⟧Ty X+ $ ⟦weakenTy⟧ᵈ X= A Aᵈ ≡ star (pp X+) (⟦ A ⟧Ty X $ Aᵈ) (pp₁ ∙ X= ∙ ! (⟦⟧Ty-ft A))

⟦weakenTm⟧ᵈ : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) (u : TmExpr n)
            → isDefined (⟦ u ⟧Tm X)
            → isDefined (⟦ weakenTm u ⟧Tm X+)

⟦weakenTm⟧= : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → ⟦ weakenTm u ⟧Tm X+ $ ⟦weakenTm⟧ᵈ X= u uᵈ ≡ ss (comp (⟦ u ⟧Tm X $ uᵈ) (pp X+) (pp₁ ∙ X= ∙ ! (⟦⟧Tm₀ u)))


⟦weakenTm⟧₁ : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) (u : TmExpr n)
             → (uᵈ : isDefined (⟦ u ⟧Tm X))
             → ∂₁ (⟦ weakenTm u ⟧Tm X+ $ ⟦weakenTm⟧ᵈ X= u uᵈ) ≡ star (pp X+) (∂₁ (⟦ u ⟧Tm X $ uᵈ)) (pp₁ ∙ X= ∙ ! (⟦⟧Tm₁-ft u))
             

⟦weakenMor⟧ᵈ : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y : Ob m} (δ : Mor n m)
           → isDefined (⟦ δ ⟧Mor X Y)
           → isDefined (⟦ weakenMor δ ⟧Mor X+ Y)
           
⟦weakenMor⟧= : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y : Ob m} (δ : Mor n m)
           → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
           → ⟦ weakenMor δ ⟧Mor X+ Y $ ⟦weakenMor⟧ᵈ X= δ δᵈ ≡ comp (⟦ δ ⟧Mor X Y $ δᵈ) (pp X+) (pp₁ ∙ ! (⟦⟧Mor₀ δ ∙ ! X=))

-- ⟦ weakenMor δ ⟧Mor (star Y+  Y $ ⟦weakenMor⟧ᵈ X= Y= δ δᵈ ≡ comp (pp Y+) (qq (⟦ δ ⟧Mor X Y $ δᵈ) Y+ (⟦⟧Mor₁ δ ∙ ! Y=)) (qq₁ ∙ ! pp₀)

⟦weakenMorVar⟧ᵈ : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y+ : Ob (suc m)} {Y : Ob m} (Y= : ft Y+ ≡ Y) (δ : Mor n m)
           → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
           → (_ : X+ ≡ star (⟦ δ ⟧Mor X Y $ δᵈ) Y+ (⟦⟧Mor₁ δ ∙ ! Y=))
           → isDefined (⟦ weakenMor δ , var last ⟧Mor X+ Y+)
⟦weakenMorVar⟧= : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y+ : Ob (suc m)} {Y : Ob m} (Y= : ft Y+ ≡ Y) (δ : Mor n m)          
           → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
           → (p : X+ ≡ star (⟦ δ ⟧Mor X Y $ δᵈ) Y+ (⟦⟧Mor₁ δ ∙ ! Y=))
           → ⟦ weakenMor δ , var last ⟧Mor X+ Y+ $ ⟦weakenMorVar⟧ᵈ X= Y= δ δᵈ p ≡ qq (⟦ δ ⟧Mor X Y $ δᵈ) Y+ (⟦⟧Mor₁ δ ∙ ! Y=)


{- Interpretation of total substitutions -}

⟦tsubst⟧Tyᵈ : {X : Ob n} {Y : Ob m} (A : TyExpr m) {δ : Mor n m}
            → isDefined (⟦ A ⟧Ty Y)
            → isDefined (⟦ δ ⟧Mor X Y)
            → isDefined (⟦ A [ δ ]Ty ⟧Ty X)

⟦tsubst⟧Ty= : {X : Ob n} {Y : Ob m} (A : TyExpr m)
              (Aᵈ : isDefined (⟦ A ⟧Ty Y))
              (δ : Mor n m)
              (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            → ⟦ A [ δ ]Ty ⟧Ty X $ ⟦tsubst⟧Tyᵈ A Aᵈ δᵈ
              ≡ star (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y $ Aᵈ) (⟦⟧Mor₁ δ ∙ ! (⟦⟧Ty-ft A))

⟦tsubst⟧Tmᵈ : {X : Ob n} {Y : Ob m} (u : TmExpr m) {δ : Mor n m}
            → isDefined (⟦ u ⟧Tm Y)
            → isDefined (⟦ δ ⟧Mor X Y)
            → isDefined (⟦ u [ δ ]Tm ⟧Tm X)

⟦tsubst⟧Tm= : {X : Ob n} {Y : Ob m} (u : TmExpr m)
            (uᵈ : isDefined (⟦ u ⟧Tm Y))
            (δ : Mor n m)
            (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            → ⟦ u [ δ ]Tm ⟧Tm X $ ⟦tsubst⟧Tmᵈ u uᵈ δᵈ
              ≡ ss (comp (⟦ u ⟧Tm Y $ uᵈ) (⟦ δ ⟧Mor X Y $ δᵈ) (⟦⟧Mor₁ δ ∙ ! (⟦⟧Tm₀ u)))

⟦tsubst⟧Tm₁ : {X : Ob n} {Y : Ob m} (u : TmExpr m)
            (uᵈ : isDefined (⟦ u ⟧Tm Y))
            (δ : Mor n m)
            (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            → ∂₁ (⟦ u [ δ ]Tm ⟧Tm X $ ⟦tsubst⟧Tmᵈ u uᵈ δᵈ)
              ≡ star (⟦ δ ⟧Mor X Y $ δᵈ) (∂₁ (⟦ u ⟧Tm Y $ uᵈ)) (⟦⟧Mor₁ δ ∙ ! (⟦⟧Tm₁-ft u))


{- Interpretation of simple substitutions -}

⟦subst⟧Tyᵈ : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (B : TyExpr (suc n)) {u : TmExpr n}
            → isDefined (⟦ B ⟧Ty X)
            → (uᵈ : isDefined (⟦ u ⟧Tm Y))
            → (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → isDefined (⟦ substTy B u ⟧Ty Y)

⟦subst⟧Ty= : {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) (B : TyExpr (suc n)) {u : TmExpr n}
             (Bᵈ : isDefined (⟦ B ⟧Ty X))
             (uᵈ : isDefined (⟦ u ⟧Tm Y))
             (q : ∂₁ (⟦ u ⟧Tm Y $ uᵈ) ≡ X)
            → ⟦ substTy B u ⟧Ty Y $ ⟦subst⟧Tyᵈ p B Bᵈ uᵈ q ≡ star (⟦ u ⟧Tm Y $ uᵈ) (⟦ B ⟧Ty X $ Bᵈ) (q ∙ ! (⟦⟧Ty-ft B))

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
⟦⟧Tyᵈ r {A = pi A B} (Pi dA dB) = (⟦⟧Tyᵈ r dA , ⟦⟧Tyᵈ (respectsCtxExt r A) dB , tt)
⟦⟧Tyᵈ r {A = el i v} (El dv) = (⟦⟧Tmᵈ r dv , ⟦⟧Tmₛ v , (⟦⟧Tm₁ r v dv ∙ ap (UUStr i) (! (⟦⟧Tm₀ v))) , tt)

⟦⟧Tmᵈ r (VarLast dA) = tt
⟦⟧Tmᵈ r {u = var (prev x)} (VarPrev dA dx) = (⟦⟧Tmᵈ (fst r) dx , ⟦⟧Tm₀ (var x) , tt)
⟦⟧Tmᵈ r (Conv dA du dA=) = ⟦⟧Tmᵈ r du
⟦⟧Tmᵈ r {u = lam A B u} (Lam dA dB du) =
  (⟦⟧Tyᵈ r dA ,
   ⟦⟧Tmᵈ (respectsCtxExt r A) du ,
   ⟦⟧Tmₛ u , tt)
⟦⟧Tmᵈ r {u = app A B f a} (App dA dB df da) =
  (⟦⟧Tyᵈ r dA ,
   ⟦⟧Tyᵈ (respectsCtxExt r A) dB ,
   ⟦⟧Tmᵈ r df ,
   ⟦⟧Tmᵈ r da ,
   ⟦⟧Tmₛ f ,
   ⟦⟧Tm₁ r f df ,
   ⟦⟧Tmₛ a ,
   (⟦⟧Tm₁ r a da ∙ ! (⟦⟧Ty-ft B)) , tt)

⟦⟧Morᵈ {Δ = ◇} r r' {◇} tt = tt
⟦⟧Morᵈ {Δ = Δ , B} r (r' , Bᵈ , B=) {δ , u} (dδ , du) =
  let δᵈ = ⟦⟧Morᵈ r r' dδ in
  (δᵈ ,
   ⟦⟧Tmᵈ r du ,
   ⟦⟧Mor₁ δ ,
   (⟦⟧Tm₁ r u {Aᵈ = ⟦tsubst⟧Tyᵈ B Bᵈ δᵈ} du ∙ ⟦tsubst⟧Ty= B Bᵈ δ δᵈ ∙ ap2-irr star refl B=) , tt)

⟦⟧Tm₁ r (var last) (VarLast {A = A} dA) = ss₁ ∙ ap2-irr star (ap2-irr comp (ap pp id₁) (ap idC (! pp₀)) ∙ id-left ∙ refl) id₁ {b' = pp₁} ∙ ! (⟦weakenTy⟧= refl A (fst (snd r)) ∙ ap2-irr star refl (snd (snd r)))
⟦⟧Tm₁ r (var (prev k)) (VarPrev {A = A} dA dk) = ss₁ ∙ ap2-irr star (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ (var k) ∙ ap idC (⟦⟧Tm₀ (var k) ∙ ! pp₁)) refl ∙ id-right) (comp₁ ∙ ⟦⟧Tm₁ (fst r) (var k) dk) ∙ ! (⟦weakenTy⟧= refl A (⟦⟧Tyᵈ (fst r) dA))
⟦⟧Tm₁ r u (Conv dA du dA=) = ⟦⟧Tm₁ r u du ∙ ⟦⟧TyEq r dA= (⟦⟧Tyᵈ r dA) _
⟦⟧Tm₁ r (lam A B u) (Lam dA dB du) = lamStr₁ ∙ ap PiStr (⟦⟧Tm₁ (respectsCtxExt r A) u du)
⟦⟧Tm₁ {X = X} r (app A B f a) (App dA dB df da) = appStr₁ ∙ ! (⟦tsubst⟧Ty= B (⟦⟧Tyᵈ (respectsCtxExt r A) dB) _ (⟦idMor⟧ᵈ {Y = ft (⟦ A ⟧Ty X $ ⟦⟧Tyᵈ r dA)} (⟦⟧Ty-ft A) , ⟦⟧Tmᵈ r da , ⟦⟧Mor₁ (idMor _) , (⟦⟧Tm₁ r  a da ∙ ! (ap2-irr star (⟦idMor⟧= (⟦⟧Ty-ft A) ∙ ap idC (! (⟦⟧Ty-ft A))) refl ∙ star-id)) , tt) ∙ ap2-irr star (⟦idMor+⟧= (⟦⟧Ty-ft A) a (⟦⟧Tmᵈ r da) (⟦⟧Tm₁ r a da)) refl)

⟦idMor⟧ᵈ {zero} refl = tt
⟦idMor⟧ᵈ {suc n} {Y = Y} refl = ⟦weakenMorVar⟧ᵈ refl refl (idMor n) (⟦idMor⟧ᵈ {n = n} refl) (! (ap2-irr star (⟦idMor⟧= refl) refl ∙ star-id))

-- (⟦weakenMor⟧ᵈ refl refl (idMor n) (⟦idMor⟧ᵈ {Y = ft Y} refl) , tt , ⟦⟧Mor₁ (weakenMor (idMor n)) , (ss₁ ∙ ap2-irr star (! (⟦weakenMor⟧= refl refl (idMor n) (⟦idMor⟧ᵈ {Y = ft Y} refl) ∙ ap2-irr comp (ap pp (! id₁)) (ap2-irr qq (⟦idMor⟧= refl) refl ∙ qq-id))) id₁) , tt)

⟦idMor⟧= {zero} refl = ! (ptmor-unique _ (idC _) id₀ (id₁ ∙ pt-unique _))
⟦idMor⟧= {suc n} {Y = Y} refl = ⟦weakenMorVar⟧= {X = ft Y} refl {Y+ = Y} {Y = ft Y} refl (idMor n) (⟦idMor⟧ᵈ{n = n} refl) (! (ap2-irr star (⟦idMor⟧= refl) refl ∙ star-id)) ∙ ap2-irr qq (⟦idMor⟧= refl) refl ∙ qq-id

--⟦weakenMorVar⟧= refl (idMor n) (⟦idMor⟧ᵈ {n = n} refl) ∙ ap2-irr qq (⟦idMor⟧= refl) refl ∙ qq-id

-- lemmaMor : (δ : Mor n m) → weakenMor δ ≡ δ [ weakenMor (idMor n) ]Mor
-- lemmaMor δ = ap weakenMor (! ([idMor]Mor δ)) ∙ weaken[]Mor δ (idMor _) last

-- lemmaTm : (u : TmExpr n) → weakenTm u ≡ u [ weakenMor (idMor n) ]Tm
-- lemmaTm u = ap weakenTm (! ([idMor]Tm u)) ∙ weaken[]Tm u (idMor _) last

qq^=! : (k : Fin (suc n)) {X : Ob n} {X+ : Ob (suc (n -F' k))} (X= : ft X+ ≡ ft^ k X) (A : TyExpr n) (Aᵈ : isDefined (⟦ A ⟧Ty X)) → qq^ k X= ≡ qq^ k (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A {Aᵈ = Aᵈ})))
qq^=! k X= A Aᵈ = ap-irr (λ X → qq^ k {X = X}) (! (⟦⟧Ty-ft A)) {b = X=} {b' = X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A)) }

qq^= : (k : Fin (suc n)) {X : Ob n} {X+ : Ob (suc (n -F' k))} (X= : ft X+ ≡ ft^ k X) (A : TyExpr n) (Aᵈ : isDefined (⟦ A ⟧Ty X)) → qq^ k (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A {Aᵈ = Aᵈ}))) ≡ qq^ k X=
qq^= k X= A Aᵈ = ap-irr (λ X → qq^ k {X = X}) (⟦⟧Ty-ft A) {b = X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A)) } {b' = X=}

⟦weakenTy⟧ᵈ' k {X+ = X+} {X = X} X= (pi A B) (Aᵈ , Bᵈ , tt)  = (⟦weakenTy⟧ᵈ' k X= A Aᵈ , cong⟦⟧Ty {A = weakenTy' (prev k) B} (! (⟦weakenTy⟧=' k X= A Aᵈ ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl)) (⟦weakenTy⟧ᵈ' (prev k) (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) B Bᵈ)  , tt)
⟦weakenTy⟧ᵈ' k X= (uu i) Aᵈ = tt
⟦weakenTy⟧ᵈ' k X= (el i v) (vᵈ , vₛ , v₁ , tt) = (⟦weakenTm⟧ᵈ' k X= v vᵈ , ⟦⟧Tmₛ (weakenTm' k v) , (⟦weakenTm⟧₁' k X= v vᵈ ∙ (ap2-irr star refl v₁ ∙ UUStrNat (qq^ k X=) {p = ⟦⟧Tm₀ v ∙ ! (qq^₁ k X=)} ∙ ap (UUStr i) (qq^₀ k X= ∙ ! (⟦⟧Tm₀ (weakenTm' k v))))) , tt)

⟦weakenTy⟧=' k X= (pi A B) (Aᵈ , Bᵈ , tt) = ! (PiStrNat (qq^ k X=) {p = ! (qq^₁ k X= ∙ ! (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A))} ∙ ap PiStr (! (ap-irr (λ z p → ⟦ weakenTy' (prev k) B ⟧Ty z $ p) (⟦weakenTy⟧=' k X= A Aᵈ ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl) ∙ ⟦weakenTy⟧=' (prev k) (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) B Bᵈ ∙ ap2-irr star (ap2-irr qq (qq^= k X= A Aᵈ) (! (⟦⟧Ty-ft B))) refl)))
⟦weakenTy⟧=' k X= (uu i) uuᵈ = ! (UUStrNat (qq^ k X=) {p = ! (qq^₁ k X=)} ∙ ap (UUStr i) (qq^₀ k X=))
⟦weakenTy⟧=' k X= (el i v) (vᵈ , vₛ , v₁ , tt) = ! (ElStrNat (qq^ k X=) {p = ⟦⟧Tm₀ v ∙ ! (qq^₁ k X=)} ∙ ap-irr2 (ElStr i) (! (⟦weakenTm⟧=' k X= v vᵈ)))

⟦weakenTm⟧ᵈ' last X= (var last) tt = (tt , (ss₀ ∙ id₀) , tt)
⟦weakenTm⟧ᵈ' (prev k) X= (var last) tt = tt
⟦weakenTm⟧ᵈ' last X= (var (prev x)) (xᵈ , x₀ , tt) = (cong⟦⟧Tm {u = var x} (ap ft (! X=)) xᵈ , (⟦⟧Tm₀ (var x)) , tt) , ((ss₀ ∙ comp₀ ∙ pp₀) , tt)
⟦weakenTm⟧ᵈ' (prev k) X= (var (prev x)) (xᵈ , x₀ , tt) = (cong⟦⟧Tm {u = weakenTm' k (var x)} (! (ft-star ∙ qq^₀ k X=)) (⟦weakenTm⟧ᵈ' k X= (var x) xᵈ) , ⟦⟧Tm₀ (weakenTm' k (var x)) , tt)
⟦weakenTm⟧ᵈ' k X= (lam A B u) (Aᵈ , uᵈ , uₛ , tt) = (⟦weakenTy⟧ᵈ' k X= A Aᵈ , cong⟦⟧Tm {u = weakenTm' (prev k) u} ((! (⟦weakenTy⟧=' k X= A Aᵈ ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl))) (⟦weakenTm⟧ᵈ' (prev k) (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) u uᵈ) , ⟦⟧Tmₛ (weakenTm' (prev k) u) , tt)
⟦weakenTm⟧ᵈ' k X= (app A B f a) (Aᵈ , Bᵈ ,  fᵈ , aᵈ , fₛ , f₁ , aₛ , a₁ , tt) = (⟦weakenTy⟧ᵈ' k X= A Aᵈ , cong⟦⟧Ty {A = weakenTy' (prev k) B} (! (⟦weakenTy⟧=' k X= A Aᵈ ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl)) (⟦weakenTy⟧ᵈ' (prev k) (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) B Bᵈ) , ⟦weakenTm⟧ᵈ' k X= f fᵈ , ⟦weakenTm⟧ᵈ' k X= a aᵈ , ⟦⟧Tmₛ (weakenTm' k f) , (⟦weakenTm⟧₁' k X= f fᵈ ∙ ap2-irr star refl f₁ ∙ (PiStrNat (qq^ k X=) {p = ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (qq^₁ k X=)}) ∙ ap PiStr (! ((ap-irr (λ z p → ⟦ weakenTy' (prev k) B ⟧Ty z $ p) (⟦weakenTy⟧=' k X= A Aᵈ ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl) ∙ ⟦weakenTy⟧=' (prev k) (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) B Bᵈ ∙ ap2-irr star (ap2-irr qq (qq^= k X= A Aᵈ) (! (⟦⟧Ty-ft B))) refl)))) , ⟦⟧Tmₛ (weakenTm' k a) , (⟦weakenTm⟧₁' k X= a aᵈ ∙ ap2-irr star refl a₁ {b' = ! (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (qq^₁ k X=))} ∙ ap2-irr star refl (⟦⟧Ty-ft B) ∙ ! (⟦⟧Ty-ft (weakenTy' (prev k) B) ∙ ⟦weakenTy⟧=' k X= A Aᵈ)) , tt)

apApp : {A B E H : Set} {C : B → Prop} {D : A → B → Prop} {F : E → Prop} {G : A → E → Prop} (h : (a : A) (b : B) (c : C b) (d : D a b) (e : E) (f : F e) (g : G a e) → H) {a a' : A} (p : a ≡ a') {b b' : B} (q : b ≡ b') {c : C b} {c' : C b'} {d : D a b} {d' : D a' b'} {e e' : E} (r : e ≡ e') {f : F e} {f' : F e'} {g : G a e} {g' : G a' e'} → h a b c d e f g ≡ h a' b' c' d' e' f' g'
apApp h refl refl refl = refl


⟦weakenTm⟧=' last X= (var last) tt = ap ss (ap2-irr comp (ap ss (ap idC X=)) refl)
⟦weakenTm⟧=' (prev k) X= (var last) tt = ss-comp {f₁ = id₁} ∙ ap ss (ap2-irr comp refl (ap idC (! qq₀)) ∙ id-left) ∙ ! (ss-comp {f₁ = comp₁ ∙ ss₁} ∙ ap ss (! assoc) ∙ ap ss (ap2-irr comp (! ss-qq ∙ ap idC (! qq₁)) refl) ∙ ap ss (id-right))
⟦weakenTm⟧=' last X= (var (prev x)) (xᵈ , x₀ , tt) = ap ss (ap2-irr comp (ap ss (ap2-irr comp (ap-irr (λ z p → ⟦ var x ⟧Tm z $ p) (ap ft X=)) (ap pp X=))) refl)
⟦weakenTm⟧=' (prev k) X= (var (prev x)) (xᵈ , x₀ , tt) = ap ss (ap2-irr comp (ap-irr (λ z p → ⟦ var (weakenVar' k x) ⟧Tm z $ p) (ft-star ∙ qq^₀ k X=) ∙ (⟦weakenTm⟧=' k X= (var x) xᵈ)) refl {b' = pp₁ ∙ ft-star ∙ ! (ss₀ ∙ comp₀)}) ∙ ss-comp {f₁ = comp₁ ∙ ss₁} ∙ ap ss (! assoc) ∙ ap ss (ap2-irr comp (! ss-qq) refl) ∙ ap ss assoc ∙ ! (ss-comp {f₁ = comp₁ ∙ ss₁}∙ ap ss (! assoc) ∙ ap ss (ap2-irr comp (! ss-qq) refl) ∙ ap ss assoc ∙ ap ss (ap2-irr comp refl pp-qq)) 
⟦weakenTm⟧=' k X= (lam A B u) (Aᵈ , uᵈ , uₛ , tt) = ! (lamStrNat (qq^ k X=) {p = ap ft (⟦⟧Tm₀ u) ∙ ⟦⟧Ty-ft A ∙ ! (qq^₁ k X=)} ∙ ap-irr lamStr (! (ap-irr (λ z p → ⟦ weakenTm' (prev k) u ⟧Tm z $ p) (⟦weakenTy⟧=' k X= A Aᵈ ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl) ∙ ⟦weakenTm⟧=' (prev k) (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) u uᵈ ∙ ap ss (ap2-irr comp refl (ap2-irr qq (qq^= k X= A Aᵈ) (! (⟦⟧Tm₀ u)))))))
⟦weakenTm⟧=' k X= (app A B f a) (Aᵈ , Bᵈ , fᵈ , aᵈ , fₛ , f₁ , aₛ , a₁ , tt) = ! (appStrNat (qq^ k X=) {p = ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (qq^₁ k X=)} ∙ apApp appStr ((! (ap-irr (λ z p → ⟦ weakenTy' (prev k) B ⟧Ty z $ p) (⟦weakenTy⟧=' k X= A Aᵈ ∙ ap2-irr star (qq^=! k X= A Aᵈ) refl) ∙ ⟦weakenTy⟧=' (prev k) (X= ∙ ap (ft^ k) (! (⟦⟧Ty-ft A))) B Bᵈ ∙ ap2-irr star (ap2-irr qq (qq^= k X= A Aᵈ) (! (⟦⟧Ty-ft B))) refl))) (! (⟦weakenTm⟧=' k X= f fᵈ)) (! (⟦weakenTm⟧=' k X= a aᵈ)))


⟦weakenTm⟧₁' k X= u uᵈ = ap ∂₁ (⟦weakenTm⟧=' k X= u  uᵈ) ∙ ss₁ ∙  ap2-irr star (! (assoc {q = ! (pp₀ ∙ comp₁)})) refl ∙ star-comp (comp₁ ∙ pp₁) ∙ (ap2-irr star refl (ap2-irr star (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! (ap ft comp₁ ∙ ⟦⟧Tm₁-ft u))) refl ∙ star-id ∙ comp₁))


⟦weakenTy⟧ᵈ X= A Aᵈ = ⟦weakenTy⟧ᵈ' last X= A Aᵈ
⟦weakenTy⟧= X= A Aᵈ = ⟦weakenTy⟧=' last X= A Aᵈ

⟦weakenTm⟧ᵈ X= u uᵈ = ⟦weakenTm⟧ᵈ' last X= u uᵈ
⟦weakenTm⟧= X= u uᵈ = ⟦weakenTm⟧=' last X= u uᵈ
⟦weakenTm⟧₁ X= u uᵈ = ⟦weakenTm⟧₁' last X= u uᵈ 

⟦weakenMor⟧ᵈ refl ◇ tt = tt
⟦weakenMor⟧ᵈ {X+ = X+} refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = (⟦weakenMor⟧ᵈ refl δ δᵈ , ⟦weakenTm⟧ᵈ refl u uᵈ , ⟦⟧Mor₁ (weakenMor δ) , (⟦weakenTm⟧₁ refl u uᵈ ∙ ap2-irr star refl u₁ ∙ ! (star-comp δ₁) ∙ ! (ap2-irr star (⟦weakenMor⟧= refl δ δᵈ) refl)) , tt) 

⟦weakenMor⟧= refl ◇ tt = ! (ptmor-unique _ _ (comp₀ ∙ pp₀) (comp₁ ∙ pt-unique _))

⟦weakenMor⟧= refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = ap2-irr comp (ap2-irr qq (⟦weakenMor⟧= refl δ δᵈ) refl ∙ qq-comp (⟦⟧Mor₁ δ)) (⟦weakenTm⟧= refl u uᵈ) ∙ assoc {p = ss₁ ∙ ! (qq₀ ∙ ap2-irr star (! (! (assoc {q = ! pp₀ ∙ ap ∂₀ (ap pp (! comp₁))}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! pp₁)) refl ∙ id-right)) (! (comp₁ ∙ u₁)))} {q = qq₁ ∙ ! qq₀} ∙ ap2-irr comp refl (ap2-irr comp (ap2-irr qq (! (! (assoc {q = ! pp₀ ∙ ap ∂₀ (ap pp (! comp₁))}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! pp₁)) refl ∙ id-right)) (! (comp₁ ∙ u₁))) refl ∙ ! ss-qq) ∙ ! assoc

⟦weakenMorVar⟧ᵈ refl refl δ δᵈ p = ((⟦weakenMor⟧ᵈ refl δ δᵈ) , (tt , (⟦⟧Mor₁ (weakenMor δ) , ((ss₁ ∙ ap2-irr star (ap2-irr comp (ap pp (id₁ ∙ p)) (ap idC (p ∙ ! pp₀)) ∙ id-left) (id₁ ∙ p) ∙ ! (star-comp {p = pp₁ ∙ ! (⟦⟧Mor₀ δ ∙ ap ft p)} (⟦⟧Mor₁ δ)) ∙ ap2-irr star (ap2-irr comp refl (ap pp (! p)) ∙ ! (⟦weakenMor⟧= refl δ δᵈ)) refl) , tt))))


⟦weakenMorVar⟧= refl refl δ δᵈ p = ap2-irr comp (ap2-irr qq (⟦weakenMor⟧= refl δ δᵈ) refl) refl {b' = ss₁ ∙ ! (qq₀ ∙ star-comp (⟦⟧Mor₁ δ) ∙ ap2-irr star (! (ap2-irr comp (ap pp id₁) (ap idC (! pp₀)) ∙ id-left)) (! p ∙ ! id₁))} ∙ ap2-irr comp (qq-comp (⟦⟧Mor₁ δ)) refl ∙ (assoc {p = ss₁ ∙ ! (qq₀ ∙ ap2-irr star (! (ap2-irr comp (ap pp id₁) (ap idC (! pp₀)) ∙ id-left)) (! p ∙ ! id₁))}) ∙ ap2-irr comp refl (ap2-irr comp (ap2-irr qq (! id-left ∙ ap2-irr comp (ap pp (! id₁)) (ap idC pp₀)) (! p ∙ ! id₁)) refl ∙ (! ss-qq) ∙ ap idC (! (qq₀ ∙ ! p))) ∙ id-left


⟦⟧TyEq r (TySymm dA=) Aᵈ A'ᵈ = ! (⟦⟧TyEq r dA= A'ᵈ Aᵈ)
⟦⟧TyEq r (TyTran dB dA= dB=) Aᵈ A'ᵈ = ⟦⟧TyEq r dA= Aᵈ (⟦⟧Tyᵈ r dB) ∙ ⟦⟧TyEq r dB= (⟦⟧Tyᵈ r dB) A'ᵈ
⟦⟧TyEq r {A = pi A B} {A' = pi A' B'} (PiCong dA dA= dB=) (Aᵈ , Bᵈ , _) (A'ᵈ , B'ᵈ , _) rewrite ! (⟦⟧TyEq r dA= Aᵈ A'ᵈ) | ! (⟦⟧TyEq (respectsCtxExt r A) dB= Bᵈ B'ᵈ)
  = refl
⟦⟧TyEq r UUCong Aᵈ A'ᵈ = refl
⟦⟧TyEq r (ElCong dv=) (vᵈ , _) (v'ᵈ , _) rewrite ⟦⟧TmEq r dv= vᵈ v'ᵈ = refl

⟦⟧TmEq r (VarLastCong dA) tt tt = refl
⟦⟧TmEq r (VarPrevCong {k = k} {k' = k'} dA dx) _ _ = ap ss (ap2-irr comp (⟦⟧TmEq (fst r) dx _ _) refl)
⟦⟧TmEq r (TmSymm du=) uᵈ u'ᵈ = ! (⟦⟧TmEq r du= u'ᵈ uᵈ)
⟦⟧TmEq r (TmTran dv du= du'=) uᵈ u'ᵈ = ⟦⟧TmEq r du= uᵈ (⟦⟧Tmᵈ r dv) ∙ ⟦⟧TmEq r du'= (⟦⟧Tmᵈ r dv) u'ᵈ
⟦⟧TmEq r (ConvEq dA' du= dA=) uᵈ u'ᵈ = ⟦⟧TmEq r du= uᵈ u'ᵈ
⟦⟧TmEq r {u = lam A B u} (LamCong dA dA= dB= du=) (Aᵈ , uᵈ , utmᵈ , _) (A'ᵈ , u'ᵈ , utm'ᵈ , _)
  rewrite ! (⟦⟧TyEq r dA= Aᵈ A'ᵈ)
        | ! (⟦⟧TmEq {X = ⟦ A ⟧Ty _ $ Aᵈ} (respectsCtxExt r A) du= uᵈ u'ᵈ) = refl
⟦⟧TmEq r {u = app A B f a} (AppCong dA dA= dB= df= da=) (Aᵈ , Bᵈ , fᵈ , aᵈ , _) (A'ᵈ , B'ᵈ , f'ᵈ , a'ᵈ , _)
  rewrite ! (⟦⟧TyEq r dA= Aᵈ A'ᵈ)
           | ⟦⟧TyEq {X = ⟦ A ⟧Ty _ $ Aᵈ} (respectsCtxExt r A) dB= Bᵈ B'ᵈ
           | ⟦⟧TmEq r df= fᵈ f'ᵈ
           | ⟦⟧TmEq r da= aᵈ a'ᵈ = refl
⟦⟧TmEq r {u = app A B (lam A B u) a} (BetaPi dA dB du da) (Aᵈ , Bᵈ , (_ , uᵈ , uₛ , tt) , aᵈ , _ , u₁ , aₛ , a₁ , tt) u'ᵈ =
  betaPiStr {uₛ = uₛ} {u₁ = ⟦⟧Tm₁ (respectsCtxExt r A) u du} {aₛ = aₛ} {a₁ = a₁ ∙ ap ft (! (⟦⟧Tm₁ (respectsCtxExt r A) u du))}
  ∙ ! (⟦tsubst⟧Tm= u uᵈ (idMor _ , a) (⟦idMor+⟧ᵈ (⟦⟧Ty-ft A) a aᵈ (a₁ ∙ ⟦⟧Ty-ft B))
      ∙ ap ss (ap2-irr comp refl (⟦idMor+⟧= (⟦⟧Ty-ft A) a aᵈ (a₁ ∙ ⟦⟧Ty-ft B))))

⟦tsubst⟧Tyᵈ (pi A B) {δ = δ} (Aᵈ , Bᵈ , tt) δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δᵈ ,
   ⟦tsubst⟧Tyᵈ B Bᵈ (⟦weakenMorVar⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
  , tt)
⟦tsubst⟧Tyᵈ (uu i) tt δᵈ = tt
⟦tsubst⟧Tyᵈ (el i v) {δ = δ} (vᵈ , vₛ , v₁ , tt) δᵈ =
  (⟦tsubst⟧Tmᵈ v vᵈ δᵈ ,
   ⟦⟧Tmₛ (v [ δ ]Tm) ,
   (ap ∂₁ (⟦tsubst⟧Tm= v vᵈ δ δᵈ) ∙ ss₁ ∙ (ap2-irr star (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ v ∙ ap idC (⟦⟧Tm₀ v ∙ ! (⟦⟧Mor₁ δ))) refl ∙ id-right) (comp₁ ∙ v₁) ∙ UUStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) {p = ⟦⟧Tm₀ v ∙ ! (⟦⟧Mor₁ δ)}) ∙ (ap (UUStr i) (! (ss₀ ∙ comp₀) ∙ ap ∂₀ (! (⟦tsubst⟧Tm= v vᵈ δ δᵈ))))) , tt)

⟦tsubst⟧Ty= (pi A B) (Aᵈ , Bᵈ , tt) δ δᵈ = ! (PiStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) {p = (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A) ∙ ! (⟦⟧Mor₁ δ)} ∙ ap PiStr (! (⟦tsubst⟧Ty= B Bᵈ (weakenMor δ , var last) (⟦weakenMorVar⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ∙ ap2-irr star (⟦weakenMorVar⟧= (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ∙ ap2-irr qq refl (! (⟦⟧Ty-ft B))) refl)))
⟦tsubst⟧Ty= (uu i) Aᵈ δ δᵈ = ! (UUStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) {p = ! (⟦⟧Mor₁ δ)} ∙ ap (UUStr i) (⟦⟧Mor₀ δ))
⟦tsubst⟧Ty= (el i v) (vᵈ , _) δ δᵈ = ! (ElStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) {p = ⟦⟧Tm₀ v ∙ ! (⟦⟧Mor₁ δ)} ∙ ap-irr2 (ElStr i) (! (⟦tsubst⟧Tm= v vᵈ δ δᵈ)))

⟦tsubst⟧Tmᵈ (var ()) {◇} uᵈ δᵈ
⟦tsubst⟧Tmᵈ (var last) {δ , u} _ (_ , uᵈ , _) = uᵈ
⟦tsubst⟧Tmᵈ (var (prev x)) {δ , u} (xᵈ , _) (δᵈ , _) = ⟦tsubst⟧Tmᵈ (var x) xᵈ δᵈ
⟦tsubst⟧Tmᵈ (lam A B u) {δ = δ} (Aᵈ , uᵈ , p) δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δᵈ ,
   ⟦tsubst⟧Tmᵈ u uᵈ (⟦weakenMorVar⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
   ⟦⟧Tmₛ (u [ weakenMor δ , var last ]Tm) , tt)
⟦tsubst⟧Tmᵈ (app A B f a) {δ = δ} (Aᵈ , Bᵈ , fᵈ , aᵈ , fₛ , f₁ , aₛ , a₁ , tt) δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δᵈ ,
   ⟦tsubst⟧Tyᵈ B Bᵈ (⟦weakenMorVar⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)) ,
   ⟦tsubst⟧Tmᵈ f fᵈ δᵈ ,
   ⟦tsubst⟧Tmᵈ a aᵈ δᵈ ,
   ⟦⟧Tmₛ (f [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ f fᵈ δ δᵈ
    ∙ ap2-irr star refl f₁
    ∙ PiStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) {p = ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ)}
    ∙ ap PiStr (! (⟦tsubst⟧Ty= B Bᵈ (weakenMor δ , var last) (⟦weakenMorVar⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                  ∙ ap2-irr star (⟦weakenMorVar⟧= (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ)
                                 ∙ ap2-irr qq refl (! (⟦⟧Ty-ft B))) refl))) ,
   ⟦⟧Tmₛ (a [ δ ]Tm) ,
   (⟦tsubst⟧Tm₁ a aᵈ δ δᵈ
     ∙ ap2-irr star refl a₁ {b = ⟦⟧Mor₁ δ ∙ ! (⟦⟧Tm₁-ft a)} {b' = ⟦⟧Mor₁ δ ∙ ! (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A)}
     ∙ ! (⟦⟧Ty-ft (B [ weakenMor δ , var last ]Ty)
         ∙ ⟦tsubst⟧Ty= A Aᵈ δ δᵈ
         ∙ ap2-irr star refl (! (⟦⟧Ty-ft B)))) , tt)

⟦tsubst⟧Tm= (var ()) _ ◇ δᵈ
⟦tsubst⟧Tm= (var last) tt (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = ! (ss-of-section (⟦ u ⟧Tm _ $ uᵈ) (⟦⟧Tmₛ u)) ∙ ss-comp {f₁ = u₁} ∙ ap ss ((! id-right ∙ ap2-irr comp (ap idC (comp₁ ∙ qq₁) ∙ ss-qq) refl) ∙ assoc {q = ss₁ ∙ ! qq₀}) ∙ ! (ss-comp {f₁ = comp₁ ∙ ss₁})
⟦tsubst⟧Tm= (var (prev x)) (xᵈ , _) (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = ⟦tsubst⟧Tm= (var x) xᵈ δ δᵈ ∙ ! (ss-comp {f₁ = comp₁ ∙ ss₁} ∙ ap ss (! (assoc {q = ss₁ ∙ ! qq₀}) ∙ ap2-irr comp (! ss-qq) refl ∙ assoc ∙ ap2-irr comp refl (! assoc ∙ ap2-irr comp pp-qq refl ∙ assoc {p = u₁ ∙ ! pp₀} {q = pp₁ ∙ ft-star} ∙ ap2-irr comp refl (ap2-irr comp (ap pp (! u₁)) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! (⟦⟧Mor₀ δ))) ∙ id-left)))
⟦tsubst⟧Tm= (lam A B u) (Aᵈ , uᵈ , _) δ δᵈ =
  ap-irr lamStr (⟦tsubst⟧Tm= u uᵈ (weakenMor δ , var last) (⟦weakenMorVar⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                ∙ ap ss (ap2-irr comp refl (⟦weakenMorVar⟧= (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ∙ ap2-irr qq refl (! (⟦⟧Tm₀ u)))))
  ∙ ! (lamStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) {p = ap ft (⟦⟧Tm₀ u) ∙ ⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ)})
⟦tsubst⟧Tm= (app A B f a) (Aᵈ , Bᵈ , fᵈ , aᵈ , fₛ , f₁ , aₛ , a₁ , tt) δ δᵈ =
  apApp appStr (⟦tsubst⟧Ty= B Bᵈ (weakenMor δ , var last) (⟦weakenMorVar⟧ᵈ (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ))
                ∙ ap2-irr star (⟦weakenMorVar⟧= (⟦⟧Ty-ft (A [ δ ]Ty)) (⟦⟧Ty-ft A) δ δᵈ (⟦tsubst⟧Ty= A Aᵈ δ δᵈ) ∙ ap2-irr qq refl (! (⟦⟧Ty-ft B))) refl)
               (⟦tsubst⟧Tm= f fᵈ δ δᵈ)
               (⟦tsubst⟧Tm= a aᵈ δ δᵈ)
  ∙ ! (appStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) {p = ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A ∙ ! (⟦⟧Mor₁ δ)})

⟦tsubst⟧Tm₁ u uᵈ δ δᵈ = ap ∂₁ (⟦tsubst⟧Tm= u uᵈ δ δᵈ) ∙ ss₁ ∙ ap2-irr star (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! (⟦⟧Mor₁ δ))) refl ∙ id-right) comp₁

⟦subst⟧Tyᵈ {X = X} refl B Bᵈ uᵈ q = ⟦tsubst⟧Tyᵈ B Bᵈ (⟦idMor⟧ᵈ {X = ft X} refl , uᵈ , ⟦⟧Mor₁ (idMor _) , (q ∙ ! (ap2-irr star (⟦idMor⟧= refl) refl ∙ star-id)) , tt)

⟦subst⟧Ty= {X = X} refl B {u = u} Bᵈ uᵈ q = ⟦tsubst⟧Ty= B Bᵈ (idMor _ , _) (⟦idMor⟧ᵈ {X = ft X} refl , uᵈ , ⟦⟧Mor₁ (idMor _) , (q ∙ ! (ap2-irr star (⟦idMor⟧= refl) refl ∙ star-id)) , tt) ∙ ap2-irr star (⟦idMor+⟧= refl u uᵈ q) refl


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
  rewrite ! (⟦⟧CtxEq dΓ= {Γᵈ} {Γ'ᵈ}) | ⟦⟧TyEq respects⟦⟧Ctx dA= Aᵈ A'ᵈ = refl

{- Interpretation of morphism equalities -}

⟦⟧MorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} {X : Ob n} {Y : Ob m} (r : respectsCtx X Γ) (dδ= : Γ ⊢ δ == δ' ∷> Δ) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} {δ'ᵈ : isDefined (⟦ δ' ⟧Mor X Y)}
        → ⟦ δ ⟧Mor X Y $ δᵈ ≡ ⟦ δ' ⟧Mor X Y $ δ'ᵈ
⟦⟧MorEq {Δ = ◇} {δ = ◇} {◇} r tt = refl
⟦⟧MorEq {Γ' = Γ'} {Δ = Δ , B} {δ = δ , u} {δ' , u'} r (dδ= , du=) = ap2-irr comp (ap2-irr qq (⟦⟧MorEq {Γ' = Γ'} {Δ' = Δ} r dδ=) refl) (⟦⟧TmEq r du= _ _)

{- Interpretation of morphism substitution -}

⟦tsubst⟧Morᵈ : {X : Ob n} {Y Y' : Ob m} {Z : Ob k} (Y= : Y ≡ Y') (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (θ : Mor m k) (θᵈ : isDefined (⟦ θ ⟧Mor Y' Z)) → isDefined (⟦ θ [ δ ]Mor ⟧Mor X Z)
⟦tsubst⟧Mor= : {X : Ob n} {Y Y' : Ob m} {Z : Ob k} (Y= : Y ≡ Y') (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (θ : Mor m k) (θᵈ : isDefined (⟦ θ ⟧Mor Y' Z))
             → ⟦ θ [ δ ]Mor ⟧Mor X Z $ (⟦tsubst⟧Morᵈ Y= δ δᵈ θ θᵈ) ≡ comp (⟦ θ ⟧Mor Y' Z $ θᵈ) (⟦ δ ⟧Mor X Y $ δᵈ) (⟦⟧Mor₁ δ ∙ Y= ∙ ! (⟦⟧Mor₀ θ))

⟦tsubst⟧Morᵈ refl δ δᵈ ◇ tt = tt
⟦tsubst⟧Morᵈ refl δ δᵈ (θ , u) (θᵈ , uᵈ , θ₁ , u₁ , tt) = (⟦tsubst⟧Morᵈ refl δ δᵈ θ θᵈ , ⟦tsubst⟧Tmᵈ u uᵈ δᵈ , ⟦⟧Mor₁ (θ [ δ ]Mor) , (⟦tsubst⟧Tm₁ u uᵈ δ δᵈ ∙ ! (ap2-irr star (⟦tsubst⟧Mor= refl δ δᵈ θ θᵈ) refl ∙ star-comp (⟦⟧Mor₁ θ) ∙ ap2-irr star refl (! u₁))) , tt)

⟦tsubst⟧Mor= refl δ δᵈ ◇ θᵈ = ! (ptmor-unique _ _ (comp₀ ∙ ⟦⟧Mor₀ δ) (comp₁ ∙ ptmor₁))
⟦tsubst⟧Mor= refl δ δᵈ (θ , u) (θᵈ , uᵈ , θ₁ , u₁ , tt) =
  let thing = (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ ⟦⟧Tmₛ u ∙ ap idC (⟦⟧Tm₀ u ∙ ! (⟦⟧Mor₁ δ))) refl ∙ id-right) in
  ap2-irr comp (ap2-irr qq (⟦tsubst⟧Mor= refl δ δᵈ θ θᵈ) refl) (⟦tsubst⟧Tm= u uᵈ δ δᵈ) {b' = ss₁ ∙ (ap2-irr star thing (comp₁ ∙ u₁) ∙ ! (star-comp (⟦⟧Mor₁ θ))) ∙ ! qq₀}
  ∙ ap2-irr comp (qq-comp _) refl ∙ assoc {p = ss₁ ∙ ap2-irr star thing (comp₁ ∙ u₁) ∙ ! qq₀} {q = qq₁ ∙ ! qq₀}
  ∙ ! (assoc ∙ ap2-irr comp refl (ss-qq ∙ ap2-irr comp (ap2-irr qq thing (comp₁ ∙ u₁)) refl))

