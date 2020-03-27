{-# OPTIONS --rewriting --prop #-}

open import common
open import typetheory
open import reflection hiding (proj)
open import syntx hiding (Mor; getTy)
open import rules
open import contextualcat
open import contextualcatmor
open import quotients
open import termmodel 
import partialinterpretation
import totality

module _ (sC : StructuredCCat) where

open StructuredCCat
open CCatMor
open partialinterpretation sC
open import interpretationweakening sC
open import interpretationsubstitution sC
open totality sC
open StructuredCCatMor+
open StructuredCCatMor

private
  C = ccat sC

open CCat+ C renaming (id to idC)

{- Uniqueness of the morphism -}

getLastTy : {Δ : Ctx n} {C : TyExpr n} → ⊢ (Δ , C) → Derivable (Δ ⊢ C)
getLastTy (_ , dC) = dC

getFirstTms : {Γ : Ctx n} {Δ : Ctx m} {C : TyExpr m} {δ : syntx.Mor n m} {u : TmExpr n} → Γ ⊢ (δ , u) ∷> (Δ , C) → Γ ⊢ δ ∷> Δ
getFirstTms (dδ , _) = dδ

getLastTm : {Γ : Ctx n} {Δ : Ctx m} {C : TyExpr m} {δ : syntx.Mor n m} {u : TmExpr n} → Γ ⊢ (δ , u) ∷> (Δ , C) → Derivable (Γ ⊢ u :> C [ δ ]Ty)
getLastTm (_ , du) = du

split-left : DMor n (suc m) → DMor n (suc n)
split-left (dmor' (dctx' dΓ) (dctx' {ctx = _ , _} dΔC) {mor = _ , _} dδu) =
  dmor (dctx dΓ) (dctx {ctx = _ , _} (dΓ , SubstTy (getLastTy dΔC) (getFirstTms dδu))) {mor = _ , _} (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl (getLastTm dδu))

split-right : DMor n (suc m) → DMor (suc n) (suc m)
split-right (dmor' (dctx' dΓ) (dctx' {ctx = _ , _} dΔC) {mor = _ , _} dδu) =
  dmor (dctx {ctx = _ , _} (dΓ , SubstTy (getLastTy dΔC) (getFirstTms dδu))) (dctx {ctx = _ , _} dΔC) {mor = _ , _} (WeakMor (getFirstTms dδu) , (congTm (weaken[]Ty _ _ last) refl (VarLast (SubstTy (getLastTy dΔC) (getFirstTms dδu)))))

split-eq : (δ : DMor n (suc m)) → ⊢ ctx (rhs (split-left δ)) == ctx (lhs (split-right δ))
split-eq (dmor' (dctx' dΓ) (dctx' {ctx = _ , _} (dΔ , dC)) {mor = _ , _} (dδ , du)) = CtxRefl (dΓ , SubstTy dC dδ)

split-comp : (δ : DMor n (suc m)) → compS-// (split-right δ) (split-left δ) _ refl (eq (box (split-eq δ))) ≡ δ
split-comp (dmor' (dctx' dΓ) (dctx' {ctx = _ , _} (dΔ , dC)) {mor = δ , u} (dδ , du)) =
  ap-irr (λ x z → dmor' (dctx' dΓ) (dctx' {ctx = _ , _} (dΔ , dC)) {mor = x} z) (Mor+= (weakenMorInsert _ _ _ ∙ [idMor]Mor δ) refl) 


module _ (sf+ sg+ : StructuredCCatMor+ strSynCCat sC) where

  private
    sf = strucCCat→ sf+
    sg = strucCCat→ sg+
    f = ccat→ sf
    g = ccat→ sg

  -- Non-recursive lemmas that are needed for J

  uniqueness-Ty-//-Id : {Γ : Ctx n} (dΓ : ⊢ Γ) {A : TyExpr n} {u v : TmExpr n} (dA : Derivable (Γ ⊢ A)) (du : Derivable (Γ ⊢ u :> A)) (dv : Derivable (Γ ⊢ v :> A))
                        (uΓ : Ob→ f (proj (dctx dΓ)) ≡ Ob→ g (proj (dctx dΓ)))
                        (uA : Ob→ f (proj (dctx (dΓ , dA))) ≡ Ob→ g (proj (dctx (dΓ , dA))))
                        (u-u : Mor→ f (proj (dmorTm (dctx dΓ) du)) ≡ Mor→ g (proj (dmorTm (dctx dΓ) du)))
                        (uv : Mor→ f (proj (dmorTm (dctx dΓ) dv)) ≡ Mor→ g (proj (dmorTm (dctx dΓ) dv)))
                        → Ob→ f (proj (dctx (dΓ , Id dA du dv))) ≡ Ob→ g (proj (dctx (dΓ , Id dA du dv)))
  uniqueness-Ty-//-Id dΓ dA du dv uΓ uA u-u uv =
    IdStr→ sf _ _ refl _ dmorTmₛ refl _ dmorTmₛ refl
    ∙ ap-irr-IdStr sC uΓ uA u-u uv
    ∙ ! (IdStr→ sg _ _ refl _ dmorTmₛ refl _ dmorTmₛ refl)

  uniqueness-Ty-//-Weak : {Γ : Ctx n} (dΓ : ⊢ Γ) {A B : TyExpr n} (dA : Derivable (Γ ⊢ A)) (dB : Derivable (Γ ⊢ B))
                          (uΓ : Ob→ f (proj (dctx dΓ)) ≡ Ob→ g (proj (dctx dΓ)))
                          (uA : Ob→ f (proj (dctx (dΓ , dA))) ≡ Ob→ g (proj (dctx (dΓ , dA))))
                          (uB : Ob→ f (proj (dctx (dΓ , dB))) ≡ Ob→ g (proj (dctx (dΓ , dB))))
                          → Ob→ f (proj (dctx ((dΓ , dB) , SubstTy dA (WeakMor (idMorDerivable dΓ)))))
                          ≡ Ob→ g (proj (dctx ((dΓ , dB) , SubstTy dA (WeakMor (idMorDerivable dΓ)))))
  uniqueness-Ty-//-Weak dΓ dA dB uΓ uA uB =
    star→ f {f = proj (dmor (dctx (dΓ , dB)) (dctx dΓ) (WeakMor (idMorDerivable dΓ)))} {X = proj (dctx (dΓ , dA))} {q = refl} {f₁ = refl}
    ∙ ap-irr-star (pp→ f {X = proj (dctx (dΓ , dB))} ∙ ap pp uB ∙ ! (pp→ g {X = proj (dctx (dΓ , dB))})) uA
    ∙ ! (star→ g {f = proj (dmor (dctx (dΓ , dB)) (dctx dΓ) (WeakMor (idMorDerivable dΓ)))} {X = proj (dctx (dΓ , dA))} {q = refl} {f₁ = refl})

  uniqueness-Tm-//-Var : {Γ : Ctx n} (dΓ : ⊢ Γ) (k : VarPos n)
                       → (uΓ : Ob→ f (proj (dctx dΓ)) ≡ Ob→ g (proj (dctx dΓ)))
                       → {A : _} (A= : syntx.getTy k Γ ≡ A)
                       → Mor→ f (proj (dmorTm (dctx dΓ) (congTmTy A= (Var k (getTyDer k dΓ)))))
                       ≡ Mor→ g (proj (dmorTm (dctx dΓ) (congTmTy A= (Var k (getTyDer k dΓ)))))
  uniqueness-Tm-//-Var dΓ@(dΓ' , dA) last uΓ refl =
    ap (Mor→ f) (eq (box (CtxRefl dΓ) (CtxRefl dΓ , congTyRefl (WeakTy dA) (! (ap weakenTy ([idMor]Ty _)) ∙ weaken[]Ty _ (idMor _) last))
                         (MorRefl (idMorDerivable dΓ , congTmTy! ([idMor]Ty (weakenTy _)) (VarLast dA)))))
    ∙ (ss→ f {f = proj (dmor (dctx dΓ) (dctx dΓ) (idMorDerivable dΓ))}
    ∙ ap ss (id→ f ∙ ap idC uΓ ∙ ! (id→ g))
    ∙ ! (ss→ g {f = proj (dmor (dctx dΓ) (dctx dΓ) (idMorDerivable dΓ))}))
    ∙ ! (ap (Mor→ g) (eq (box (CtxRefl dΓ) (CtxRefl dΓ , congTyRefl (WeakTy dA) (! (ap weakenTy ([idMor]Ty _)) ∙ weaken[]Ty _ (idMor _) last))
                              (MorRefl (idMorDerivable dΓ , congTmTy! ([idMor]Ty (weakenTy _)) (VarLast dA))))))
  uniqueness-Tm-//-Var (dΓ , dB) (prev k) uΓ refl =
    ap (Mor→ f) (eq (box (CtxRefl (dΓ , dB)) (CtxRefl (dΓ , dB) , congTyRefl (getTyDer (prev k) (dΓ , dB)) (ap weakenTy (! ([idMor]Ty _)) ∙ weaken[]Ty _ (idMor _) last ∙ ap (λ z → syntx.getTy k _ [ z ]Ty) (! (idMor[]Mor _))))
                         (MorRefl (idMorDerivable (dΓ , dB)) , congTmRefl (congTm (! ([idMor]Ty _)) refl (Var (prev k) (getTyDer (prev k) (dΓ , dB)))) (ap weakenTm (! ([idMor]Tm (var k))) ∙ weaken[]Tm (var k) (idMor _) last))))
    ∙ ss→ f {f = proj (dmor (dctx (dΓ , dB)) (dctx (dΓ , getTyDer k dΓ))
                            (SubstMor (idMorDerivable dΓ) (WeakMor (idMorDerivable dΓ)) , congTm (ap (λ z → syntx.getTy k _ [ z ]Ty) (! (idMor[]Mor _))) refl (SubstTm (Var k (getTyDer k dΓ)) (WeakMor (idMorDerivable dΓ)))))}
    ∙ ap ss (comp→ f {g = proj (dmor (dctx dΓ) (dctx (dΓ , getTyDer k dΓ)) (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl (Var k (getTyDer k dΓ))))} {f = ppS (proj (dctx (dΓ , dB)))} {g₀ = refl} {f₁ = refl}
            ∙ ap-irr-comp (uniqueness-Tm-//-Var dΓ k (ft→ f ∙ ap ft uΓ ∙ ! (ft→ g)) refl)
                          (pp→ f {X = proj (dctx (dΓ , dB))}
                           ∙ ap pp uΓ
                           ∙ ! (pp→ g {X = proj (dctx (dΓ , dB))}))
            ∙ ! (comp→ g {g = proj (dmor (dctx dΓ) (dctx (dΓ , getTyDer k dΓ)) (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl (Var k (getTyDer k dΓ))))}
                         {f = ppS (proj (dctx (dΓ , dB)))} {g₀ = refl} {f₁ = refl}))
    ∙ ! (ss→ g {f = proj (dmor (dctx (dΓ , dB)) (dctx (dΓ , getTyDer k dΓ))
                               (SubstMor (idMorDerivable dΓ) (WeakMor (idMorDerivable dΓ)) , congTm (ap (λ z → syntx.getTy k _ [ z ]Ty) (! (idMor[]Mor _))) refl (SubstTm (Var k (getTyDer k dΓ)) (WeakMor (idMorDerivable dΓ)))))})
    ∙ ! (ap (Mor→ g) (eq (box (CtxRefl (dΓ , dB)) (CtxRefl (dΓ , dB) , congTyRefl (getTyDer (prev k) (dΓ , dB)) (ap weakenTy (! ([idMor]Ty _)) ∙ weaken[]Ty _ (idMor _) last ∙ ap (λ z → syntx.getTy k _ [ z ]Ty) (! (idMor[]Mor _))))
                              (MorRefl (idMorDerivable (dΓ , dB)) , congTmRefl (congTm (! ([idMor]Ty _)) refl (Var (prev k) (getTyDer (prev k) (dΓ , dB)))) (ap weakenTm (! ([idMor]Tm (var k))) ∙ weaken[]Tm (var k) (idMor _) last)))))

  -- The actual lemmas that we prove by mutual induction

  uniqueness-Ob-// : (Γ : DCtx n)
                   → Ob→ f (proj Γ) ≡ Ob→ g (proj Γ)
  uniqueness-Ty-// : {Γ : Ctx n} (dΓ : ⊢ Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) (uΓ : Ob→ f (proj (dctx dΓ)) ≡ Ob→ g (proj (dctx dΓ)))
                   → Ob→ f (proj (dctx (dΓ , dA))) ≡ Ob→ g (proj (dctx (dΓ , dA)))
  uniqueness-Tm-// : {Γ : Ctx n} (dΓ : ⊢ Γ) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A))
                     (uΓ : Ob→ f (proj (dctx dΓ)) ≡ Ob→ g (proj (dctx dΓ)))
                   → Mor→ f (proj (dmorTm (dctx dΓ) du)) ≡ Mor→ g (proj (dmorTm (dctx dΓ) du))

  uniqueness-Ob-// (dctx' {ctx = ◇} tt) = pt→ f ∙ ! (pt→ g)
  uniqueness-Ob-// (dctx' {ctx = _ , _} (dΓ , dA)) = uniqueness-Ty-// dΓ dA (uniqueness-Ob-// (dctx dΓ))

  uniqueness-Ty-// dΓ UU uΓ =
    UUStr→ sf _ _
    ∙ ap (UUStr sC _) uΓ
    ∙ ! (UUStr→ sg _ _)
  uniqueness-Ty-// dΓ (El dv) uΓ =
    ElStr→ sf _ _ _ dmorTmₛ refl
    ∙ ap-irr-ElStr uΓ
                   (uniqueness-Tm-// dΓ dv uΓ)
    ∙ ! (ElStr→ sg _ _ _ dmorTmₛ refl)
  uniqueness-Ty-// dΓ (Sum dA dB) uΓ =
    SumStr→ sf _ _ refl _ refl
    ∙ ap-irr-SumStr uΓ
                    (uniqueness-Ty-// dΓ dA uΓ)
                    (uniqueness-Ty-// dΓ dB uΓ)
    ∙ ! (SumStr→ sg _ _ refl _ refl)
  uniqueness-Ty-// dΓ (Pi dA dB) uΓ =
    PiStr→ sf _ _ refl _ refl
    ∙ ap-irr-PiStr uΓ
                   (uniqueness-Ty-// dΓ dA uΓ)
                   (uniqueness-Ty-// (dΓ , dA) dB (uniqueness-Ty-// dΓ dA uΓ))
    ∙ ! (PiStr→ sg _ _ refl _ refl)
  uniqueness-Ty-// dΓ (Sig dA dB) uΓ =
    SigStr→ sf _ _ refl _ refl
    ∙ ap-irr-SigStr uΓ
                   (uniqueness-Ty-// dΓ dA uΓ)
                   (uniqueness-Ty-// (dΓ , dA) dB (uniqueness-Ty-// dΓ dA uΓ))
    ∙ ! (SigStr→ sg _ _ refl _ refl)
  uniqueness-Ty-// dΓ Empty uΓ =
    EmptyStr→ sf _
    ∙ ap (EmptyStr sC) uΓ
    ∙ ! (EmptyStr→ sg _)
  uniqueness-Ty-// dΓ Unit uΓ =
    UnitStr→ sf _
    ∙ ap (UnitStr sC) uΓ
    ∙ ! (UnitStr→ sg _)
  uniqueness-Ty-// dΓ Nat uΓ =
    NatStr→ sf _
    ∙ ap (NatStr sC) uΓ
    ∙ ! (NatStr→ sg _)
  uniqueness-Ty-// dΓ (Id dA du dv) uΓ = uniqueness-Ty-//-Id dΓ dA du dv uΓ (uniqueness-Ty-// dΓ dA uΓ) (uniqueness-Tm-// dΓ du uΓ) (uniqueness-Tm-// dΓ dv uΓ)

  uniqueness-Tm-// dΓ (Var k dA) uΓ = uniqueness-Tm-//-Var dΓ k uΓ refl

  uniqueness-Tm-// {Γ = Γ} dΓ (Conv dA du dA=) uΓ =
    ap (Mor→ f) (! (eq (box (CtxRefl dΓ) (CtxRefl dΓ , dA=) (MorRefl (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl du)))))
    ∙ uniqueness-Tm-// dΓ du uΓ
    ∙ ! (ap (Mor→ g) (! (eq (box (CtxRefl dΓ) (CtxRefl dΓ , dA=) (MorRefl (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl du))))))

  uniqueness-Tm-// {Γ = Γ} dΓ {u = uu i} UUUU uΓ =
    uuStr→ sf i _
    ∙ ap (uuStr sC i) uΓ
    ∙ ! (uuStr→ sg i _)

  uniqueness-Tm-// {Γ = Γ} dΓ {u = sum i a b} (SumUU da db) uΓ =
    sumStr→ sf i _ _ dmorTmₛ refl _ dmorTmₛ refl
    ∙ ap-irr-sumStr uΓ
                    (uniqueness-Tm-// dΓ da uΓ)
                    (uniqueness-Tm-// dΓ db uΓ)
    ∙ ! (sumStr→ sg i _ _ dmorTmₛ refl _ dmorTmₛ refl)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = inl A B a} (Inl dA dB da) uΓ =
    inlStr→ sf _ _ refl _ refl _ dmorTmₛ refl
    ∙ ap-irr-inlStr sC
                    uΓ
                    (uniqueness-Ty-// dΓ dA uΓ)
                    (uniqueness-Ty-// dΓ dB uΓ)
                    (uniqueness-Tm-// dΓ da uΓ)
    ∙ ! (inlStr→ sg _ _ refl _ refl _ dmorTmₛ refl)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = inr A B b} (Inr dA dB db) uΓ =
    inrStr→ sf _ _ refl _ refl _ dmorTmₛ refl
    ∙ ap-irr-inrStr sC
                    uΓ
                    (uniqueness-Ty-// dΓ dA uΓ)
                    (uniqueness-Ty-// dΓ dB uΓ)
                    (uniqueness-Tm-// dΓ db uΓ)
    ∙ ! (inrStr→ sg _ _ refl _ refl _ dmorTmₛ refl)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = match A B C da db u} (Match dA dB dC dda ddb du) uΓ =
    matchStr→ sf _ _ refl _ refl _ refl _ dmorTmₛ refl _ dmorTmₛ refl _ dmorTmₛ refl
    ∙ ap-irr-matchStr uΓ
                      (uniqueness-Ty-// dΓ dA uΓ)
                      (uniqueness-Ty-// dΓ dB uΓ)
                      (uniqueness-Ty-// (dΓ , Sum dA dB) dC (uniqueness-Ty-// dΓ (Sum dA dB) uΓ))
                      (uniqueness-Tm-// (dΓ , dA) (congTmTy fixTyda dda) (uniqueness-Ty-// dΓ dA uΓ))
                      (uniqueness-Tm-// (dΓ , dB) (congTmTy fixTydb ddb) (uniqueness-Ty-// dΓ dB uΓ))
                      (uniqueness-Tm-// dΓ du uΓ)
    ∙ ! (matchStr→ sg _ _ refl _ refl _ refl _ dmorTmₛ refl _ dmorTmₛ refl _ dmorTmₛ refl)
    
  uniqueness-Tm-// {Γ = Γ} dΓ {u = pi i a b} (PiUU da db) uΓ =
    piStr→ sf i _ _ dmorTmₛ refl _ dmorTmₛ refl
    ∙ ap-irr-piStr uΓ
                   (uniqueness-Tm-// dΓ da uΓ)
                   (uniqueness-Tm-// (dΓ , El da) db (uniqueness-Ty-// dΓ (El da) uΓ))
    ∙ ! (piStr→ sg i _ _ dmorTmₛ refl _ dmorTmₛ refl)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = lam A B u} (Lam dA dB du) uΓ =
    let uΓA = uniqueness-Ty-// dΓ dA uΓ in
    lamStr→ sf _ _ refl _ refl _ dmorTmₛ refl
    ∙ ap-irr-lamStr uΓ
                    uΓA
                    (uniqueness-Ty-// (dΓ , dA) dB uΓA)
                    (uniqueness-Tm-// (dΓ , dA) du uΓA)
    ∙ ! (lamStr→ sg _ _ refl _ refl _ dmorTmₛ refl)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = app A B f a} (App dA dB df da) uΓ =
    let uΓA = uniqueness-Ty-// dΓ dA uΓ in
    appStr→ sf _ _ refl _ refl _ dmorTmₛ refl _ dmorTmₛ refl
    ∙ ap-irr-appStr uΓ
                    uΓA
                    (uniqueness-Ty-// (dΓ , dA) dB uΓA)
                    (uniqueness-Tm-// dΓ df uΓ)
                    (uniqueness-Tm-// dΓ da uΓ)
    ∙ ! (appStr→ sg _ _ refl _ refl _ dmorTmₛ refl _ dmorTmₛ refl)

  uniqueness-Tm-// {Γ = Γ} dΓ {u = sig i a b} (SigUU da db) uΓ =
    sigStr→ sf i _ _ dmorTmₛ refl _ dmorTmₛ refl
    ∙ ap-irr-sigStr uΓ
                    (uniqueness-Tm-// dΓ da uΓ)
                    (uniqueness-Tm-// (dΓ , El da) db (uniqueness-Ty-// dΓ (El da) uΓ))
    ∙ ! (sigStr→ sg i _ _ dmorTmₛ refl _ dmorTmₛ refl)
  uniqueness-Tm-// {Γ = Γ} dΓ  {u = pair A B a b} (Pair dA dB da db) uΓ =
    let uΓA = uniqueness-Ty-// dΓ dA uΓ in
    pairStr→ sf _ _ refl _ refl _ dmorTmₛ refl _ dmorTmₛ refl
    ∙ ap-irr-pairStr uΓ
                     uΓA
                     (uniqueness-Ty-// (dΓ , dA) dB uΓA)
                     (uniqueness-Tm-// dΓ da uΓ)
                     (uniqueness-Tm-// dΓ db uΓ)
    ∙ ! (pairStr→ sg _ _ refl _ refl _ dmorTmₛ refl _ dmorTmₛ refl)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = pr1 A B u} (Pr1 dA dB du) uΓ =
    let uΓA = uniqueness-Ty-// dΓ dA uΓ in
    pr1Str→ sf _ _ refl _ refl _ dmorTmₛ refl
    ∙ ap-irr-pr1Str uΓ
                    uΓA
                    (uniqueness-Ty-// (dΓ , dA) dB uΓA)
                    (uniqueness-Tm-// dΓ du uΓ)
    ∙ ! (pr1Str→ sg _ _ refl _ refl _ dmorTmₛ refl)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = pr2 A B u} (Pr2 dA dB du) uΓ =
    let uΓA = uniqueness-Ty-// dΓ dA uΓ in
    pr2Str→ sf _ _ refl _ refl _ dmorTmₛ refl
    ∙ ap-irr-pr2Str uΓ
                    uΓA
                    (uniqueness-Ty-// (dΓ , dA) dB uΓA)
                    (uniqueness-Tm-// dΓ du uΓ)
    ∙ ! (pr2Str→ sg _ _ refl _ refl _ dmorTmₛ refl)

  uniqueness-Tm-// {Γ = Γ} dΓ {u = empty i} EmptyUU uΓ =
    emptyStr→ sf i _
    ∙ ap (emptyStr sC i) uΓ
    ∙ ! (emptyStr→ sg i _)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = emptyelim A u} (Emptyelim dA du) uΓ =
    emptyelimStr→ sf _ _ refl _ dmorTmₛ refl
    ∙ ap-irr-emptyelimStr uΓ
                          (uniqueness-Ty-// (dΓ , Empty) dA (uniqueness-Ty-// dΓ Empty uΓ))
                          (uniqueness-Tm-// dΓ du uΓ)
    ∙ ! (emptyelimStr→ sg _ _ refl _ dmorTmₛ refl)
  
  uniqueness-Tm-// {Γ = Γ} dΓ {u = unit i} UnitUU uΓ =
    unitStr→ sf i _
    ∙ ap (unitStr sC i) uΓ
    ∙ ! (unitStr→ sg i _)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = tt} TT uΓ =
    ttStr→ sf _
    ∙ ap (ttStr sC) uΓ
    ∙ ! (ttStr→ sg _)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = unitelim A dtt u} (Unitelim dA ddtt du) uΓ =
    unitelimStr→ sf _ _ refl _ dmorTmₛ refl _ dmorTmₛ refl
    ∙ ap-irr-unitelimStr uΓ
                         (uniqueness-Ty-// (dΓ , Unit) dA (uniqueness-Ty-// dΓ Unit uΓ))
                         (uniqueness-Tm-// dΓ ddtt uΓ)
                         (uniqueness-Tm-// dΓ du uΓ)
    ∙ ! (unitelimStr→ sg _ _ refl _ dmorTmₛ refl _ dmorTmₛ refl)
    
  uniqueness-Tm-// {Γ = Γ} dΓ {u = nat i} NatUU uΓ =
    natStr→ sf i _
    ∙ ap (natStr sC i) uΓ
    ∙ ! (natStr→ sg i _)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = zero} Zero uΓ =
    zeroStr→ sf _
    ∙ ap (zeroStr sC) uΓ
    ∙ ! (zeroStr→ sg _)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = suc u} (Suc du) uΓ =
    sucStr→ sf _ _ dmorTmₛ refl
    ∙ ap-irr-sucStr sC uΓ
                       (uniqueness-Tm-// dΓ du uΓ)
    ∙ ! (sucStr→ sg _ _ dmorTmₛ refl)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = natelim P dO dS u} (Natelim dP ddO ddS du) uΓ =
    natelimStr→ sf+ _ _ refl _ dmorTmₛ refl _ dmorTmₛ refl _ dmorTmₛ refl
    ∙ ap-irr-natelimStr uΓ
                        (uniqueness-Ty-// (dΓ , Nat) dP (uniqueness-Ty-// dΓ Nat uΓ))
                        (uniqueness-Tm-// dΓ ddO uΓ)
                        (uniqueness-Tm-// ((dΓ , Nat) , dP) (congTmTy fixSubstTy ddS) (uniqueness-Ty-// (dΓ , Nat) dP (uniqueness-Ty-// dΓ Nat uΓ)))
                        (uniqueness-Tm-// dΓ du uΓ)
    ∙ ! (natelimStr→ sg+ _ _ refl _ dmorTmₛ refl _ dmorTmₛ refl _ dmorTmₛ refl)

  uniqueness-Tm-// {Γ = Γ} dΓ {u = id i a u v} (IdUU da du dv) uΓ =
    idStr→ sf i _ _ dmorTmₛ refl _ dmorTmₛ refl _ dmorTmₛ refl
    ∙ ap-irr-idStr uΓ
                   (uniqueness-Tm-// dΓ da uΓ)
                   (uniqueness-Tm-// dΓ du uΓ)
                   (uniqueness-Tm-// dΓ dv uΓ)
    ∙ ! (idStr→ sg i _ _ dmorTmₛ refl _ dmorTmₛ refl _ dmorTmₛ refl)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = refl A u} (Refl dA du) uΓ =
    reflStr→ sf _ _ refl _ dmorTmₛ refl
    ∙ ap-irr-reflStr sC uΓ
                        (uniqueness-Ty-// dΓ dA uΓ)
                        (uniqueness-Tm-// dΓ du uΓ)
    ∙ ! (reflStr→ sg _ _ refl _ dmorTmₛ refl)
  uniqueness-Tm-// {Γ = Γ} dΓ {u = jj A P d a b p} (JJ dA dP dd da db dp) uΓ =
    let uΓA = uniqueness-Ty-// dΓ dA uΓ in
    let uΓAwA = uniqueness-Ty-//-Weak dΓ dA dA uΓ uΓA uΓA in
    let dwA = SubstTy dA (WeakMor (idMorDerivable dΓ)) in
    let dwwA = SubstTy dwA ((WeakMor (WeakMor (idMorDerivable dΓ))) , congTmTy (ap weakenTy weakenTy-to-[]Ty ∙ weaken[]Ty _ _ last) (VarPrevLast dA)) in
    let dvpl = congTmTy (ap weakenTy weakenTy-to-[]Ty ∙ weakenTy-to-[]Ty) (VarPrevLast dA) in
    let dvl = congTmTy weakenTy-to-[]Ty (VarLast dwA) in
    let did = Id dwwA dvpl dvl in
    let dP' = congTyCtx (Ctx+= (Ctx+= refl weakenTy-to-[]Ty) (ap-id-Ty (ap weakenTy weakenTy-to-[]Ty ∙ weakenTy-to-[]Ty) refl refl)) dP in
    jjStr→ sf+ (proj (dctx dΓ)) (proj (dctx (dΓ , dA))) refl
                                (proj (dctx {ctx = ((((_ , _) , _) , _) , _)} ((((dΓ , dA) , dwA) , did) , dP'))) refl
                                (proj (dmor (dctx {ctx = (_ , _)} (dΓ , dA)) (dctx {ctx = ((_ , _) , _)} ((dΓ , dA) , DerTmTy (dΓ , dA) (congTmTy fixTyJJ dd))) {mor = (idMor _ , d)} (idMor+ (dΓ , dA) (congTmTy fixTyJJ dd)))) dmorTmₛ refl
                                (proj (dmor (dctx {ctx = Γ} dΓ) (dctx {ctx = (_ , _)} (dΓ , dA)) {mor = (idMor _ , a)} (idMor+ dΓ da))) dmorTmₛ refl
                                (proj (dmor (dctx {ctx = Γ} dΓ) (dctx {ctx = (_ , _)} (dΓ , dA)) {mor = (idMor _ , b)} (idMor+ dΓ db))) dmorTmₛ refl
                                (proj (dmor (dctx {ctx = Γ} dΓ) (dctx {ctx = (_ , _)} (dΓ , Id dA da db)) {mor = (idMor _ , p)} (idMor+ dΓ dp))) dmorTmₛ refl
    ∙ ap-irr-jjStr uΓ
                   uΓA
                   (uniqueness-Ty-// (((dΓ , dA) , dwA) , did) dP'
                     (uniqueness-Ty-//-Id ((dΓ , dA) , dwA) dwwA dvpl dvl uΓAwA
                       (uniqueness-Ty-//-Weak (dΓ , dA) dwA dwA uΓA uΓAwA uΓAwA)
                       (uniqueness-Tm-//-Var ((dΓ , dA) , dwA) (prev last) uΓAwA (ap weakenTy weakenTy-to-[]Ty ∙ weakenTy-to-[]Ty))
                       (uniqueness-Tm-//-Var ((dΓ , dA) , dwA) last uΓAwA weakenTy-to-[]Ty)))
                   (uniqueness-Tm-// (dΓ , dA) (congTmTy fixTyJJ dd) uΓA)
                   (uniqueness-Tm-// dΓ da uΓ)
                   (uniqueness-Tm-// dΓ db uΓ)
                   (uniqueness-Tm-// dΓ dp uΓ)
    ∙ ! (jjStr→ sg+ _ (proj (dctx (dΓ , dA))) refl
                      (proj (dctx {ctx = ((((_ , _) , _) , _) , _)} ((((dΓ , dA) , dwA) , did) , dP'))) refl
                      (proj (dmor (dctx {ctx = (_ , _)} (dΓ , dA)) (dctx {ctx = ((_ , _) , _)} ((dΓ , dA) , DerTmTy (dΓ , dA) (congTmTy fixTyJJ dd))) {mor = (idMor _ , d)} (idMor+ (dΓ , dA) (congTmTy fixTyJJ dd)))) dmorTmₛ refl
                      (proj (dmor (dctx {ctx = Γ} dΓ) (dctx {ctx = (_ , _)} (dΓ , dA)) {mor = (idMor _ , a)} (idMor+ dΓ da))) dmorTmₛ refl
                      (proj (dmor (dctx {ctx = Γ} dΓ) (dctx {ctx = (_ , _)} (dΓ , dA)) {mor = (idMor _ , b)} (idMor+ dΓ db))) dmorTmₛ refl
                      (proj (dmor (dctx {ctx = Γ} dΓ) (dctx {ctx = (_ , _)} (dΓ , Id dA da db)) {mor = (idMor _ , p)} (idMor+ dΓ dp))) dmorTmₛ refl)

  uniqueness-Ob : (X : ObS n) → Ob→ f X ≡ Ob→ g X
  uniqueness-Ob = //-elimP uniqueness-Ob-//

  uniqueness-Mor-// : (δ : DMor n m) → Mor→ f (proj δ) ≡ Mor→ g (proj δ)
  uniqueness-Mor-// (dmor' (dctx' dΓ) (dctx' {ctx = ◇} tt) {mor = ◇} tt) = ptmor→ f {X = proj (dctx dΓ)} ∙ ap ptmor (uniqueness-Ob-// (dctx dΓ)) ∙ ! (ptmor→ g)
  uniqueness-Mor-// δδ@(dmor' (dctx' dΓ) (dctx' {ctx = Δ , C} (dΔ , dC)) {mor = (δ , u)} (dδ , du)) =
    ap (Mor→ f) (ap proj (! (split-comp δδ)))
    ∙ comp→ f {g = proj (split-right δδ)} {f = proj (split-left δδ)} {g₀ = refl} {f₁ = refl}
    ∙ ap-irr-comp (qq→ f {f = proj (dmor (dctx dΓ) (dctx dΔ) dδ)} {X = proj (dctx (dΔ , dC))} {q = refl} {f₁ = refl}
                  ∙ ap-irr-qq (uniqueness-Mor-// (dmor (dctx dΓ) (dctx dΔ) dδ)) (uniqueness-Ob-// (dctx (dΔ , dC)))
                  ∙ ! (qq→ g {f = proj (dmor (dctx dΓ) (dctx dΔ) dδ)} {X = proj (dctx (dΔ , dC))} {q = refl} {f₁ = refl}))
                  (uniqueness-Tm-// dΓ du (uniqueness-Ob-// (dctx dΓ)))
    ∙ ! (comp→ g {g = proj (split-right δδ)} {f = proj (split-left δδ)} {g₀ = refl} {f₁ = refl})
    ∙ ! (ap (Mor→ g) (ap proj (! (split-comp δδ))))

  uniqueness-Mor : (X : MorS n m) → Mor→ f X ≡ Mor→ g X
  uniqueness-Mor = //-elimP uniqueness-Mor-//

  uniqueness : sf ≡ sg
  uniqueness = structuredCCatMorEq uniqueness-Ob uniqueness-Mor

  uniqueness+ : sf+ ≡ sg+
  uniqueness+ = structuredCCatMor+Eq uniqueness-Ob uniqueness-Mor
