{-# OPTIONS --irrelevant-projections #-}

open import common
open import contextualcat

{- Syntax of term- and type-expressions, using de Bruijn indices -}

data Fin : ℕ → Set where
  last : Fin (suc n)
  prev : Fin n → Fin (suc n)

data TyExpr : ℕ → Set
data TmExpr : ℕ → Set

data TyExpr where
  pi : TyExpr n → TyExpr (suc n) → TyExpr n
  uu : TyExpr n
  el : TmExpr n → TyExpr n

data TmExpr where
  var : Fin n → TmExpr n
  lam : TyExpr n → TyExpr (suc n) → TmExpr (suc n) → TmExpr n
  app : TyExpr n → TyExpr (suc n) → TmExpr n → TmExpr n → TmExpr n

{- Weakening -}

weakenTy : TyExpr n → TyExpr (suc n)
weakenTm : TmExpr n → TmExpr (suc n)

weakenTy (pi A B) = pi (weakenTy A) (weakenTy B)
weakenTy uu = uu
weakenTy (el v) = el (weakenTm v)

weakenTm (var x) = var (prev x)
weakenTm (lam A B u) = lam (weakenTy A) (weakenTy B) (weakenTm u)
weakenTm (app A B f a) = app (weakenTy A) (weakenTy B) (weakenTm f) (weakenTm a)

{- Substitution -}

substTy : TyExpr (suc m + n) → TmExpr n → TyExpr (m + n)
substTm : TmExpr (suc m + n) → TmExpr n → TmExpr (m + n)
substVar : Fin (suc m + n) → TmExpr n → TmExpr (m + n)

substTy (pi A B) u = pi (substTy A u) (substTy B u)
substTy uu u = uu
substTy (el v) u = el (substTm v u)

substTm (var x) u = substVar x u
substTm (lam A B v) u = lam (substTy A u) (substTy B u) (substTm v u)
substTm (app A B f a) u = app (substTy A u) (substTy B u) (substTm f u) (substTm a u)

substVar {m = zero}  last u = u
substVar {m = suc m} last u = var last
substVar {m = zero}  (prev x) u = var x
substVar {m = suc m} (prev x) u = weakenTm (substVar x u)

{- Contexts and context morphisms -}

data Ctx : Set
lenCtx : Ctx → ℕ

data Ctx where
  ◇ : Ctx
  _,_ : (Γ : Ctx) → TyExpr (lenCtx Γ) → Ctx

lenCtx ◇ = 0
lenCtx (Γ , A) = suc (lenCtx Γ)


data Mor (n : ℕ) : Set where
  ◇ : Mor n
  _,_ : Mor n → TmExpr n → Mor n

lenMor : {n : ℕ} → Mor n → ℕ
lenMor ◇ = 0
lenMor (δ , u) = suc (lenMor δ)


weakenMor : Mor n → Mor (suc n)
weakenMor ◇ = ◇
weakenMor (δ , u) = (weakenMor δ , weakenTm u)

lenWeakenMor : {δ : Mor n} → lenMor (weakenMor δ) ≡ lenMor δ
lenWeakenMor {δ = ◇} = refl
lenWeakenMor {δ = δ , u} = ap suc lenWeakenMor

{- Total substitutions -}

totalSubstTy : {n m : ℕ} → TyExpr n → (δ : Mor m) → lenMor δ ≡ n → TyExpr m
totalSubstTm : {n m : ℕ} → TmExpr n → (δ : Mor m) → lenMor δ ≡ n → TmExpr m

totalSubstTy (pi A B) δ refl = pi (totalSubstTy A δ refl) (totalSubstTy B (weakenMor δ , var last) (ap suc lenWeakenMor))
totalSubstTy uu δ refl = uu
totalSubstTy (el v) δ refl = el (totalSubstTm v δ refl)

totalSubstTm (var last) ◇ ()
totalSubstTm (var last) (δ , u) p = u
totalSubstTm (var (prev x)) ◇ ()
totalSubstTm (var (prev x)) (δ , u) refl = totalSubstTm (var x) δ refl
totalSubstTm (lam A B u) δ refl = lam (totalSubstTy A δ refl)
                                      (totalSubstTy B (weakenMor δ , var last) (ap suc lenWeakenMor))
                                      (totalSubstTm u (weakenMor δ , var last) (ap suc lenWeakenMor))
totalSubstTm (app A B f a) δ refl = app (totalSubstTy A δ refl) (totalSubstTy B (weakenMor δ , var last) (ap suc lenWeakenMor)) (totalSubstTm f δ refl) (totalSubstTm a δ refl)

{- The different forms of (pre)judgments. Maybe the judgments for contexts and context morphisms could be defined later. -}
data Judgment : Set where
  ⊢_ : Ctx → Judgment

  _⊢_ : (Γ : Ctx) → TyExpr (lenCtx Γ) → Judgment
  _⊢_:>_ : (Γ : Ctx) → TmExpr (lenCtx Γ) → TyExpr (lenCtx Γ) → Judgment
  _⊢_∷>_ : (Γ : Ctx) → Mor (lenCtx Γ) → Ctx → Judgment

  _⊢_==_ : (Γ : Ctx) → TyExpr (lenCtx Γ) → TyExpr (lenCtx Γ) → Judgment
  _⊢_==_:>_ : (Γ : Ctx) → TmExpr (lenCtx Γ) → TmExpr (lenCtx Γ) → TyExpr (lenCtx Γ) → Judgment
  _⊢_==_∷>_ : (Γ : Ctx) → Mor (lenCtx Γ) → Mor (lenCtx Γ) → Ctx → Judgment


data _∋_:>_ : (Γ : Ctx) → Fin (lenCtx Γ) → TyExpr (lenCtx Γ) → Set where
  last : {Γ : Ctx} {A : TyExpr (lenCtx Γ)} → (Γ , A) ∋ last :> weakenTy A
  prev : {Γ : Ctx} {x : Fin (lenCtx Γ)} {A B : TyExpr (lenCtx Γ)} → (Γ ∋ x :> A) → (Γ , B) ∋ prev x :> weakenTy A

{- Derivability of judgments, the typing rules of the type theory -}

data Derivable : Judgment → Set where

  -- Variable rule
  VarRule : {Γ : Ctx} {x : Fin (lenCtx Γ)} {A : TyExpr (lenCtx Γ)}
          → (Γ ∋ x :> A) → Derivable (⊢ Γ) → Derivable (Γ ⊢ var x :> A)

  -- Congruence for variables
  VarCong : {Γ : Ctx} {x : Fin (lenCtx Γ)} {A : TyExpr (lenCtx Γ)}
          → (Γ ∋ x :> A) → Derivable (⊢ Γ) → Derivable (Γ ⊢ var x == var x :> A)

  -- Symmetry and transitivity for types
  TySymm : {Γ : Ctx} {A B : TyExpr (lenCtx Γ)}
         → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B == A)
  TyTran : {Γ : Ctx} {A B C : TyExpr (lenCtx Γ)}
         → Derivable (Γ ⊢ A == B)→ Derivable (Γ ⊢ B == C) → Derivable (Γ ⊢ A == C)

  -- Symmetry and transitivity for terms
  TmSymm : {Γ : Ctx} {u v : TmExpr (lenCtx Γ)} {A : TyExpr (lenCtx Γ)}
         → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ v == u :> A)
  TmTran : {Γ : Ctx} {u v w : TmExpr (lenCtx Γ)} {A : TyExpr (lenCtx Γ)}
         → Derivable (Γ ⊢ u == v :> A)→ Derivable (Γ ⊢ v == w :> A) → Derivable (Γ ⊢ u == w :> A)

  -- Conversion rule
  Conv : {Γ : Ctx} {u : TmExpr (lenCtx Γ)} {A B : TyExpr (lenCtx Γ)}
       → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u :> B)
  ConvEq : {Γ : Ctx} {u u' : TmExpr (lenCtx Γ)} {A B : TyExpr (lenCtx Γ)}
       → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u == u' :> B)

  -- Formation rules for contexts
  EmpCtx : Derivable (⊢ ◇)
  ExtCtx : {Γ : Ctx} {A : TyExpr (lenCtx Γ)}
         → Derivable (⊢ Γ) → Derivable (Γ ⊢ A) → Derivable (⊢ (Γ , A))

  -- Formation rules for context morphisms
  EmpMor : {Γ : Ctx}
         → Derivable (⊢ Γ) → Derivable (Γ ⊢ ◇ ∷> ◇)
  ExtMor : {Γ Δ : Ctx} {A : TyExpr (lenCtx Δ)} {u : TmExpr (lenCtx Γ)} {δ : Mor (lenCtx Γ)} {p : lenMor δ ≡ lenCtx Δ}
         → Derivable (Γ ⊢ δ ∷> Δ) → Derivable (Δ ⊢ A) → Derivable (Γ ⊢ u :> totalSubstTy A δ p) → Derivable (Γ ⊢ (δ , u) ∷> (Δ , A))

  -- Formation rules for context morphism equality
  EmpMorEq : {Γ : Ctx}
           → Derivable (⊢ Γ) → Derivable (Γ ⊢ ◇ == ◇ ∷> ◇)
  ExtMorEq : {Γ Δ : Ctx} {A : TyExpr (lenCtx Δ)} {u u' : TmExpr (lenCtx Γ)} {δ δ' : Mor (lenCtx Γ)} {p : lenMor δ ≡ lenCtx Δ}
           → Derivable (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Δ ⊢ A) → Derivable (Γ ⊢ u == u' :> totalSubstTy A δ p) → Derivable (Γ ⊢ (δ , u) == (δ' , u') ∷> (Δ , A))

  -- Rules for Pi
  Pi : {Γ : Ctx} {A : TyExpr (lenCtx Γ)} {B : TyExpr (suc (lenCtx Γ))} 
     → Derivable (⊢ Γ) → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ pi A B)
  PiCong : {Γ : Ctx} {A A' : TyExpr (lenCtx Γ)} {B B' : TyExpr (suc (lenCtx Γ))} 
     → Derivable (⊢ Γ) → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ pi A B == pi A' B')

  -- Rules for lambda
  Lam : {Γ : Ctx} {A : TyExpr (lenCtx Γ)} {B : TyExpr (suc (lenCtx Γ))} {u : TmExpr (suc (lenCtx Γ))}
      → Derivable (⊢ Γ) → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ lam A B u :> pi A B)
  LamCong : {Γ : Ctx} {A A' : TyExpr (lenCtx Γ)} {B B' : TyExpr (suc (lenCtx Γ))} {u u' : TmExpr (suc (lenCtx Γ))}
      → Derivable (⊢ Γ) → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable ((Γ , A) ⊢ u == u' :> B) → Derivable (Γ ⊢ lam A B u == lam A' B' u' :> pi A B)

  -- Rules for app
  App : {Γ : Ctx} {A : TyExpr (lenCtx Γ)} {B : TyExpr (suc (lenCtx Γ))} {f a : TmExpr (lenCtx Γ)}
      → Derivable (⊢ Γ) → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ f :> pi A B) → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ app A B f a :> substTy B a)
  AppCong : {Γ : Ctx} {A A' : TyExpr (lenCtx Γ)} {B B' : TyExpr (suc (lenCtx Γ))} {f f' a a' : TmExpr (lenCtx Γ)}
      → Derivable (⊢ Γ) → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ f == f' :> pi A B) → Derivable (Γ ⊢ a == a' :> A) → Derivable (Γ ⊢ app A B f a == app A' B' f' a' :> substTy B a)

  Beta : {Γ : Ctx} {A : TyExpr (lenCtx Γ)} {B : TyExpr (suc (lenCtx Γ))} {u : TmExpr (suc (lenCtx Γ))} {a : TmExpr (lenCtx Γ)}
       → Derivable (⊢ Γ) → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ a :> A)
       → Derivable (Γ ⊢ app A B (lam A B u) a == substTm u a :> substTy B a)

  -- Rules for UU
  UU : {Γ : Ctx}
     → Derivable (⊢ Γ) → Derivable (Γ ⊢ uu)
  UUCong : {Γ : Ctx}
     → Derivable (⊢ Γ) → Derivable (Γ ⊢ uu == uu)

  -- Rules for El
  El : {Γ : Ctx} {v : TmExpr (lenCtx Γ)}
     → Derivable (⊢ Γ) → Derivable (Γ ⊢ v :> uu) → Derivable (Γ ⊢ el v)
  ElCong : {Γ : Ctx} {v v' : TmExpr (lenCtx Γ)}
     → Derivable (⊢ Γ) → Derivable (Γ ⊢ v == v' :> uu) → Derivable (Γ ⊢ el v == el v')
