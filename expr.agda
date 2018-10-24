{-# OPTIONS --irrelevant-projections --type-in-type --rewriting #-}

open import common
open import contextualcat
open import quotients

open CCat hiding (Mor)

{- Syntax of term- and type-expressions, using de Bruijn indices -}

data TyExpr : ℕ → Set
data TmExpr : ℕ → Set

data TyExpr where
  pi : (A : TyExpr n) (B : TyExpr (suc n)) → TyExpr n
  uu : TyExpr n
  el : (v : TmExpr n) → TyExpr n

data TmExpr where
  var : (x : Fin n) → TmExpr n
  lam : (A : TyExpr n) (B : TyExpr (suc n)) (u : TmExpr (suc n)) → TmExpr n
  app : (A : TyExpr n) (B : TyExpr (suc n)) (f : TmExpr n) (a : TmExpr n) → TmExpr n

{- Renaming -}

extendRen : (Fin n → Fin m) → (Fin (suc n) → Fin (suc m))
extendRen r last = last
extendRen r (prev k) = prev (r k)

renameTy : (r : Fin n → Fin m) → TyExpr n → TyExpr m
renameTm : (r : Fin n → Fin m) → TmExpr n → TmExpr m

renameTy r (pi A B) = pi (renameTy r A) (renameTy (extendRen r) B)
renameTy r uu = uu
renameTy r (el v) = el (renameTm r v)

renameTm r (var x) = var (r x)
renameTm r (lam A B u) = lam (renameTy r A) (renameTy (extendRen r) B) (renameTm (extendRen r) u)
renameTm r (app A B f a) = app (renameTy r A) (renameTy (extendRen r) B) (renameTm r f) (renameTm r a)

injF : Fin (suc n) → (Fin n → Fin (suc n))
injF last = prev
injF {n = suc n} (prev k) = extendRen (injF k)

weakenTy : TyExpr n → TyExpr (suc n)
weakenTy = renameTy prev

weakenTm : TmExpr n → TmExpr (suc n)
weakenTm = renameTm prev

weakenTy' : (k : Fin (suc n)) → TyExpr n → TyExpr (suc n)
weakenTy' k = renameTy (injF k)

weakenTm' : (k : Fin (suc n)) → TmExpr n → TmExpr (suc n)
weakenTm' k = renameTm (injF k)

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

data Ctx : ℕ → Set where
  ◇ : Ctx 0
  _,_ : {n : ℕ} (Γ : Ctx n) → TyExpr n → Ctx (suc n)

data Mor (n : ℕ) : ℕ → Set where
  ◇ : Mor n 0
  _,_ : {m : ℕ} → Mor n m → TmExpr n → Mor n (suc m)


renameMor : (r : Fin n → Fin n') → Mor n m → Mor n' m
renameMor r ◇ = ◇
renameMor r (δ , u) = (renameMor r δ , renameTm r u)

weakenMor : Mor n m → Mor (suc n) m
weakenMor = renameMor prev

weakenMor' : (k : Fin (suc n)) → Mor n m → Mor (suc n) m
weakenMor' k = renameMor (injF k)

{- Total substitutions -}

infix 42 _[_]Ty
infix 42 _[_]Tm

_[_]Ty : {n m : ℕ} → TyExpr n → (δ : Mor m n) → TyExpr m
_[_]Tm : {n m : ℕ} → TmExpr n → (δ : Mor m n) → TmExpr m

pi A B [ δ ]Ty = pi (A [ δ ]Ty) (B [ (weakenMor δ , var last) ]Ty)
uu [ δ ]Ty = uu
el v [ δ ]Ty = el (v [ δ ]Tm)

var last [ (δ , u) ]Tm = u
var (prev x) [ (δ , u) ]Tm = var x [ δ ]Tm
lam A B u [ δ ]Tm = lam (A [ δ ]Ty) (B [ (weakenMor δ , var last) ]Ty) (u [ (weakenMor δ , var last) ]Tm)
app A B f a [ δ ]Tm = app (A [ δ ]Ty) (B [ (weakenMor δ , var last) ]Ty) (f [ δ ]Tm) (a [ δ ]Tm)

_[_]Mor : {n m k : ℕ} → Mor n k → (δ : Mor m n) → Mor m k
◇ [ δ ]Mor = ◇
(γ , u) [ δ ]Mor = (γ [ δ ]Mor , u [ δ ]Tm)

{- The different forms of (pre)judgments. Maybe the judgments for contexts and context morphisms could be defined later. -}
data Judgment : Set where
  _⊢_ : (Γ : Ctx n) → TyExpr n → Judgment
  _⊢_:>_ : (Γ : Ctx n) → TmExpr n → TyExpr n → Judgment
  _⊢_==_ : (Γ : Ctx n) → TyExpr n → TyExpr n → Judgment
  _⊢_==_:>_ : (Γ : Ctx n) → TmExpr n → TmExpr n → TyExpr n → Judgment


data _∋_:>_ : {n : ℕ} (Γ : Ctx n) → Fin n → TyExpr n → Set where
  last : {Γ : Ctx n} {A : TyExpr n} → (Γ , A) ∋ last :> weakenTy A
  prev : {Γ : Ctx n} {x : Fin n} {A B : TyExpr n} → (Γ ∋ x :> A) → (Γ , B) ∋ prev x :> weakenTy A

{- Derivability of judgments, the typing rules of the type theory -}
data Derivable : Judgment → Set

⊢_ : Ctx n → Set
⊢ ◇ = Unit
⊢ (Γ , A) = (⊢ Γ) × Derivable (Γ ⊢ A)

⊢_==_ : Ctx n → Ctx n → Set
⊢ ◇ == ◇ = Unit
⊢ (Γ , A) == (Γ' , A') = (⊢ Γ == Γ') ×' Derivable (Γ ⊢ A == A')

_⊢_∷>_ : (Γ : Ctx n) → Mor n m → Ctx m → Set
Γ ⊢ ◇ ∷> ◇ = Unit
Γ ⊢ (δ , u) ∷> (Δ , A) = (Γ ⊢ δ ∷> Δ) × Derivable (Γ ⊢ u :> A [ δ ]Ty)

_⊢_==_∷>_ : (Γ : Ctx n) → Mor n m → Mor n m → Ctx m → Set
Γ ⊢ ◇ == ◇ ∷> ◇ = Unit
Γ ⊢ (δ , u) == (δ' , u') ∷> (Δ , A) = (Γ ⊢ δ == δ' ∷> Δ) × Derivable (Γ ⊢ u == u' :> A [ δ ]Ty)

data Derivable where

  -- Variable rule
  VarRule : {Γ : Ctx n} {x : Fin n} {A : TyExpr n}
          → (Γ ∋ x :> A) → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ var x :> A)

  -- Congruence for variables
  VarCong : {Γ : Ctx n} {x : Fin n} {A : TyExpr n}
          → (Γ ∋ x :> A) → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ var x == var x :> A)

  -- Symmetry and transitivity for types
  TySymm : {Γ : Ctx n} {A B : TyExpr n}
         → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B == A)
  TyTran : {Γ : Ctx n} {A B C : TyExpr n}
         → Derivable (Γ ⊢ A == B)→ Derivable (Γ ⊢ B == C) → Derivable (Γ ⊢ A == C)

  -- Symmetry and transitivity for terms
  TmSymm : {Γ : Ctx n} {u v : TmExpr n} {A : TyExpr n}
         → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ v == u :> A)
  TmTran : {Γ : Ctx n} {u v w : TmExpr n} {A : TyExpr n}
         → Derivable (Γ ⊢ u == v :> A)→ Derivable (Γ ⊢ v == w :> A) → Derivable (Γ ⊢ u == w :> A)

  -- Conversion rule
  Conv : {Γ : Ctx n} {u : TmExpr n} {A B : TyExpr n}
       → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u :> B)
  ConvEq : {Γ : Ctx n} {u u' : TmExpr n} {A B : TyExpr n}
       → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u == u' :> B)

  -- Substitution rules
  SubstTy : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ A) → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty)
  SubstTm : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ u :> A) → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm :> A [ δ ]Ty)
  SubstTyEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ ]Ty)
  SubstTmEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u' [ δ ]Tm :> A [ δ ]Ty)
  SubstTySubstEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m}
       → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
  SubstTmSubstEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m}
       → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u' [ δ' ]Tm :> A [ δ' ]Ty)

  -- Rules for Pi
  Pi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} 
     → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ pi A B)
  PiCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} 
     → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ pi A B == pi A' B')

  -- Rules for lambda
  Lam : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)}
      → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ lam A B u :> pi A B)
  LamCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr (suc n)}
      → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable ((Γ , A) ⊢ u == u' :> B) → Derivable (Γ ⊢ lam A B u == lam A' B' u' :> pi A B)

  -- Rules for app
  App : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f a : TmExpr n}
      → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ f :> pi A B) → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ app A B f a :> substTy B a)
  AppCong : {n : ℕ} {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {f f' a a' : TmExpr n}
      → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ f == f' :> pi A B) → Derivable (Γ ⊢ a == a' :> A) → Derivable (Γ ⊢ app A B f a == app A' B' f' a' :> substTy B a)

  -- Beta-reduction
  Beta : {n : ℕ} {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)} {a : TmExpr n}
       → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ a :> A)
       → Derivable (Γ ⊢ app A B (lam A B u) a == substTm u a :> substTy B a)

  -- Rules for UU
  UU : {Γ : Ctx n}
     → Derivable (Γ ⊢ uu)
  UUCong : {Γ : Ctx n}
     → Derivable (Γ ⊢ uu == uu)

  -- Rules for El
  El : {Γ : Ctx n} {v : TmExpr n}
     → Derivable (Γ ⊢ v :> uu) → Derivable (Γ ⊢ el v)
  ElCong : {Γ : Ctx n} {v v' : TmExpr n}
     → Derivable (Γ ⊢ v == v' :> uu) → Derivable (Γ ⊢ el v == el v')


.SubstMor : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ : Mor m k} {δ : Mor n m}
     → (Δ ⊢ θ ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ θ [ δ ]Mor ∷> Θ)
SubstMor {Θ = ◇} {θ = ◇} tt dδ = tt
SubstMor {Θ = Θ , C} {θ = θ , w} (dθ , dw) dδ = (SubstMor dθ dδ , {!SubstTm dw dδ!})

TyRefl : {Γ : Ctx n} {A : TyExpr n} → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A)
TmRefl : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u == u :> A)

TyRefl (SubstTy dA dδ) = SubstTyEq (TyRefl dA) dδ
TyRefl (Pi dA dB) = PiCong (TyRefl dA) (TyRefl dB)
TyRefl UU = UUCong
TyRefl (El dv) = ElCong (TmRefl dv)

TmRefl (VarRule x∈ dA) = VarCong x∈ dA
TmRefl (Conv du dA=) = ConvEq (TmRefl du) dA=
TmRefl (SubstTm du dδ) = SubstTmEq (TmRefl du) dδ
TmRefl (Lam dA dB du) = LamCong (TyRefl dA) (TyRefl dB) (TmRefl du)
TmRefl (App dA dB df da) = AppCong (TyRefl dA) (TyRefl dB) (TmRefl df) (TmRefl da)

ConvTyEq : {Γ Δ : Ctx n} {A B : TyExpr n} → Derivable (Γ ⊢ A == B) → (⊢ Γ == Δ) → Derivable (Δ ⊢ A == B)
ConvTyEq dA= dΓ= = {!!}

ConvMorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} → (Γ ⊢ δ == δ' ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ == δ' ∷> Δ')
ConvMorEq dδ= dΓ= dΔ= = {!!}

CtxRefl : {Γ : Ctx n} → ⊢ Γ → ⊢ Γ == Γ
CtxRefl {Γ = ◇} tt = tt
CtxRefl {Γ = Γ , A} (dΓ , dA) = (CtxRefl dΓ , TyRefl dA)

CtxSymm : {Γ Δ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Γ
CtxSymm {Γ = ◇} {Δ = ◇} tt = tt
CtxSymm {Γ = Γ , A} {Δ , B} (dΓ= , dA=) = (CtxSymm dΓ= , ConvTyEq (TySymm dA=) dΓ=)

CtxTran : {Γ Δ Θ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Θ → ⊢ Γ == Θ
CtxTran {Γ = ◇} {Δ = ◇} {Θ = ◇} tt tt = tt
CtxTran {Γ = Γ , A} {Δ , B} {Θ , C} (dΓ= , dA=) (dΔ= , dB=) = (CtxTran dΓ= dΔ= , TyTran dA= (ConvTyEq dB= (CtxSymm dΓ=)))

MorRefl : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} → Γ ⊢ δ ∷> Δ → Γ ⊢ δ == δ ∷> Δ
MorRefl {Δ = ◇} {◇} tt = tt
MorRefl {Δ = Δ , B} {δ , u} (dδ , du) = (MorRefl dδ , TmRefl du)

MorSymm : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ ∷> Δ
MorSymm {Δ = ◇} {◇} {◇} _ tt = tt
MorSymm {Δ = Δ , B} {δ , u} {δ' , u'} (dΔ , dB) (dδ , du) = (MorSymm dΔ dδ) , (ConvEq (TmSymm du) (SubstTySubstEq (TyRefl dB) dδ))

MorTran : {Γ : Ctx n} {Δ : Ctx m} {δ δ' δ'' : Mor n m} → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ'' ∷> Δ → Γ ⊢ δ == δ'' ∷> Δ
MorTran {Δ = ◇} {◇} {◇} {◇} _ tt tt = tt
MorTran {Δ = Δ , B} {δ , u} {δ' , u'} {δ'' , u''} (dΔ , dB) (dδ , du) (dδ' , du') = (MorTran dΔ dδ dδ') , TmTran du (ConvEq du' (SubstTySubstEq (TyRefl dB) (MorSymm dΔ dδ)))

record DCtx (n : ℕ) : Set where
  constructor _,_
  field
    fst : Ctx n
    .snd : (⊢ fst)
open DCtx

DMor : ℕ → ℕ → Set
DMor n m = Σ (DCtx n × DCtx m) (λ {((Γ , _) , (Δ , _)) → Σ' (Mor n m) (λ δ → (Γ ⊢ δ ∷> Δ))})

{- Messy failed attempts to prove stuff about weakening -}

⟨_⟩ : {n : ℕ} → Fin n → ℕ
⟨ last ⟩ = 0
⟨ prev k ⟩ = suc ⟨ k ⟩

weakenCtx' : {n : ℕ} (k : Fin (suc n)) (Γ : Ctx n) (A : TyExpr (n -F k)) → Ctx (suc n)
weakenCtx' last Γ A = Γ , A
weakenCtx' (prev k) (Γ , B) A = weakenCtx' k Γ A , weakenTy' k B

prev^ : (n : ℕ) → Fin (suc m) → Fin (suc (n + m))
prev^ zero k = k
prev^ (suc n) k = prev (prev^ n k)

-- weakenCommutes : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TyExpr (m + n)) → weakenTy' (prev^ m last) (weakenTy' (prev^ m k) A) ≡ weakenTy' (prev^ m (prev k)) (weakenTy' (prev^ m last) A)
-- weakenCommutes k (pi A B) = {!!}
-- weakenCommutes k uu = {!!}
-- weakenCommutes k (el v) = {!!}

transport : {A : Set} (B : A → Set) {a a' : A} (p : a ≡ a') → B a → B a'
transport B refl x = x

inj∈ : {Γ : Ctx n} {k : Fin (suc n)} {x : Fin n} {A : TyExpr n} {B : TyExpr (n -F k)} → Γ ∋ x :> A → ((weakenCtx' k Γ B) ∋ (injF k x) :> (weakenTy' k A))
inj∈ = {!!}
-- inj∈ {k = last} r = prev r
-- inj∈ {k = prev k} {B = B} (last {Γ = Γ} {A = A}) = transport (λ x → (weakenCtx' k Γ B , weakenTy' k A) ∋ last :> x) (weakenCommutes 0 k A) last
-- inj∈ {k = prev k} {B = B} (prev {Γ = Γ} {x = x} {A = A} {B = B'} r) =
--   transport (λ y → (weakenCtx' k Γ B , weakenTy' k B') ∋ prev (injF k x) :> y)
--             (weakenCommutes 0 k A) (prev (inj∈ r))

weakeningDerivableTy : {m : ℕ} (k : Fin (suc m)) {Γ : Ctx m} {A : TyExpr m} {B : TyExpr (m -F k)} → Derivable (Γ ⊢ A) → Derivable (weakenCtx' k Γ B ⊢ weakenTy' k A)
weakeningDerivableTm : {m : ℕ} (k : Fin (suc m)) {Γ : Ctx m} {u : TmExpr m} {A : TyExpr m} {B : TyExpr (m -F k)} → Derivable (Γ ⊢ u :> A) → Derivable (weakenCtx' k Γ B ⊢ weakenTm' k u :> weakenTy' k A)

weakeningDerivableTy k (Pi dA dB) = Pi (weakeningDerivableTy k dA) (weakeningDerivableTy (prev k) dB)
weakeningDerivableTy k UU = UU
weakeningDerivableTy k (El dv) = El (weakeningDerivableTm k dv)
weakeningDerivableTy k _ = {!!}

weakeningDerivableTm k (VarRule x∈ dA) = VarRule (inj∈ x∈) (weakeningDerivableTy k dA)
weakeningDerivableTm k (Conv du dA=) = {!!}
weakeningDerivableTm k (Lam dA dB du) = Lam (weakeningDerivableTy k dA) (weakeningDerivableTy (prev k) dB) (weakeningDerivableTm (prev k) du)
weakeningDerivableTm k (App dA dB df da) = {!App (weakeningDerivableTy k dA) (weakeningDerivableTy (prev k) dB) (weakeningDerivableTm k df) (weakeningDerivableTm k da)!}
weakeningDerivableTm k _ = {!!}

idMor' : (n : ℕ) → Mor n n
idMor' zero = ◇
idMor' (suc n) = weakenMor (idMor' n) , var last

prefMor : (n : ℕ) (k : Fin (suc n)) → Mor n ⟨ k ⟩
prefMor n last = ◇
prefMor (suc n) (prev k) = {!prefMor n k!} , var k

weakeningMor : (n : ℕ) (k : Fin (suc n)) → Mor (suc n) n
weakeningMor n last = weakenMor (idMor' n)
weakeningMor (suc n) (prev k) = (weakenMor (weakeningMor n k) , var last)

idMor : (n : ℕ) → Mor n n
idMor zero = ◇
idMor (suc n) = idMor n [ weakeningMor n last ]Mor , var last

renameIsSubstVar : {n m k : ℕ} (r : Fin m → Fin k) (x : Fin n) (δ : Mor m n) → renameTm r (var x [ δ ]Tm) ≡ var x [ renameMor r δ ]Tm
renameIsSubstVar r last (δ , u) = refl
renameIsSubstVar r (prev x) (δ , u) = renameIsSubstVar r x δ

weakenIsSubstVar : (k : Fin (suc n)) (x : Fin n) → weakenTm' k (var x) ≡ var x [ weakeningMor n k ]Tm
weakenIsSubstTy : (k : Fin (suc n)) (A : TyExpr n) → weakenTy' k A ≡ A [ weakeningMor n k ]Ty
weakenIsSubstTm : (k : Fin (suc n)) (u : TmExpr n) → weakenTm' k u ≡ u [ weakeningMor n k ]Tm
weakenIsSubstMor : (k : Fin (suc n)) (δ : Mor n m) → weakenMor' k δ ≡ δ [ weakeningMor n k ]Mor

weakenIsSubstVar last last = refl
weakenIsSubstVar last (prev x) = ap weakenTm (weakenIsSubstVar last x) ∙ renameIsSubstVar prev x _
weakenIsSubstVar (prev k) last = refl
weakenIsSubstVar (prev k) (prev x) = ap weakenTm (weakenIsSubstVar k x) ∙ renameIsSubstVar prev x _

weakenIsSubstTy k (pi A B) rewrite weakenIsSubstTy k A | weakenIsSubstTy (prev k) B = refl
weakenIsSubstTy k uu = refl
weakenIsSubstTy k (el v) rewrite weakenIsSubstTm k v = refl

weakenIsSubstTm k (var x) = weakenIsSubstVar k x
weakenIsSubstTm k (lam A B u) rewrite weakenIsSubstTy k A | weakenIsSubstTy (prev k) B | weakenIsSubstTm (prev k) u = refl
weakenIsSubstTm k (app A B f a) rewrite weakenIsSubstTy k A | weakenIsSubstTy (prev k) B | weakenIsSubstTm k f | weakenIsSubstTm k a = refl

weakenIsSubstMor k ◇ = refl
weakenIsSubstMor k (δ , u) rewrite weakenIsSubstMor k δ | weakenIsSubstTm k u = refl

idMor=idMor' : (n : ℕ) → idMor n ≡ idMor' n
idMor=idMor' zero = refl
idMor=idMor' (suc n) rewrite idMor=idMor' n | ! (weakenIsSubstMor last (idMor' n)) = refl


-- weakeningMorDerivable : (n : ℕ) (Γ : Ctx n) .(_ : ⊢ Γ) (k : Fin (suc n)) (A : TyExpr (n -F k)) → (weakenCtx' k Γ A ⊢ weakeningMor n k ∷> Γ)
-- weakeningMorDerivable zero ◇ tt k A = {!!}
-- weakeningMorDerivable (suc n) (Γ , B) dΓ last A = {!weakeningMorDerivable n Γ ? last !} , {!!}
-- -- weakeningMorDerivable (suc n) (Γ , B) dΓ (prev k₁) A = {!weakeningMorDerivable n Γ ? k₁ A!} , {!!}

-- weakenMor^ : (m : Fin (suc n)) (δ : Mor (n -F m) k) → Mor n k
-- weakenMor^ last δ = δ
-- weakenMor^ {n = suc n} (prev m) δ = weakenMor^ {!m!} (weakenMor δ)

trim : {n : ℕ} (k : Fin (suc n)) (Γ : Ctx n) → Ctx (n -F k)
trim last Γ = Γ
trim (prev k) (Γ , _) = trim k Γ


postulate
  weakeningMorDerivable : (n : ℕ) (Γ : Ctx n) .(_ : ⊢ Γ) (A : TyExpr n) → ((Γ , A) ⊢ weakeningMor n last ∷> Γ)
-- weakeningMorDerivable .(suc _) m (Γ , B) last (dΓ , dB) A = {!m!}
-- weakeningMorDerivable .(suc _) m Γ (prev k₁) dΓ A = {!!}
-- weakeningMorDerivable (suc n) (Γ , B) (dΓ , dB) A = {!weakeningMorDerivable n Γ ? !} , {!!}
-- weakeningMorDerivable (suc n) (Γ , B) dΓ (prev k₁) A = {!weakeningMorDerivable n Γ ? k₁ A!} , {!!}

.idMorDerivable : (n : ℕ) (Γ : Ctx n) (_ : ⊢ Γ) → (Γ ⊢ idMor n ∷> Γ)
idMorDerivable zero ◇ dΓ = tt
idMorDerivable (suc n) (Γ , A) (dΓ , dA) = (SubstMor (idMorDerivable n Γ dΓ) (weakeningMorDerivable n Γ dΓ A) , VarRule {!last!} {!!})


{- Preliminary definitions for the syntactic model -}

⊢==-is-prop : {n : ℕ} (Γ Γ' : Ctx n) → is-prop (⊢ Γ == Γ')
⊢==-is-prop ◇ ◇ tt tt = refl
⊢==-is-prop (Γ , A) (Γ' , A') (a , b) (a' , b') = {!pair-irr (⊢==-is-prop Γ Γ' a a')!}

ObEquiv : (n : ℕ) → EquivRel (DCtx n)
EquivRel._≃_ (ObEquiv n) (Γ , _) (Γ' , _) = ⊢ Γ == Γ'
EquivRel._≃-is-prop_ (ObEquiv n) (Γ , _) (Γ' , _) = ⊢==-is-prop Γ Γ' 
EquivRel.ref (ObEquiv n) (Γ , dΓ) = CtxRefl dΓ
EquivRel.sym (ObEquiv n) p = CtxSymm p
EquivRel.tra (ObEquiv n) p q = CtxTran p q

ObsynCCat : ℕ → Set
ObsynCCat n = DCtx n // ObEquiv n

MorEquiv : (n m : ℕ) → EquivRel (DMor n m)
EquivRel._≃_ (MorEquiv n m) (((Γ , _), (Δ , _)), (δ , _)) (((Γ' , _), (Δ' , _)), (δ' , _)) = ((⊢ Γ == Γ') × (⊢ Δ == Δ')) × (Γ ⊢ δ == δ' ∷> Δ)
EquivRel._≃-is-prop_ (MorEquiv n m) = {!!}
EquivRel.ref (MorEquiv n m) (((_ , dΓ), (_ , dΔ)) , (_ , dδ)) = (CtxRefl dΓ , CtxRefl dΔ) , (MorRefl dδ)
EquivRel.sym (MorEquiv n m) {a = a} ((Γ= , Δ=) , δ=) = (CtxSymm Γ= , CtxSymm Δ=) , ConvMorEq (MorSymm (snd (snd (fst a))) δ=) Γ= Δ=
EquivRel.tra (MorEquiv n m) {a = a} ((Γ= , Δ=) , δ=) ((Γ'= , Δ'=) , δ'=) = ((CtxTran Γ= Γ'=) , (CtxTran Δ= Δ'=)) , (MorTran (snd (snd (fst a))) δ= (ConvMorEq δ'= (CtxSymm Γ=) (CtxSymm Δ=)))

MorsynCCat : ℕ → ℕ → Set
MorsynCCat n m = DMor n m // MorEquiv n m

∂₀synCCat : {n m : ℕ} → MorsynCCat n m → ObsynCCat n
∂₀synCCat = //-rec (ObsynCCat _) (λ {((Γ , _), _) → proj Γ}) (λ _ _ r → eq (fst (fst r)))

∂₁synCCat : {n m : ℕ} → MorsynCCat n m → ObsynCCat m
∂₁synCCat = //-rec (ObsynCCat _) (λ {((_ , Δ), _) → proj Δ}) (λ _ _ r → eq (snd (fst r)))

idsynCCat : (n : ℕ) → ObsynCCat n → MorsynCCat n n
idsynCCat n = //-rec (MorsynCCat _ _) (λ {(Γ , dΓ) → proj (((Γ , dΓ) , (Γ , dΓ)) , (idMor n , idMorDerivable n Γ dΓ))}) #TODO#

compsynCCat-//2 : (g : DMor m k) (f : DMor n m) .(_ : ∂₁synCCat (proj f) ≡ ∂₀synCCat (proj g)) → MorsynCCat n k
compsynCCat-//2 ((Δd , Θd) , (θ , dθ)) ((Γd , Δd') , (δ , dδ)) p = proj ((Γd , Θd) , (θ [ δ ]Mor , (SubstMor dθ {!dδ!})))

compsynCCat-// : (g : DMor m k) (f : MorsynCCat n m) .(_ : ∂₁synCCat f ≡ ∂₀synCCat (proj g)) → MorsynCCat n k
compsynCCat-// g = {!!}

compsynCCat : (g : MorsynCCat m k) (f : MorsynCCat n m) .(_ : ∂₁synCCat f ≡ ∂₀synCCat g) → MorsynCCat n k
compsynCCat = {!//-rec!}

dft : DCtx (suc n) → DCtx n
dft ((Γ , A), (dΓ , dA)) = (Γ , dΓ)

ftsynCCat-// : (n : ℕ) → DCtx (suc n) → ObsynCCat n
ftsynCCat-// n Γ = proj (dft Γ)

ftsynCCat : (n : ℕ) → ObsynCCat (suc n) → ObsynCCat n
ftsynCCat n = //-rec (ObsynCCat n) (ftsynCCat-// n) (λ {((Γ , _) , (_ , _)) ((Γ' , _) , (_ , _)) r → eq (fst' r)})

ppsynCCat : (X : ObsynCCat (suc n)) → MorsynCCat (suc n) n
ppsynCCat {n = n} = //-rec _ (λ Γ → proj ((Γ , dft Γ) , ((weakeningMor n last) , {!!}))) (λ a b r → eq ((r , {!!}) , {!!}))

ptmorsynCCat : (X : ObsynCCat n) → MorsynCCat n 0
ptmorsynCCat = //-rec _ (λ Γ → proj ((Γ , (◇ , tt)) , (◇ , tt))) (λ a b r → eq ((r , tt) , tt))

{- The syntactic model itsefl -}

synCCat : CCat
Ob synCCat = ObsynCCat
CCat.Mor synCCat = MorsynCCat
∂₀ synCCat = ∂₀synCCat
∂₁ synCCat = ∂₁synCCat
id synCCat = idsynCCat _
id₀ synCCat {n = n} {X = X} = //-elimId (λ X → ∂₀synCCat (idsynCCat n X)) (λ X → X) (λ Γ → refl) X
id₁ synCCat {n = n} {X = X} = //-elimId (λ X → ∂₁synCCat (idsynCCat n X)) (λ X → X) (λ Γ → refl) X
comp synCCat = {!compsynCCat!}
comp₀ synCCat = {!!}
comp₁ synCCat = {!!}
ft synCCat {n = n} = ftsynCCat n
pp synCCat = ppsynCCat
pp₀ synCCat {X = X} = //-elimId (λ X → ∂₀synCCat (ppsynCCat X)) (λ X → X) (λ Γ → refl) X
pp₁ synCCat {n = n} {X = X} = //-elimId (λ X → ∂₁synCCat (ppsynCCat X)) (λ X → ftsynCCat n X) (λ Γ → refl) X
star synCCat = {!!}
qq synCCat = {!!}
qq₀ synCCat = {!!}
qq₁ synCCat = {!!}
ss synCCat = {!!}
ss₀ synCCat = {!!}
ss₁ synCCat = {!!}
pt synCCat = proj (◇ , tt)
pt-unique synCCat = //-elimId (λ z → z) (λ _ → proj (◇ , tt)) (λ {(◇ , tt) → eq tt})
ptmor synCCat = ptmorsynCCat
ptmor₀ synCCat {X = X} = //-elimId (λ X → ∂₀synCCat (ptmorsynCCat X)) (λ X → X) (λ Γ → refl) X
ptmor₁ synCCat {X = X} = //-elimId (λ X → ∂₁synCCat (ptmorsynCCat X)) (λ X → proj (◇ , tt)) (λ Γ → refl) X
ptmor-unique synCCat = {!!}
id-right synCCat = {!!}
id-left synCCat = {!!}
assoc synCCat = {!!}
ft-star synCCat = {!!}
pp-qq synCCat = {!!}
star-id synCCat = {!!}
qq-id synCCat = {!!}
star-comp synCCat = {!!}
ss-pp synCCat = {!!}
ss-qq synCCat = {!!}
ss-comp synCCat = {!!}
