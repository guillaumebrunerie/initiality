{-# OPTIONS --irrelevant-projections --type-in-type --rewriting #-}

open import common
open import contextualcat
open import quotients

open CCat hiding (Mor)

{- Syntax of term- and type-expressions, using de Bruijn indices -}

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

{- Total substitutions -}

totalSubstTy : {n m : ℕ} → TyExpr n → (δ : Mor m n) → TyExpr m
totalSubstTm : {n m : ℕ} → TmExpr n → (δ : Mor m n) → TmExpr m

totalSubstTy (pi A B) δ = pi (totalSubstTy A δ) (totalSubstTy B (weakenMor δ , var last))
totalSubstTy uu δ = uu
totalSubstTy (el v) δ = el (totalSubstTm v δ)

totalSubstTm (var last) (δ , u) = u
totalSubstTm (var (prev x)) (δ , u) = totalSubstTm (var x) δ
totalSubstTm (lam A B u) δ = lam (totalSubstTy A δ)
                                 (totalSubstTy B (weakenMor δ , var last))
                                 (totalSubstTm u (weakenMor δ , var last))
totalSubstTm (app A B f a) δ = app (totalSubstTy A δ) (totalSubstTy B (weakenMor δ , var last)) (totalSubstTm f δ) (totalSubstTm a δ)

{- The different forms of (pre)judgments. Maybe the judgments for contexts and context morphisms could be defined later. -}
data Judgment : Set where
  _⊢_ : (Γ : Ctx n) → TyExpr n → Judgment
  _⊢_:>_ : (Γ : Ctx n) → TmExpr n → TyExpr n → Judgment
  _⊢_∷>_ : (Γ : Ctx n) → Mor n m → Ctx m → Judgment

  _⊢_==_ : (Γ : Ctx n) → TyExpr n → TyExpr n → Judgment
  _⊢_==_:>_ : (Γ : Ctx n) → TmExpr n → TmExpr n → TyExpr n → Judgment
  _⊢_==_∷>_ : (Γ : Ctx n) → Mor n m → Mor n m → Ctx m → Judgment


data _∋_:>_ : {n : ℕ} (Γ : Ctx n) → Fin n → TyExpr n → Set where
  last : {Γ : Ctx n} {A : TyExpr n} → (Γ , A) ∋ last :> weakenTy A
  prev : {Γ : Ctx n} {x : Fin n} {A B : TyExpr n} → (Γ ∋ x :> A) → (Γ , B) ∋ prev x :> weakenTy A

{- Derivability of judgments, the typing rules of the type theory -}
data Derivable : Judgment → Set
⊢_ : Ctx n → Set
⊢ ◇ = Unit
⊢ (Γ , A) = (⊢ Γ) × Derivable (Γ ⊢ A)

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

  -- Formation rules for context morphisms
  EmpMor : {Γ : Ctx n}
         → (⊢ Γ) → Derivable (Γ ⊢ ◇ ∷> ◇)
  ExtMor : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {u : TmExpr n} {δ : Mor n m}
         → Derivable (Γ ⊢ δ ∷> Δ) → Derivable (Δ ⊢ A) → Derivable (Γ ⊢ u :> totalSubstTy A δ) → Derivable (Γ ⊢ (δ , u) ∷> (Δ , A))

  -- Formation rules for context morphism equality
  EmpMorEq : {Γ : Ctx n}
           → (⊢ Γ) → Derivable (Γ ⊢ ◇ == ◇ ∷> ◇)
  ExtMorEq : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {u u' : TmExpr n} {δ δ' : Mor n m}
           → Derivable (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Δ ⊢ A) → Derivable (Γ ⊢ u == u' :> totalSubstTy A δ) → Derivable (Γ ⊢ (δ , u) == (δ' , u') ∷> (Δ , A))

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

⊢_==_ : Ctx n → Ctx n → Set
⊢ ◇ == ◇ = Unit
⊢ (Γ , A) == (Γ' , A') = (⊢ Γ == Γ') × Derivable (Γ ⊢ A == A')

record DCtx (n : ℕ) : Set where
  constructor _,_
  field
    fst : Ctx n
    .snd : (⊢ fst)
open DCtx

pair-irr : {n : ℕ} {Γ Γ' : Ctx n} {dΓ : ⊢ Γ} {dΓ' : ⊢ Γ'} → Γ ≡ Γ' → _≡_ {A = DCtx n} (Γ , dΓ) (Γ' , dΓ')
pair-irr refl = refl

DMor : ℕ → ℕ → Set
DMor n m = Σ (DCtx n × DCtx m) (λ {((Γ , _) , (Δ , _)) → Σ (Mor n m) (λ δ → Derivable (Γ ⊢ δ ∷> Δ))})


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

weakeningDerivableTm k (VarRule x∈ dA) = VarRule (inj∈ x∈) (weakeningDerivableTy k dA)
weakeningDerivableTm k (Conv du dA=) = {!!}
weakeningDerivableTm k (Lam dA dB du) = Lam (weakeningDerivableTy k dA) (weakeningDerivableTy (prev k) dB) (weakeningDerivableTm (prev k) du)
weakeningDerivableTm k (App dA dB df da) = {!App (weakeningDerivableTy k dA) (weakeningDerivableTy (prev k) dB) (weakeningDerivableTm k df) (weakeningDerivableTm k da)!}

idMor : (n : ℕ) → Mor n n
idMor zero = ◇
idMor (suc n) = weakenMor (idMor n) , var last

idMorDerivable : (n : ℕ) (Γ : Ctx n) → ⊢ Γ → Derivable (Γ ⊢ idMor n ∷> Γ)
idMorDerivable zero ◇ dΓ = EmpMor dΓ
idMorDerivable (suc n) (Γ , A) (dΓ , dA) = ExtMor {!idMorDerivable n Γ dΓ!} dA {!!}

ObsynCCat : ℕ → Set
ObsynCCat n = DCtx n // λ {(Γ , _) (Γ' , _) → ⊢ Γ == Γ'}

MorsynCCat : ℕ → ℕ → Set
MorsynCCat n m = DMor n m // λ {(((Γ , _), (Δ , _)), (δ , _)) (((Γ' , _), (Δ' , _)), (δ' , _)) → ((⊢ Γ == Γ') × (⊢ Δ == Δ')) × Derivable (Γ ⊢ δ == δ' ∷> Δ)}

∂₀synCCat : {n m : ℕ} → MorsynCCat n m → ObsynCCat n
∂₀synCCat = //-rec (ObsynCCat _) (λ {((Γ , _), _) → proj Γ}) (λ {_ _ r → eq (fst (fst r))})

∂₁synCCat : {n m : ℕ} → MorsynCCat n m → ObsynCCat m
∂₁synCCat = //-rec (ObsynCCat _) (λ {((_ , Δ), _) → proj Δ}) (λ {_ _ r → eq (snd (fst r))})

postulate
  #TODO# : {A : Set} → A

idsynCCat : (n : ℕ) → ObsynCCat n → MorsynCCat n n
idsynCCat n = //-rec (MorsynCCat _ _) (λ {(Γ , dΓ) → proj (((Γ , dΓ) , (Γ , dΓ)) , (idMor n , {!!}))}) #TODO#

ftsynCCat-// : (n : ℕ) → DCtx (suc n) → ObsynCCat n
ftsynCCat-// n ((Γ , _) , (dΓ , _)) = proj (Γ , dΓ)

ftsynCCat : (n : ℕ) → ObsynCCat (suc n) → ObsynCCat n
ftsynCCat n = //-rec (ObsynCCat n) (ftsynCCat-// n) (λ {((Γ , _) , _) ((Γ' , _) , _) r → eq (fst r)})

synCCat : CCat
Ob synCCat = ObsynCCat
CCat.Mor synCCat = MorsynCCat
∂₀ synCCat = ∂₀synCCat
∂₁ synCCat = ∂₁synCCat
id synCCat {n = n} = idsynCCat n
id₀ synCCat {n = n} {X = X} = //-elimId (λ X → ∂₀synCCat (idsynCCat n X)) (λ X → X) (λ Γ → refl) X
id₁ synCCat {n = n} {X = X} = //-elimId (λ X → ∂₁synCCat (idsynCCat n X)) (λ X → X) (λ Γ → refl) X
comp synCCat = {!!}
comp₀ synCCat = {!!}
comp₁ synCCat = {!!}
ft synCCat {n = n} = ftsynCCat n
pp synCCat = {!!}
pp₀ synCCat = {!!}
pp₁ synCCat = {!!}
star synCCat = {!!}
qq synCCat = {!!}
qq₀ synCCat = {!!}
qq₁ synCCat = {!!}
ss synCCat = {!!}
ss₀ synCCat = {!!}
ss₁ synCCat = {!!}
pt synCCat = proj (◇ , tt)
pt-unique synCCat = {!!}
ptmor synCCat = {!!}
ptmor₀ synCCat = {!!}
ptmor₁ synCCat = {!!}
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
