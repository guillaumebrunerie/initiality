{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import typetheory
open import syntx
open import reflection
 
{- The four different forms of (pre)judgments. -}

data Judgment : Set where
  _⊢_ : (Γ : Ctx n) → TyExpr n → Judgment
  _⊢_:>_ : (Γ : Ctx n) → TmExpr n → TyExpr n → Judgment
  _⊢_==_ : (Γ : Ctx n) → TyExpr n → TyExpr n → Judgment
  _⊢_==_:>_ : (Γ : Ctx n) → TmExpr n → TmExpr n → TyExpr n → Judgment


{- Derivability of judgments, the typing rules of the type theory -}

data Derivable : Judgment → Prop where

  -- Variable rules
  VarLast : {Γ : Ctx n} {A : TyExpr n}
    → Derivable (Γ ⊢ A)
    → Derivable ((Γ , A) ⊢ var last :> weakenTy A)
  VarPrev : {Γ : Ctx n} {B : TyExpr n} {k : Fin n} {A : TyExpr n}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ var k :> A)
    → Derivable ((Γ , B) ⊢ var (prev k) :> weakenTy A)
          
  -- Congruence for variables
  VarLastCong : {Γ : Ctx n} {A : TyExpr n}
    → Derivable (Γ ⊢ A)
    → Derivable ((Γ , A) ⊢ var last == var last :> weakenTy A)
  VarPrevCong : {Γ : Ctx n} {B : TyExpr n} {k k' : Fin n} {A : TyExpr n}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ var k == var k' :> A)
    → Derivable ((Γ , B) ⊢ var (prev k) == var (prev k') :> weakenTy A)
          
  -- Symmetry and transitivity for types
  TySymm : {Γ : Ctx n} {A B : TyExpr n}
    → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B == A)
  TyTran : {Γ : Ctx n} {A B C : TyExpr n}
    → Derivable (Γ ⊢ B) → Derivable (Γ ⊢ A == B)→ Derivable (Γ ⊢ B == C) → Derivable (Γ ⊢ A == C)

  -- Symmetry and transitivity for terms
  TmSymm : {Γ : Ctx n} {u v : TmExpr n} {A : TyExpr n}
    → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ v == u :> A)
  TmTran : {Γ : Ctx n} {u v w : TmExpr n} {A : TyExpr n}
    → Derivable (Γ ⊢ v :> A) → Derivable (Γ ⊢ u == v :> A)→ Derivable (Γ ⊢ v == w :> A) → Derivable (Γ ⊢ u == w :> A)

  -- Conversion rules
  Conv : {Γ : Ctx n} {u : TmExpr n} {A B : TyExpr n} → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u :> B)
  ConvEq : {Γ : Ctx n} {u u' : TmExpr n} {A B : TyExpr n} → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u == u' :> B)


  -- Rules for UU
  UU : {i : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ uu i)
  UUCong :  {i : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ uu i == uu i)

  -- Rules for UU
  UUUU : {i : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ uu i :> uu (suc i))
  UUUUCong : {i : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ uu i == uu i :> uu (suc i))
  ElUU= : {i : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ el (suc i) (uu i) == uu i)

  -- Rules for El
  El : {i : ℕ} {Γ : Ctx n} {v : TmExpr n}
    → Derivable (Γ ⊢ v :> uu i) → Derivable (Γ ⊢ el i v)
  ElCong : {i : ℕ} {Γ : Ctx n} {v v' : TmExpr n}
    → Derivable (Γ ⊢ v == v' :> uu i) → Derivable (Γ ⊢ el i v == el i v')


  -- Rules for Pi
  Pi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} 
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ pi A B)
  PiCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ pi A B == pi A' B')

  -- Rules for pi
  PiUU : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {b : TmExpr (suc n)}
    → Derivable (Γ ⊢ a :> uu i) → Derivable ((Γ , el i a) ⊢ b :> uu i) → Derivable (Γ ⊢ pi i a b :> uu i)
  PiUUCong : {i : ℕ} {Γ : Ctx n} {a a' : TmExpr n} {b b' : TmExpr (suc n)}
    → Derivable (Γ ⊢ a :> uu i) → Derivable (Γ ⊢ a == a' :> uu i) → Derivable ((Γ , el i a) ⊢ b == b' :> uu i) → Derivable (Γ ⊢ pi i a b == pi i a' b' :> uu i)
  ElPi= : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {b : TmExpr (suc n)}
    → Derivable (Γ ⊢ a :> uu i) → Derivable ((Γ , el i a) ⊢ b :> uu i) → Derivable (Γ ⊢ el i (pi i a b) == pi (el i a) (el i b))

  -- Rules for lambda
  Lam : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B)
    → Derivable (Γ ⊢ lam A B u :> pi A B)
  LamCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr (suc n)}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable ((Γ , A) ⊢ u == u' :> B)
    → Derivable (Γ ⊢ lam A B u == lam A' B' u' :> pi A B)

  -- Rules for app
  App : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ f :> pi A B) → Derivable (Γ ⊢ a :> A)
    → Derivable (Γ ⊢ app A B f a :> substTy B a)
  AppCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {f f' a a' : TmExpr n}
    → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ f == f' :> pi A B) → Derivable (Γ ⊢ a == a' :> A)
    → Derivable (Γ ⊢ app A B f a == app A' B' f' a' :> substTy B a)


  -- Rules for Sigma
  Sig : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ sig A B)
  SigCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ sig A B == sig A' B')

  -- Rules for sig
  SigUU : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {b : TmExpr (suc n)}
    → Derivable (Γ ⊢ a :> uu i) → Derivable ((Γ , el i a) ⊢ b :> uu i) → Derivable (Γ ⊢ sig i a b :> uu i)
  SigUUCong : {i : ℕ} {Γ : Ctx n} {a a' : TmExpr n} {b b' : TmExpr (suc n)}
    → Derivable (Γ ⊢ a :> uu i) → Derivable (Γ ⊢ a == a' :> uu i) → Derivable ((Γ , el i a) ⊢ b == b' :> uu i) → Derivable (Γ ⊢ sig i a b == sig i a' b' :> uu i)
  ElSig= : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {b : TmExpr (suc n)}
    → Derivable (Γ ⊢ a :> uu i) → Derivable ((Γ , el i a) ⊢ b :> uu i) → Derivable (Γ ⊢ el i (sig i a b) == sig (el i a) (el i b))

  -- Rules for pair
  Pair : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {a : TmExpr n} {b : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ b :> substTy B a) → Derivable (Γ ⊢ pair A B a b :> sig A B)
  PairCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {a a' : TmExpr n} {b b' : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ a == a' :> A) → Derivable (Γ ⊢ b == b' :> substTy B a) → Derivable (Γ ⊢ pair A B a b == pair A' B' a' b' :> sig A B)

  -- Rules for pr1
  Pr1 : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ u :> sig A B) → Derivable (Γ ⊢ pr1 A B u :> A)
  Pr1Cong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ u == u' :> sig A B) → Derivable (Γ ⊢ pr1 A B u == pr1 A' B' u' :> A)

  -- Rules for pr2
  Pr2 : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ u :> sig A B) → Derivable (Γ ⊢ pr2 A B u :> substTy B (pr1 A B u))
  Pr2Cong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr (suc n)} {u u' : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A') → Derivable ((Γ , A) ⊢ B == B') → Derivable (Γ ⊢ u == u' :> sig A B) → Derivable (Γ ⊢ pr2 A B u == pr2 A' B' u' :> substTy B (pr1 A B u))


  -- Rules for Nat
  Nat : {Γ : Ctx n}
    → Derivable (Γ ⊢ nat)
  NatCong : {Γ : Ctx n}
    → Derivable (Γ ⊢ nat == nat)

  -- Rules for nat
  NatUU : {i : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ nat i :> uu i)
  NatUUCong : {i : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ nat i == nat i :> uu i)
  ElNat= : {i : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ el i (nat i) == nat)

  -- Rules for zero
  Zero : {Γ : Ctx n}
    → Derivable (Γ ⊢ zero :> nat)
  ZeroCong : {Γ : Ctx n}
    → Derivable (Γ ⊢ zero == zero :> nat)

  -- Rules for suc
  Suc : {Γ : Ctx n} {u : TmExpr n}
    → Derivable (Γ ⊢ u :> nat) → Derivable (Γ ⊢ suc u :> nat)
  SucCong : {Γ : Ctx n} {u u' : TmExpr n}
    → Derivable (Γ ⊢ u == u' :> nat) → Derivable (Γ ⊢ suc u == suc u' :> nat)

  -- Rules for natelim
  Natelim : {Γ : Ctx n} {P : TyExpr (suc n)} {dO : TmExpr n} {dS : TmExpr (suc (suc n))} {u : TmExpr n}
    → Derivable ((Γ , nat) ⊢ P) → Derivable (Γ ⊢ dO :> substTy P zero) → Derivable (((Γ , nat) , P) ⊢ dS :> weakenTy (substTy (weakenTy' (prev last) P) (suc (var last)))) → Derivable (Γ ⊢ u :> nat) → Derivable (Γ ⊢ natelim P dO dS u :> substTy P u)
  NatelimCong : {Γ : Ctx n} {P P' : TyExpr (suc n)} {dO dO' : TmExpr n} {dS dS' : TmExpr (suc (suc n))} {u u' : TmExpr n}
    → Derivable ((Γ , nat) ⊢ P) → Derivable ((Γ , nat) ⊢ P == P') → Derivable (Γ ⊢ dO == dO' :> substTy P zero) → Derivable (((Γ , nat) , P) ⊢ dS == dS' :> weakenTy (substTy (weakenTy' (prev last) P) (suc (var last)))) → Derivable (Γ ⊢ u == u' :> nat) → Derivable (Γ ⊢ natelim P dO dS u == natelim P' dO' dS' u' :> substTy P u)


  -- Rules for Id
  Id : {Γ : Ctx n} {A : TyExpr n} {a b : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ b :> A) → Derivable (Γ ⊢ id A a b)
  IdCong : {Γ : Ctx n} {A A' : TyExpr n} {a a' b b' : TmExpr n}
    → Derivable (Γ ⊢ A == A') → Derivable (Γ ⊢ a == a' :> A) → Derivable (Γ ⊢ b == b' :> A) → Derivable (Γ ⊢ id A a b == id A' a' b')

  -- Rules for id
  IdUU : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {u v : TmExpr n}
    → Derivable (Γ ⊢ a :> uu i) → Derivable (Γ ⊢ u :> el i a) → Derivable (Γ ⊢ v :> el i a) → Derivable (Γ ⊢ id i a u v :> uu i)
  IdUUCong : {i : ℕ} {Γ : Ctx n} {a a' : TmExpr n} {u u' v v' : TmExpr n}
    → Derivable (Γ ⊢ a == a' :> uu i) → Derivable (Γ ⊢ u == u' :> el i a) → Derivable (Γ ⊢ v == v' :> el i a) → Derivable (Γ ⊢ id i a u v == id i a' u' v' :> uu i)
  ElId= : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {u v : TmExpr n}
    → Derivable (Γ ⊢ a :> uu i) → Derivable (Γ ⊢ u :> el i a) → Derivable (Γ ⊢ v :> el i a) → Derivable (Γ ⊢ el i (id i a u v) == id (el i a) u v)
  
  -- Rules for refl
  Refl : {Γ : Ctx n} {A : TyExpr n} {a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ refl A a :> id A a a)
  ReflCong : {Γ : Ctx n} {A A' : TyExpr n} {a a' : TmExpr n}
    → Derivable (Γ ⊢ A == A') → Derivable (Γ ⊢ a == a' :> A) → Derivable (Γ ⊢ refl A a == refl A' a' :> id A a a)

  -- Rules for jj
  JJ : {Γ : Ctx n} {A : TyExpr n} {P : TyExpr (suc (suc (suc n)))} {d : TmExpr (suc n)} {a b p : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((((Γ , A) , weakenTy A) , id (weakenTy (weakenTy A)) (var (prev last)) (var last)) ⊢ P) → Derivable ((Γ , A) ⊢ d :> subst3Ty (weakenTy' (prev (prev (prev last))) P) (var last) (var last) (refl (weakenTy A) (var last))) → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ b :> A) → Derivable (Γ ⊢ p :> id A a b) → Derivable (Γ ⊢ jj A P d a b p :> subst3Ty P a b p)
  JJCong :  {Γ : Ctx n} {A A' : TyExpr n} {P P' : TyExpr (suc (suc (suc n)))} {d d' : TmExpr (suc n)} {a a' b b' p p' : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A') →  Derivable ((((Γ , A) , weakenTy A) , id (weakenTy (weakenTy A)) (var (prev last)) (var last)) ⊢ P == P') → Derivable ((Γ , A) ⊢ d == d' :> subst3Ty (weakenTy' (prev (prev (prev last))) P) (var last) (var last) (refl (weakenTy A) (var last))) → Derivable (Γ ⊢ a == a' :> A) → Derivable (Γ ⊢ b == b' :> A) → Derivable (Γ ⊢ p == p' :> id A a b) → Derivable (Γ ⊢ jj A P d a b p == jj A' P' d' a' b' p' :> subst3Ty P a b p)


  -- Beta-reductions
  BetaPi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)} {a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ a :> A)
    → Derivable (Γ ⊢ app A B (lam A B u) a == substTm u a :> substTy B a)
  BetaSig1 : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {a : TmExpr n} {b : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ b :> substTy B a) → Derivable (Γ ⊢ pr1 A B (pair A B a b) == a :> A)
  BetaSig2 : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {a : TmExpr n} {b : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ b :> substTy B a) → Derivable (Γ ⊢ pr2 A B (pair A B a b) == b :> substTy B a)
  BetaNatZero : {Γ : Ctx n} {P : TyExpr (suc n)} {dO : TmExpr n} {dS : TmExpr (suc (suc n))}
    → Derivable ((Γ , nat) ⊢ P) → Derivable (Γ ⊢ dO :> substTy P zero) → Derivable (((Γ , nat) , P) ⊢ dS :> weakenTy (substTy (weakenTy' (prev last) P) (suc (var last))))
    → Derivable (Γ ⊢ natelim P dO dS zero == dO :> substTy P zero)
  BetaNatSuc : {Γ : Ctx n} {P : TyExpr (suc n)} {dO : TmExpr n} {dS : TmExpr (suc (suc n))} {u : TmExpr n}
    → Derivable ((Γ , nat) ⊢ P) → Derivable (Γ ⊢ dO :> substTy P zero) → Derivable (((Γ , nat) , P) ⊢ dS :> weakenTy (substTy (weakenTy' (prev last) P) (suc (var last)))) → Derivable (Γ ⊢ u :> nat)
    → Derivable (Γ ⊢ natelim P dO dS (suc u) == subst2Tm dS u (natelim P dO dS u) :> substTy P (suc u))
  BetaIdRefl : {Γ : Ctx n} {A : TyExpr n} {P : TyExpr (suc (suc (suc n)))} {d : TmExpr (suc n)} {a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((((Γ , A) , weakenTy A) , id (weakenTy (weakenTy A)) (var (prev last)) (var last)) ⊢ P) → Derivable ((Γ , A) ⊢ d :> subst3Ty (weakenTy' (prev (prev (prev last))) P) (var last) (var last) (refl (weakenTy A) (var last))) → Derivable (Γ ⊢ a :> A)
    → Derivable (Γ ⊢ jj A P d a a (refl A a) == substTm d a :> subst3Ty P a a (refl A a))

{- Derivability of contexts, context equality, context morphisms, and context morphism equality -}

⊢_ : Ctx n → Prop
⊢ ◇ = Unit
⊢ (Γ , A) = (⊢ Γ) × Derivable (Γ ⊢ A)

⊢_==_ : Ctx n → Ctx n → Prop
⊢ ◇ == ◇ = Unit
⊢ (Γ , A) == (Γ' , A') = (⊢ Γ == Γ') × Derivable (Γ ⊢ A) × Derivable (Γ' ⊢ A') × Derivable (Γ ⊢ A == A') × Derivable (Γ' ⊢ A == A')

_⊢_∷>_ : (Γ : Ctx n) → Mor n m → Ctx m → Prop
Γ ⊢ ◇ ∷> ◇ = Unit
Γ ⊢ (δ , u) ∷> (Δ , A) = (Γ ⊢ δ ∷> Δ) × Derivable (Γ ⊢ u :> A [ δ ]Ty) 

_⊢_==_∷>_ : (Γ : Ctx n) → Mor n m → Mor n m → Ctx m → Prop
Γ ⊢ ◇ == ◇ ∷> ◇ = Unit
Γ ⊢ (δ , u) == (δ' , u') ∷> (Δ , A) = (Γ ⊢ δ == δ' ∷> Δ) × Derivable (Γ ⊢ u == u' :> A [ δ ]Ty)


{- Congruence with respect to the type in derivability of term expressions -}

congTy : {Γ : Ctx n} {A A' : TyExpr n} → A ≡ A' → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A')
congTy refl dA = dA

congTyCtx :  {Γ Γ' : Ctx n} {A : TyExpr n} → Γ ≡ Γ' → Derivable (Γ ⊢ A) → Derivable (Γ' ⊢ A)
congTyCtx refl dA = dA

congTyCtxEq : {Γ Γ' : Ctx n} {A B : TyExpr n} → Γ ≡ Γ' → Derivable (Γ ⊢ A == B) → Derivable (Γ' ⊢ A == B)
congTyCtxEq refl dA= = dA=

congTyEq : {Γ : Ctx n} {A A' B B' : TyExpr n} → A ≡ A' → B ≡ B' → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A' == B')
congTyEq refl refl dA= = dA=

congTm : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A ≡ A' → u ≡ u' → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u' :> A')
congTm refl refl du = du

congTmTy : {Γ : Ctx n} {A A' : TyExpr n} {u : TmExpr n} → A ≡ A' → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u :> A')
congTmTy refl du = du

congTmTy! : {Γ : Ctx n} {A A' : TyExpr n} {u : TmExpr n} → A' ≡ A → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u :> A')
congTmTy! refl du = du

congTmEqTy : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A ≡ A' → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u == u' :> A')
congTmEqTy refl du= = du=

congTmEqTy! : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A' ≡ A → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u == u' :> A')
congTmEqTy! refl du= = du=

congTmEqTm : {Γ : Ctx n} {A : TyExpr n} {u u' v v' : TmExpr n} → u ≡ v → u' ≡ v' → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ v == v' :> A)
congTmEqTm refl refl du= = du=

congTmEq : {Γ : Ctx n} {A A' : TyExpr n} {u u' v v' : TmExpr n} → u ≡ v → u' ≡ v' → A ≡ A' → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ v == v' :> A')
congTmEq refl refl refl du= = du=

congMor : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} → Γ ≡ Γ' → Δ ≡ Δ' → δ ≡ δ' → Γ ⊢ δ ∷> Δ → Γ' ⊢ δ' ∷> Δ'
congMor refl refl refl dδ = dδ

congMorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' θ θ' : Mor n m} → Γ ≡ Γ' → Δ ≡ Δ' → δ ≡ δ' → θ ≡ θ' → Γ ⊢ δ == θ ∷> Δ → Γ' ⊢ δ' == θ' ∷> Δ'
congMorEq refl refl refl refl dδ= = dδ=


{- Reflexivity rules -}

TyRefl : {Γ : Ctx n} {A : TyExpr n} → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A)
TmRefl : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u == u :> A)

TyRefl (Pi dA dB) = PiCong dA (TyRefl dA) (TyRefl dB)
TyRefl UU = UUCong
TyRefl (El dv) = ElCong (TmRefl dv)
TyRefl (Sig dA dB) = SigCong dA (TyRefl dA) (TyRefl dB)
TyRefl Nat = NatCong
TyRefl (Id dA da db) = IdCong (TyRefl dA) (TmRefl da) (TmRefl db)

TmRefl (VarLast dA) = VarLastCong dA
TmRefl (VarPrev dA dk) = VarPrevCong dA (TmRefl dk) 
TmRefl (Conv dA du dA=) = ConvEq dA (TmRefl du) dA=
TmRefl (Lam dA dB du) = LamCong dA (TyRefl dA) (TyRefl dB) (TmRefl du)
TmRefl (App dA dB df da) = AppCong dA (TyRefl dA) (TyRefl dB) (TmRefl df) (TmRefl da)
TmRefl UUUU = UUUUCong
TmRefl (PiUU da db) = PiUUCong da (TmRefl da) (TmRefl db)
TmRefl (SigUU da db) = SigUUCong da (TmRefl da) (TmRefl db)
TmRefl (Pair dA dB du dv) = PairCong dA (TyRefl dA) (TyRefl dB) (TmRefl du) (TmRefl dv)
TmRefl (Pr1 dA dB du) = Pr1Cong dA (TyRefl dA) (TyRefl dB) (TmRefl du)
TmRefl (Pr2 dA dB du) = Pr2Cong dA (TyRefl dA) (TyRefl dB) (TmRefl du)
TmRefl NatUU = NatUUCong
TmRefl Zero = ZeroCong
TmRefl (Suc du) = SucCong (TmRefl du)
TmRefl (Natelim dP ddO ddS du) = NatelimCong dP (TyRefl dP) (TmRefl ddO) (TmRefl ddS) (TmRefl du)
TmRefl (IdUU da du dv) = IdUUCong (TmRefl da) (TmRefl du) (TmRefl dv)
TmRefl (Refl dA da) = ReflCong (TyRefl dA) (TmRefl da)
TmRefl (JJ dA dP dd da db dp) = JJCong dA (TyRefl dA) (TyRefl dP) (TmRefl dd) (TmRefl da) (TmRefl db) (TmRefl dp) 


congTyRefl : {Γ : Ctx n} {A A' : TyExpr n} → Derivable (Γ ⊢ A) → A ≡ A' → Derivable (Γ ⊢ A == A')
congTyRefl dA refl = TyRefl dA

congTyRefl' : {Γ : Ctx n} {A A' : TyExpr n} → Derivable (Γ ⊢ A') → A ≡ A' → Derivable (Γ ⊢ A == A')
congTyRefl' dA refl = TyRefl dA

congTmRefl : {Γ : Ctx n} {A : TyExpr n} {u u' : TmExpr n} → Derivable (Γ ⊢ u :> A) → u ≡ u' → Derivable (Γ ⊢ u == u' :> A)
congTmRefl du refl = TmRefl du

CtxRefl : {Γ : Ctx n} → ⊢ Γ → ⊢ Γ == Γ
CtxRefl {Γ = ◇} tt = tt
CtxRefl {Γ = Γ , A} (dΓ , dA) = (CtxRefl dΓ , dA , dA , TyRefl dA , TyRefl dA)

MorRefl : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ δ == δ ∷> Δ)
MorRefl {Δ = ◇} {δ = ◇} dδ = tt
MorRefl {Δ = Δ , B} {δ = δ , u} (dδ , du) = MorRefl dδ , TmRefl du

congMorRefl : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → δ ≡ δ' → Γ ⊢ δ ∷> Δ → Γ ⊢ δ == δ' ∷> Δ
congMorRefl refl dδ = MorRefl dδ


{- Substitution and weakening are admissible -}

SubstTy : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → Derivable (Γ ⊢ A [ δ ]Ty)
SubstTm : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ u :> A) → Γ ⊢ δ ∷> Δ → Derivable (Γ ⊢ u [ δ ]Tm :> A [ δ ]Ty)
SubstTyEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ A == A') → Γ ⊢ δ ∷> Δ → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ ]Ty)
SubstTmEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ : Mor n m}
       → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u' [ δ ]Tm :> A [ δ ]Ty)
SubstTyMorEq : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m} → Derivable (Δ ⊢ A) → (Γ ⊢ δ ∷> Δ)
       → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A [ δ' ]Ty)
SubstTmMorEq : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m} →  Derivable (Δ ⊢ u :> A) → (Γ ⊢ δ ∷> Δ) 
       → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u [ δ' ]Tm :> A [ δ ]Ty)
       
WeakTy' : (k : Fin (suc n)) {Γ : Ctx n} (T : TyExpr (n -F' k)) {A : TyExpr n}
     → Derivable (Γ ⊢ A) → Derivable (weakenCtx k Γ T ⊢ weakenTy' k A)
WeakTm' : (k : Fin (suc n)) {Γ : Ctx n} (T : TyExpr (n -F' k)) {u : TmExpr n} {A : TyExpr n}
     → Derivable (Γ ⊢ u :> A) → Derivable (weakenCtx k Γ T ⊢ weakenTm' k u :> weakenTy' k A)
WeakTyEq' : (k : Fin (suc n)) {Γ : Ctx n} (T : TyExpr (n -F' k)) {A A' : TyExpr n}
     → Derivable (Γ ⊢ A == A') → Derivable (weakenCtx k Γ T ⊢ weakenTy' k A == weakenTy' k A')
WeakTmEq' : (k : Fin (suc n)) {Γ : Ctx n} (T : TyExpr (n -F' k)) {u u' : TmExpr n} {A : TyExpr n}
     → Derivable (Γ ⊢ u == u' :> A) → Derivable (weakenCtx k Γ T ⊢ weakenTm' k u == weakenTm' k u' :> weakenTy' k A)

WeakMor : {Γ : Ctx n} {Δ : Ctx m} (T : TyExpr n) {δ : Mor n m} → Γ ⊢ δ ∷> Δ → (Γ , T) ⊢ weakenMor δ ∷> Δ
WeakMor {Δ = ◇} _ {δ = ◇} tt = tt
WeakMor {Δ = Δ , B} T  {δ = δ , u} (dδ , du) rewrite ! (weaken[]Ty B δ last) = (WeakMor T dδ , WeakTm' last T du)

WeakMorEq : {Γ : Ctx n } {Δ : Ctx m} (T : TyExpr n) {δ δ' : Mor n m} → (Γ ⊢ δ == δ' ∷> Δ) → ((Γ , T) ⊢ weakenMor δ == weakenMor δ' ∷> Δ)
WeakMorEq {Δ = ◇} _ {δ = ◇} {◇} dδ = tt
WeakMorEq {Δ = Δ , B} T {δ = δ , u} {δ' , u'} (dδ , du) rewrite ! (weaken[]Ty B δ last) = (WeakMorEq T dδ , WeakTmEq' last T du)

WeakMor+~ : {Γ : Ctx n} {Δ : Ctx m} (A : TyExpr m) {δ : Mor n m} → Derivable (Γ ⊢ A [ δ ]Ty) → Γ ⊢ δ ∷> Δ → (Γ , A [ δ ]Ty) ⊢ weakenMor+ δ ∷> (Δ , A)
WeakMor+~ A dAδ dδ = (WeakMor _ dδ , congTmTy (weaken[]Ty _ _ _) (VarLast dAδ))

WeakMor+ : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m} → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → (Γ , A [ δ ]Ty) ⊢ weakenMor+ δ ∷> (Δ , A)
WeakMor+ dA dδ = WeakMor+~ _ (SubstTy dA dδ) dδ

WeakMor+Eq : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m} → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → Γ ⊢ δ == δ' ∷> Δ → (Γ , A [ δ ]Ty) ⊢ weakenMor+ δ == weakenMor+ δ' ∷> (Δ , A)
WeakMor+Eq dA dδ dδ= = (WeakMorEq _ dδ= , TmRefl (congTmTy (weaken[]Ty _ _ _) (VarLast (SubstTy dA dδ))))


SubstTy {A = pi A B} (Pi dA dB) dδ = Pi (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ))
SubstTy {A = uu i} UU dδ = UU
SubstTy {A = el i v} (El dA) dδ = El (SubstTm dA dδ)
SubstTy {A = sig A B} (Sig dA dB) dδ = Sig (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ))
SubstTy {A = nat} Nat dδ = Nat
SubstTy {A = id A u v} (Id dA du dv) dδ = Id (SubstTy dA dδ) (SubstTm du dδ) (SubstTm dv dδ)

SubstTm (Conv dA du dA=) dδ = Conv (SubstTy dA dδ) (SubstTm du dδ) (SubstTyEq dA= dδ)
SubstTm {Δ = (Δ , A)} {var last} {δ = δ , u} (VarLast {A = A'} dA) (dδ , du) rewrite weakenTyInsert A δ u = du
SubstTm {Δ = (Δ , B)} {u = var (prev k)} {δ = δ , u} (VarPrev {A = A} _ dk) (dδ , du) rewrite weakenTyInsert A δ u = SubstTm dk dδ
SubstTm {u = lam A B u} (Lam dA dB du) dδ = Lam (SubstTy dA dδ) ((SubstTy dB (WeakMor+ dA dδ))) (SubstTm du (WeakMor+ dA dδ ))
SubstTm {u = app A B f a} {δ = δ} (App dA dB df da) dδ rewrite ! (substCommutes[]Ty B a δ)=  App (SubstTy dA  dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm df dδ) (SubstTm da dδ)
SubstTm {u = uu i} UUUU dδ = UUUU
SubstTm {u = pi i a b} (PiUU da db) dδ = PiUU (SubstTm da dδ) (SubstTm db (WeakMor+ (El da) dδ))
SubstTm {u = sig i a b} (SigUU da db) dδ = SigUU (SubstTm da dδ) (SubstTm db (WeakMor+ (El da) dδ))
SubstTm {u = pair A B a b} {δ = δ} (Pair dA dB da db) dδ = Pair (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm da dδ) (congTmTy! (substCommutes[]Ty B a δ) (SubstTm db dδ))
SubstTm {u = pr1 A B u} (Pr1 dA dB du) dδ = Pr1 (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm du dδ)
SubstTm {u = pr2 A B u} {δ = δ} (Pr2 dA dB du) dδ rewrite ! (substCommutes[]Ty B (pr1 A B u) δ) = Pr2 (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm du dδ)
SubstTm {u = nat i} NatUU dδ = NatUU
SubstTm {u = zero} Zero dδ = Zero
SubstTm {u = suc u} (Suc du) dδ = Suc (SubstTm du dδ)
SubstTm {u = natelim P dO dS u} {δ = δ} (Natelim dP ddO ddS du) dδ =
  let thing = ap weakenTy (ap (λ z → substTy z _) (weaken[]Ty _ _ _
                                                  ∙ ! (weakenTyInsert' (prev last) _ _ (var (prev last)))
                                                  ∙ ap (λ z → _ [ (z , _) , _ ]Ty) (! (weakenMorCommutes _ _)))
                           ∙ substCommutes[]Ty _ _ _)
              ∙ ! ([weakenMor]Ty _ _) in
  congTmTy (substCommutes[]Ty _ _ _) (Natelim (SubstTy dP (WeakMor+ Nat dδ)) (congTmTy! (substCommutes[]Ty _ _ _) (SubstTm ddO dδ)) (congTmTy! thing (SubstTm ddS (WeakMor+ dP (WeakMor+ Nat dδ)))) (SubstTm du dδ))
SubstTm {u = id i a u v} (IdUU da du dv) dδ = IdUU (SubstTm da dδ) (SubstTm du dδ) (SubstTm dv dδ)
SubstTm {u = refl A a} (Refl dA da) dδ = Refl (SubstTy dA dδ) (SubstTm da dδ)
SubstTm {Γ = Γ} {Δ = Δ} {u = jj A P d a b p} {δ = δ} (JJ dA dP dd da db dp) dδ =
        congTmTy ([]Ty-assoc _ _ _ ∙ ap (_[_]Ty P) (Mor+= (Mor+= (Mor+= (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ [idMor]Mor _ ∙ ! (idMor[]Mor _)) refl) refl) refl ) ∙ ! ([]Ty-assoc _ _ _))
                 (JJ (SubstTy dA dδ) 
                     (SubstTy dP (congMor {Δ = ((Δ , A) , weakenTy A) , id (weakenTy (weakenTy A)) (var (prev last)) (var last)}
                                          (Ctx+= (Ctx+= refl
                                                        (weakenTyInsert _ _ (var last) ∙ ! (weaken[]Ty _ _ _)))
                                                 (ap-id-Ty (weakenTyInsert _ _ (var last) ∙ weakenTyInsert _ _ (var (prev last)) ∙ ! (weaken[]Ty _ _ _) ∙ ap weakenTy (! (weaken[]Ty _ _ _)))
                                                           refl
                                                           refl))
                                                 refl
                                                 refl
                                                 ((((WeakMor _ (WeakMor _ (WeakMor _ dδ))) ,
                                                    congTmTy (ap weakenTy (ap weakenTy (weaken[]Ty _ _ _) ) ∙ ap weakenTy (weaken[]Ty _ _ _) ∙ weaken[]Ty _ _ _)
                                                             (VarPrev (WeakTy' last _ (WeakTy' last _ (SubstTy dA dδ))) (VarPrev (WeakTy' last _ (SubstTy dA dδ)) (VarLast (SubstTy dA dδ))))) ,
                                                    congTmTy (ap weakenTy (weaken[]Ty _ _ _) ∙ weaken[]Ty _ _ _)
                                                             (VarPrev (WeakTy' last _ (congTy (! (weakenTyInsert _ _ _)) (SubstTy dA (WeakMor _ dδ)))) (VarLast (congTy (! (weakenTyInsert _ _ _)) (SubstTy dA (WeakMor _ dδ)))))) ,
                                                    congTmTy (ap-id-Ty (ap weakenTy (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _) ∙ weaken[]Ty _ _ _ ∙ ! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _ ))
                                                                       refl
                                                                       refl)
                                                             (VarLast (Id (congTy (! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _))
                                                                                  (SubstTy dA (WeakMor _ (WeakMor _ dδ))))
                                                                          (congTmTy (! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _ ∙ ! (ap weakenTy (weaken[]Ty _ _ _) ∙ weaken[]Ty _ _ _)))
                                                                                    (VarPrev (WeakTy' last _ (SubstTy dA dδ)) (VarLast (SubstTy dA dδ))))
                                                                          (congTmTy (ap weakenTy (weakenTyInsert _ _ _) ∙ weaken[]Ty _ _ _ ∙ ! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _))
                                                                                    (VarLast (congTy (! (weakenTyInsert _ _ _)) (SubstTy dA (WeakMor _ dδ))))))))))
                     (congTmTy ([]-subst3Ty (weakenTy' (prev (prev (prev last))) P) ∙ ap-subst3Ty ([]-weakenTy3 P) refl refl (ap-refl-Tm ([]-weakenTy A) refl)) (SubstTm dd (WeakMor+ dA dδ)))
                     (SubstTm da dδ)
                     (SubstTm db dδ)
                     (SubstTm dp dδ))

SubstTyEq (TySymm dA=) dδ = TySymm (SubstTyEq dA= dδ)
SubstTyEq (TyTran dB dA= dB=) dδ = TyTran (SubstTy dB dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= dδ)
SubstTyEq {A = pi A B} (PiCong dA dA= dB=) dδ = PiCong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ))
SubstTyEq UUCong dδ = UUCong
SubstTyEq (ElCong dv=) dδ = ElCong (SubstTmEq dv= dδ)
SubstTyEq ElUU= dδ = ElUU=
SubstTyEq {A = el i (pi i a b)} (ElPi= da db) dδ = ElPi= (SubstTm da dδ) (SubstTm db (WeakMor+ (El da) dδ))
SubstTyEq {A = sig A B} (SigCong dA dA= dB=) dδ = SigCong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ))
SubstTyEq {A = el i (sig i a b)} (ElSig= da db) dδ = ElSig= (SubstTm da dδ) (SubstTm db (WeakMor+ (El da) dδ))
SubstTyEq NatCong dδ = NatCong
SubstTyEq ElNat= dδ = ElNat=
SubstTyEq (IdCong dA= da= db=) dδ = IdCong (SubstTyEq dA= dδ) (SubstTmEq da= dδ) (SubstTmEq db= dδ)
SubstTyEq (ElId= da du dv) dδ = ElId= (SubstTm da dδ) (SubstTm du dδ) (SubstTm dv dδ)


ap2 : {A B C : Set} (f : A → B → C) {a a' : A} (p : a ≡ a') {b b' : B} (q : b ≡ b') → f a b ≡ f a' b'
ap2 f refl refl = refl

SubstTmEq {δ = δ , u} (VarLastCong {A = A} dA=) (_ , du) rewrite weakenTyInsert A δ u = TmRefl du
SubstTmEq {δ = δ , u} (VarPrevCong {A = A} _ dA=) (dδ , du) rewrite weakenTyInsert A δ u = SubstTmEq dA= dδ 
SubstTmEq (TmSymm du=) dδ = TmSymm (SubstTmEq du= dδ)
SubstTmEq (TmTran dv du= dv=) dδ = TmTran (SubstTm dv dδ) (SubstTmEq du= dδ) (SubstTmEq dv= dδ)
SubstTmEq (ConvEq dA du= dA=) dδ = ConvEq (SubstTy dA dδ) (SubstTmEq du= dδ) (SubstTyEq dA= dδ) 
SubstTmEq UUUUCong dδ = UUUUCong
SubstTmEq (PiUUCong da da= db=) dδ = PiUUCong (SubstTm da dδ) (SubstTmEq da= dδ) (SubstTmEq db= (WeakMor+ (El da) dδ))
SubstTmEq (LamCong dA dA= dB= du=) dδ = LamCong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ)) (SubstTmEq du= (WeakMor+ dA dδ))
SubstTmEq (AppCong dA dA= dB= df= da=) dδ = congTmEqTy (substCommutes[]Ty _ _ _) (AppCong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ)) (SubstTmEq df= dδ) (SubstTmEq da= dδ))
SubstTmEq (SigUUCong da da= db=) dδ = SigUUCong (SubstTm da dδ) (SubstTmEq da= dδ) (SubstTmEq db= (WeakMor+ (El da) dδ))
SubstTmEq (PairCong dA dA= dB= da= db=) dδ = PairCong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ)) (SubstTmEq da= dδ) (congTmEqTy! (substCommutes[]Ty _ _ _) (SubstTmEq db= dδ))
SubstTmEq (Pr1Cong dA dA= dB= du=) dδ = Pr1Cong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ)) (SubstTmEq du= dδ)
SubstTmEq (Pr2Cong dA dA= dB= du=) dδ = congTmEqTy (substCommutes[]Ty _ _ _) (Pr2Cong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ)) (SubstTmEq du= dδ))
SubstTmEq NatUUCong dδ = NatUUCong
SubstTmEq ZeroCong dδ = ZeroCong
SubstTmEq (SucCong du=) dδ = SucCong (SubstTmEq du= dδ)
SubstTmEq (NatelimCong dP dP= ddO= ddS= du=) dδ =
  let thing = ap weakenTy (ap (λ z → substTy z _) (weaken[]Ty _ _ _
                                                  ∙ ! (weakenTyInsert' (prev last) _ _ (var (prev last)))
                                                  ∙ ap (λ z → _ [ (z , _) , _ ]Ty) (! (weakenMorCommutes _ _)))
                           ∙ substCommutes[]Ty _ _ _)
              ∙ ! ([weakenMor]Ty _ _) in
  congTmEqTy (substCommutes[]Ty _ _ _) (NatelimCong (SubstTy dP (WeakMor+ Nat dδ)) (SubstTyEq dP= (WeakMor+ Nat dδ)) (congTmEqTy! (substCommutes[]Ty _ _ _) (SubstTmEq ddO= dδ)) (congTmEqTy! thing (SubstTmEq ddS= (WeakMor+ dP (WeakMor+ Nat dδ)))) (SubstTmEq du= dδ))
SubstTmEq (IdUUCong da= du= dv=) dδ = IdUUCong (SubstTmEq da= dδ) (SubstTmEq du= dδ) (SubstTmEq dv= dδ)
SubstTmEq (ReflCong dA= da=) dδ = ReflCong (SubstTyEq dA= dδ) (SubstTmEq da= dδ)
SubstTmEq (JJCong {A = A} {P = P} dA dA= dP= dd= da= db= dp=) dδ =
          congTmEqTy ([]Ty-assoc _ _ _ ∙ ap (_[_]Ty P) (Mor+= (Mor+= (Mor+= (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ [idMor]Mor _ ∙ ! (idMor[]Mor _)) refl) refl) refl ) ∙ ! ([]Ty-assoc _ _ _))
                     (JJCong (SubstTy dA dδ)
                             (SubstTyEq dA= dδ)
                             (SubstTyEq dP= (congMor {Δ = ((_ , A) , weakenTy A) , id (weakenTy (weakenTy A)) (var (prev last)) (var last)}
                                                     (Ctx+= (Ctx+= refl
                                                                   (weakenTyInsert _ _ _ ∙ ! (weaken[]Ty _ _ _)))
                                                     (ap-id-Ty (weakenTyInsert _ _ (var last) ∙ weakenTyInsert _ _ (var (prev last)) ∙ ! (weaken[]Ty _ _ _) ∙ ap weakenTy (! (weaken[]Ty _ _ _)))
                                                               refl
                                                               refl))
                                                     refl
                                                     refl
                                                     ((((WeakMor _ (WeakMor _ (WeakMor _ dδ))) ,
                                                      congTmTy (ap weakenTy (ap weakenTy (weaken[]Ty _ _ _) ) ∙ ap weakenTy (weaken[]Ty _ _ _) ∙ weaken[]Ty _ _ _)
                                                               (VarPrev (WeakTy' last _ (WeakTy' last _ (SubstTy dA dδ))) (VarPrev (WeakTy' last _ (SubstTy dA dδ)) (VarLast (SubstTy dA dδ))))) ,
                                                      congTmTy (ap weakenTy (weaken[]Ty _ _ _) ∙ weaken[]Ty _ _ _)
                                                               (VarPrev (WeakTy' last _ (congTy (! (weakenTyInsert _ _ _)) (SubstTy dA (WeakMor _ dδ))))
                                                                        (VarLast (congTy (! (weakenTyInsert _ _ _)) (SubstTy dA (WeakMor _ dδ)))))) ,
                                                      congTmTy (ap-id-Ty (ap weakenTy (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _) ∙ weaken[]Ty _ _ _ ∙ ! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _ ))
                                                                         refl
                                                                         refl)
                                                               (VarLast (Id (congTy (! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _))
                                                                                    (SubstTy dA (WeakMor _ (WeakMor _ dδ))))
                                                                            (congTmTy (! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _ ∙ ! (ap weakenTy (weaken[]Ty _ _ _) ∙ weaken[]Ty _ _ _)))
                                                                                      (VarPrev (WeakTy' last _ (SubstTy dA dδ)) (VarLast (SubstTy dA dδ))))
                                                                            (congTmTy (ap weakenTy (weakenTyInsert _ _ _) ∙ weaken[]Ty _ _ _ ∙ ! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _))
                                                                                      (VarLast (congTy (! (weakenTyInsert _ _ _)) (SubstTy dA (WeakMor _ dδ))))))))))
                             (congTmEqTy ([]-subst3Ty (weakenTy' (prev (prev (prev last))) P) ∙ ap-subst3Ty ([]-weakenTy3 P) refl refl (ap (λ z → refl z _) ([]-weakenTy A))) (SubstTmEq dd= (WeakMor+ dA dδ)))
                             (SubstTmEq da= dδ)
                             (SubstTmEq db= dδ)
                             (SubstTmEq dp= dδ))
SubstTmEq (BetaPi {u = u} dA dB du da) dδ = congTmEq refl (substCommutes[]Tm u _ _) (substCommutes[]Ty _ _ _) (BetaPi (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm du (WeakMor+ dA dδ )) (SubstTm da dδ))
SubstTmEq (BetaSig1 dA dB da db) dδ = BetaSig1 (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm da dδ) (congTm (! (substCommutes[]Ty _ _ _)) refl (SubstTm db dδ))
SubstTmEq (BetaSig2 dA dB da db) dδ = congTmEqTy (substCommutes[]Ty _ _ _) (BetaSig2 (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm da dδ) (congTm (! (substCommutes[]Ty _ _ _)) refl (SubstTm db dδ)))
SubstTmEq (BetaNatZero dP ddO ddS) dδ =
  congTmEqTy (substCommutes[]Ty _ _ _)
    (BetaNatZero
      (SubstTy dP (WeakMor+ Nat dδ))
      (congTmTy! (substCommutes[]Ty _ _ _)
                 (SubstTm ddO dδ))
      (congTmTy! (ap weakenTy (ap2 substTy (weaken[]Ty _ _ _ ∙ ap (λ z → _ [ z , var last ]Ty) (! (weakenMorCommutes last _)) ∙ ! (weakenTyInsert' _ _ (weakenMor+ _) (var (prev last)))) refl ∙ substCommutes[]Ty _ _ _) ∙ ! ([weakenMor]Ty _ _))
                 (SubstTm ddS (WeakMor+ dP (WeakMor+ Nat dδ)))))
SubstTmEq (BetaNatSuc {dS = dS} dP ddO ddS du) dδ =
  congTmEq refl
           (subst2Commutes[]Tm dS)
           (substCommutes[]Ty _ _ _)
    (BetaNatSuc
      (SubstTy dP (WeakMor+ Nat dδ))
      (congTmTy! (substCommutes[]Ty _ _ _)
                 (SubstTm ddO dδ))
      (congTmTy! (ap weakenTy (ap2 substTy (weaken[]Ty _ _ _ ∙ ap (λ z → _ [ z , var last ]Ty) (! (weakenMorCommutes last _)) ∙ ! (weakenTyInsert' _ _ (weakenMor+ _) (var (prev last)))) refl ∙ substCommutes[]Ty _ _ _) ∙ ! ([weakenMor]Ty _ _))
                 (SubstTm ddS (WeakMor+ dP (WeakMor+ Nat dδ))))
      (SubstTm du dδ))
SubstTmEq (BetaIdRefl {A = A} {d = d} dA dP dd da) dδ =  -- Using WeakMor+ in this clause creates termination errors
  congTmEq refl (! ([]-substTm d)) (! ([]-subst3Ty _))
    (BetaIdRefl
      (SubstTy dA dδ)
      (congTyCtx (Ctx+= (Ctx+= refl ([]-weakenTy _)) (ap-id-Ty ([]-weakenTy _ ∙ ap weakenTy ([]-weakenTy _)) refl refl))
                 (SubstTy dP (WeakMor+~ (id (weakenTy (weakenTy A)) (var (prev last)) (var last)) (Id (congTy (! ([]-weakenTy _ ∙ ap weakenTy ([]-weakenTy _))) (WeakTy' _ _ (WeakTy' _ _ (SubstTy dA dδ))))
                                                                                                      (congTmTy! ([]-weakenTy _ ∙ ap weakenTy ([]-weakenTy _)) (VarPrev (WeakTy' _ _ (SubstTy dA dδ)) (VarLast (SubstTy dA dδ))))
                                                                                                      (congTmTy! ([]-weakenTy _) (VarLast (congTy (! (weakenTyInsert _ _ _)) (SubstTy dA (WeakMor _ dδ)))))) (WeakMor+~ (weakenTy A) (congTy (! (weakenTyInsert _ _ _)) (SubstTy dA (WeakMor _ dδ))) (WeakMor+ dA dδ)))))
      (congTmTy ([]-subst3Ty _ ∙ ap-subst3Ty ([]-weakenTy3 _) refl refl (ap-refl-Tm ([]-weakenTy _) refl)) (SubstTm dd (WeakMor+ dA dδ)))
      (SubstTm da dδ))


SubstTyMorEq {A = pi A B} (Pi dA dB) dδ dδ= = PiCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=))
SubstTyMorEq {A = uu i} dA dδ dδ= = UUCong
SubstTyMorEq {A = el i v} (El dv) dδ dδ= = ElCong (SubstTmMorEq dv dδ dδ=)
SubstTyMorEq {A = sig A B} (Sig dA dB) dδ dδ= = SigCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=))
SubstTyMorEq {A = nat} Nat dδ dδ= = NatCong
SubstTyMorEq {A = id A a b} (Id dA da db) dδ dδ= = IdCong (SubstTyMorEq dA dδ dδ=) (SubstTmMorEq da dδ dδ=) (SubstTmMorEq db dδ dδ=)

SubstTmMorEq {u = var last} {δ = δ , u} {δ' = δ' , u'} (VarLast {A = A} dA) dδ (dδ= , du=) rewrite weakenTyInsert A δ u = du=
SubstTmMorEq {u = var (prev x)} {δ = δ , u} {δ' = δ' , u'} (VarPrev _ dk) (dδ , du) (dδ= , du=) = congTmEqTy (! (weakenTyInsert _ δ u)) (SubstTmMorEq dk dδ dδ=)
SubstTmMorEq {u = u} (Conv dA du dA=) dδ dδ= = ConvEq (SubstTy dA dδ) (SubstTmMorEq du dδ dδ=) (SubstTyEq dA= dδ)

SubstTmMorEq {u = uu i} {δ = δ} UUUU dδ dδ= = UUUUCong
SubstTmMorEq {u = pi i a b} {δ = δ} (PiUU da db) dδ dδ= = PiUUCong (SubstTm da dδ) (SubstTmMorEq da dδ dδ=) (SubstTmMorEq db (WeakMor+ (El da) dδ) (WeakMor+Eq (El da) dδ dδ=))
SubstTmMorEq {u = lam A B u} (Lam dA dB du) dδ dδ= = LamCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=)) (SubstTmMorEq du (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=))
SubstTmMorEq {u = app A B f a} {δ = δ} (App dA dB df da) dδ dδ= rewrite ! (substCommutes[]Ty B a δ) = AppCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=)) (SubstTmMorEq df dδ dδ=) (SubstTmMorEq da dδ dδ=)
SubstTmMorEq {u = sig i a b} {δ = δ} (SigUU da db) dδ dδ= = SigUUCong (SubstTm da dδ) (SubstTmMorEq da dδ dδ=) (SubstTmMorEq db (WeakMor+ (El da) dδ) (WeakMor+Eq (El da) dδ dδ=))
SubstTmMorEq {u = pair A B a b} {δ = δ} (Pair dA dB da db) dδ dδ= = PairCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=)) (SubstTmMorEq da dδ dδ=) (congTmEqTy (! (substCommutes[]Ty B a δ)) (SubstTmMorEq db  dδ dδ=))
SubstTmMorEq {u = pr1 A B u} {δ = δ} (Pr1 dA dB du) dδ dδ= = Pr1Cong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=)) (SubstTmMorEq du dδ dδ=)
SubstTmMorEq {u = pr2 A B u} {δ = δ} (Pr2 dA dB du) dδ dδ= rewrite ! (substCommutes[]Ty B (pr1 A B u) δ) = Pr2Cong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=)) (SubstTmMorEq du dδ dδ=)
SubstTmMorEq {u = nat i} {δ = δ} NatUU dδ dδ= = NatUUCong
SubstTmMorEq {u = zero} {δ = δ} Zero dδ dδ= = ZeroCong
SubstTmMorEq {u = suc u} {δ = δ} (Suc du) dδ dδ= = SucCong (SubstTmMorEq du dδ dδ=)
SubstTmMorEq {u = natelim P dO dS u} (Natelim dP ddO ddS du) dδ dδ= =
  let thing = ap weakenTy (ap (λ z → substTy z _) (weaken[]Ty _ _ _
                                                  ∙ ! (weakenTyInsert' (prev last) _ _ (var (prev last)))
                                                  ∙ ap (λ z → _ [ (z , _) , _ ]Ty) (! (weakenMorCommutes _ _)))
                           ∙ substCommutes[]Ty _ _ _)
              ∙ ! ([weakenMor]Ty _ _) in
  congTmEqTy (substCommutes[]Ty _ _ _) (NatelimCong (SubstTy dP (WeakMor+ Nat dδ)) (SubstTyMorEq dP (WeakMor+ Nat dδ) (WeakMor+Eq Nat dδ dδ=)) (congTmEqTy! (substCommutes[]Ty _ _ _) (SubstTmMorEq ddO dδ dδ=)) (congTmEqTy! thing (SubstTmMorEq ddS (WeakMor+ dP (WeakMor+ Nat dδ)) (WeakMor+Eq dP (WeakMor+ Nat dδ) (WeakMor+Eq Nat dδ dδ=)))) (SubstTmMorEq du dδ dδ=))
SubstTmMorEq {u = id i a u v} {δ = δ} (IdUU da du dv) dδ dδ= = IdUUCong (SubstTmMorEq da dδ dδ=) (SubstTmMorEq du dδ dδ=) (SubstTmMorEq dv dδ dδ=)
SubstTmMorEq {u = refl A a} {δ = δ} (Refl dA da) dδ dδ= = ReflCong (SubstTyMorEq dA dδ dδ=) (SubstTmMorEq da dδ dδ=)
SubstTmMorEq {Γ = Γ} {u = jj A P d a b p} {δ = δ} (JJ dA dP dd da db dp) dδ dδ= = 
  congTmEqTy ([]Ty-assoc _ _ _ ∙ ap (_[_]Ty P) (Mor+= (Mor+= (Mor+= (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ [idMor]Mor _ ∙ ! (idMor[]Mor _)) refl) refl) refl ) ∙ ! ([]Ty-assoc _ _ _))
                     (JJCong (SubstTy dA dδ)
                             (SubstTyMorEq dA dδ dδ=)
                             (SubstTyMorEq dP (congMor {Δ = ((_ , A) , weakenTy A) , id (weakenTy (weakenTy A)) (var (prev last)) (var last)}
                                                       (Ctx+= (Ctx+= refl
                                                                     (weakenTyInsert _ _ _ ∙ ! (weaken[]Ty _ _ _)))
                                                       (ap-id-Ty (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _ ∙ ! (weaken[]Ty _ _ _) ∙ ap weakenTy (! (weaken[]Ty _ _ _)))
                                                                 refl
                                                                 refl))
                                                       refl
                                                       refl
                                                       (WeakMor+ (Id (WeakTy' last (weakenTy A) (WeakTy' last A dA)) (VarPrev (WeakTy' last A dA) (VarLast dA)) (VarLast (WeakTy' last A dA)))
                                                                 (WeakMor+ (WeakTy' last A dA) (WeakMor+ dA dδ))))
                                              (congMorEq {Δ = ((_ , A) , weakenTy A) , id (weakenTy (weakenTy A)) (var (prev last)) (var last)}
                                                         (Ctx+= (Ctx+= refl
                                                                       (weakenTyInsert _ _ _ ∙ ! (weaken[]Ty _ _ _)))
                                                         (ap-id-Ty (weakenTyInsert _ _ (var last) ∙ weakenTyInsert _ _ (var (prev last)) ∙ ! (weaken[]Ty _ _ _) ∙ ap weakenTy (! (weaken[]Ty _ _ _)))
                                                                   refl
                                                                   refl))
                                                         refl
                                                         refl
                                                         refl
                                                         ((((WeakMorEq _ (WeakMorEq _ (WeakMorEq _ dδ=))) ,
                                                           congTmEqTy (ap weakenTy (ap weakenTy (weaken[]Ty _ _ _) ) ∙ ap weakenTy (weaken[]Ty _ _ _) ∙ weaken[]Ty _ _ _)
                                                                      (VarPrevCong (WeakTy' last _ (WeakTy' last _ (SubstTy dA dδ)))
                                                                                   (VarPrevCong (WeakTy' last _ (SubstTy dA dδ)) (VarLastCong (SubstTy dA dδ))))) ,
                                                           congTmEqTy (ap weakenTy (weaken[]Ty _ _ _) ∙ weaken[]Ty _ _ _)
                                                                      (VarPrevCong (WeakTy' last _ (congTy (! (weakenTyInsert _ _ _)) (SubstTy dA (WeakMor _ dδ))))
                                                                                   (VarLastCong (congTy (! (weakenTyInsert _ _ _)) (SubstTy dA (WeakMor _ dδ)))))) ,
                                                           congTmEqTy (ap-id-Ty (ap weakenTy (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _) ∙ weaken[]Ty _ _ _ ∙ ! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _ ))
                                                                                refl
                                                                                refl)
                                                                      (VarLastCong (Id (congTy (! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _))
                                                                                               (SubstTy dA (WeakMor _ (WeakMor _ dδ))))
                                                                                       (congTmTy (! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _ ∙ ! (ap weakenTy (weaken[]Ty _ _ _) ∙ weaken[]Ty _ _ _)))
                                                                                                 (VarPrev (WeakTy' last _ (SubstTy dA dδ)) (VarLast (SubstTy dA dδ))))
                                                                                       (congTmTy (ap weakenTy (weakenTyInsert _ _ _) ∙ weaken[]Ty _ _ _ ∙ ! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _))
                                                                                                 (VarLast (congTy (! (weakenTyInsert _ _ _)) (SubstTy dA (WeakMor _ dδ))))))))))
                             (congTmEqTy ([]-subst3Ty (weakenTy' (prev (prev (prev last))) P) ∙ ap-subst3Ty ([]-weakenTy3 P) refl refl (ap (λ z → refl z _) ([]-weakenTy A))) (SubstTmMorEq dd (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=)))
                             (SubstTmMorEq da dδ dδ=)
                             (SubstTmMorEq db dδ dδ=)
                             (SubstTmMorEq dp dδ dδ=))

WeakTy' k T {A = pi A B} (Pi dA dB) = Pi (WeakTy' k T dA) (WeakTy' (prev k) T dB)
WeakTy' k T {A = uu i} UU = UU
WeakTy' k T {A = el i v} (El dv) = El (WeakTm' k T dv)
WeakTy' k T {sig A B} (Sig dA dB) = Sig (WeakTy' k T dA) (WeakTy' (prev k) T dB)
WeakTy' k T {nat} Nat = Nat
WeakTy' k T {id A a b} (Id dA da db) = Id (WeakTy' k T dA) (WeakTm' k T da) (WeakTm' k T db)


WeakTyEq' k T (TySymm dA=) = TySymm (WeakTyEq' k T dA=)
WeakTyEq' k T (TyTran dB dA= dB=) = TyTran (WeakTy' k T dB) (WeakTyEq' k T dA=) (WeakTyEq' k T dB=)
WeakTyEq' k T (PiCong dA dA= dB=) = PiCong (WeakTy' k T dA) (WeakTyEq' k T dA=) (WeakTyEq' (prev k) T dB=)
WeakTyEq' k T UUCong = UUCong
WeakTyEq' k T (ElCong dv=) = ElCong (WeakTmEq' k T dv=)
WeakTyEq' k T ElUU= = ElUU=
WeakTyEq' k T (ElPi= da db) = ElPi= (WeakTm' k T da) (WeakTm' (prev k) T db)
WeakTyEq' k T (SigCong dA dA= dB=) = SigCong (WeakTy' k T dA) (WeakTyEq' k T dA=) (WeakTyEq' (prev k) T dB=)
WeakTyEq' k T (ElSig= da db) = ElSig= (WeakTm' k T da) (WeakTm' (prev k) T db)
WeakTyEq' k T NatCong = NatCong
WeakTyEq' k T ElNat= = ElNat=
WeakTyEq' k T (IdCong dA= da= db=) = IdCong (WeakTyEq' k T dA=) (WeakTmEq' k T da=) (WeakTmEq' k T db=)
WeakTyEq' k T (ElId= da du dv) = ElId= (WeakTm' k T da) (WeakTm' k T du) (WeakTm' k T dv)

WeakTm' k T (Conv dA du dA=) = Conv (WeakTy' k T dA) (WeakTm' k T du) (WeakTyEq' k T dA=) 
WeakTm' last {Γ , A} T {u = var x} (VarLast dA) = VarPrev (WeakTy' last A dA) (VarLast dA)
WeakTm' (prev k) T {u = var last} (VarLast {A = A} dA) rewrite ! (weakenTyCommutes k A) = VarLast (WeakTy' k T dA)
WeakTm' last T {u = var (prev x)} (VarPrev dA dk) = VarPrev (WeakTy' last _ dA) (VarPrev dA dk)
WeakTm' (prev k) T {u = var (prev x)} (VarPrev {A = A} dA dk) rewrite ! (weakenTyCommutes k A) = VarPrev (WeakTy' k T dA) (WeakTm' k T dk)
WeakTm' k T {u = lam A B u} (Lam dA dB du) = Lam (WeakTy' k T dA) (WeakTy' (prev k) T dB) (WeakTm' (prev k) T du)
WeakTm' k T {u = app A B f a} (App dA dB df da) rewrite ! (weakenCommutesSubstTy k B a) = App (WeakTy' k T dA) (WeakTy' (prev k) T dB) (WeakTm' k T df) (WeakTm' k T da)
WeakTm' k T UUUU = UUUU
WeakTm' k T (PiUU da db) = PiUU (WeakTm' k T da) (WeakTm' (prev k) T db)
WeakTm' k T (SigUU da db) = SigUU (WeakTm' k T da) (WeakTm' (prev k) T db)
WeakTm' k T {pair A B a b} (Pair dA dB da db) = Pair (WeakTy' k T dA) (WeakTy' (prev k) T dB) (WeakTm' k T da) (congTm (! (weakenCommutesSubstTy _ _ _)) refl (WeakTm' k T db))
WeakTm' k T (Pr1 dA dB du) = Pr1 (WeakTy' k T dA) (WeakTy' (prev k) T dB) (WeakTm' k T du)
WeakTm' k T {pr2 A B u} (Pr2 dA dB du) rewrite ! (weakenCommutesSubstTy k B (pr1 A B u)) = Pr2 (WeakTy' k T dA) (WeakTy' (prev k) T dB) (WeakTm' k T du)
WeakTm' k T NatUU = NatUU
WeakTm' k T Zero = Zero
WeakTm' k T (Suc du) = Suc (WeakTm' k T du)
WeakTm' k T (Natelim dP ddO ddS du) =
  let thing2 = ap weakenTy (ap (λ z → substTy z _) (weakenTyCommutesprev _ _) ∙ weakenCommutesSubstTy _ _ _) ∙ weakenTyCommutes _ _ in
  congTmTy (weakenCommutesSubstTy _ _ _) (Natelim (WeakTy' (prev k) T dP) (congTmTy! (weakenCommutesSubstTy _ _ _) (WeakTm' k T ddO))
                                               (congTmTy! thing2 (WeakTm' (prev (prev k)) T ddS)) (WeakTm' k T du))
WeakTm' k T (IdUU da du dv) = IdUU (WeakTm' k T da) (WeakTm' k T du) (WeakTm' k T dv)
WeakTm' k T (Refl dA da) = Refl (WeakTy' k T dA) (WeakTm' k T da)
WeakTm' k T (JJ {A = A} {P = P} {d = d} {a = a} {b = b} {p = p} dA dP dd da db dp) =
  congTmTy!
    (weaken-subst3Ty P)
    (JJ (WeakTy' k T dA)
        (congTyCtx (Ctx+= (Ctx+= refl (! (weakenTyCommutes _ _))) (ap-id-Ty (! (ap weakenTy (weakenTyCommutes _ _) ∙ weakenTyCommutes _ _)) refl refl)) (WeakTy' (prev (prev (prev k))) T dP))
        (congTmTy (weaken-subst3Ty (weakenTy' (prev (prev (prev last))) P) ∙ ap-subst3Ty (! (weakenTyCommutes3 _ P)) refl refl (ap-refl-Tm (! (weakenTyCommutes _ A)) refl)) (WeakTm' (prev k) T dd))
        (WeakTm' k T da)
        (WeakTm' k T db)
        (WeakTm' k T dp))

WeakTmEq' last T  {u = var last} {var last} (VarLastCong dA) = VarPrevCong (WeakTy' last _ dA) (VarLastCong dA)
WeakTmEq' (prev k) T {u = var last} {var last} (VarLastCong {A = A} dA) rewrite ! (weakenTyCommutes k A) = VarLastCong (WeakTy' k T dA)
WeakTmEq' last T {u = var (prev x)} (VarPrevCong dA dk=) = VarPrevCong (WeakTy' last _ dA) (WeakTmEq' last _ dk=)
WeakTmEq' (prev k) T {u = var (prev x)} (VarPrevCong {A = A} dA dk=) rewrite ! (weakenTyCommutes k A) = VarPrevCong (WeakTy' k T dA) (WeakTmEq' k T dk=)
WeakTmEq' k T (TmSymm du=) = TmSymm (WeakTmEq' k T du=)
WeakTmEq' k T (TmTran dv du= dv=) = TmTran (WeakTm' k T dv) (WeakTmEq' k T du=) (WeakTmEq' k T dv=)
WeakTmEq' k T (ConvEq dA du= dA=) = ConvEq (WeakTy' k T dA) (WeakTmEq' k T du=) (WeakTyEq' k T dA=)
WeakTmEq' k T UUUUCong = UUUUCong
WeakTmEq' k T (PiUUCong da da= db=) = PiUUCong (WeakTm' k T da) (WeakTmEq' k T da=) (WeakTmEq' (prev k) T db=)
WeakTmEq' k T {u = lam A B u} (LamCong dA dA= dB= du=) = LamCong (WeakTy' k T dA) (WeakTyEq' k T dA=) (WeakTyEq' (prev k) T dB=) (WeakTmEq' (prev k) T du=)
WeakTmEq' k T {u = app A B f a} (AppCong dA dA= dB= df= da=) rewrite ! (weakenCommutesSubstTy k B a) = AppCong (WeakTy' k T dA) (WeakTyEq' k T dA=) (WeakTyEq' (prev k) T dB=) (WeakTmEq' k T  df=) (WeakTmEq' k T da=)
WeakTmEq' k T (SigUUCong da da= db=) = SigUUCong (WeakTm' k T da) (WeakTmEq' k T da=) (WeakTmEq' (prev k) T db=)
WeakTmEq' k T {pair A B a b} (PairCong dA dA= dB= da= db=) = PairCong (WeakTy' k T dA) (WeakTyEq' k T dA=) (WeakTyEq' (prev k) T dB=) (WeakTmEq' k T da=) (congTmEqTy (! (weakenCommutesSubstTy k B a)) (WeakTmEq' k T db=))
WeakTmEq' k T (Pr1Cong dA dA= dB= du=) = Pr1Cong (WeakTy' k T dA) (WeakTyEq' k T dA=) (WeakTyEq' (prev k) T dB=) (WeakTmEq' k T du=)
WeakTmEq' k T {u = pr2 A B u} (Pr2Cong dA dA= dB= du=) rewrite ! (weakenCommutesSubstTy k B (pr1 A B u)) = Pr2Cong (WeakTy' k T dA) (WeakTyEq' k T dA=) (WeakTyEq' (prev k) T dB=) (WeakTmEq' k T du=)
WeakTmEq' k T NatUUCong = NatUUCong
WeakTmEq' k T ZeroCong = ZeroCong
WeakTmEq' k T (SucCong du=) = SucCong (WeakTmEq' k T du=)
WeakTmEq' k T (NatelimCong dP dP= ddO= ddS= du=) =
  let thing2 = ap weakenTy (ap (λ z → substTy z _) (weakenTyCommutesprev _ _) ∙ weakenCommutesSubstTy _ _ _) ∙ weakenTyCommutes _ _ in
  congTmEqTy (weakenCommutesSubstTy _ _ _) (NatelimCong (WeakTy' (prev k) T dP) (WeakTyEq' (prev k) T dP=) (congTmEqTy! (weakenCommutesSubstTy _ _ _) (WeakTmEq' k T ddO=)) (congTmEqTy! thing2 (WeakTmEq' (prev (prev k)) T ddS=)) (WeakTmEq' k T du=))
WeakTmEq' k T (IdUUCong da= du= dv=) = IdUUCong (WeakTmEq' k T da=) (WeakTmEq' k T du=) (WeakTmEq' k T dv=)
WeakTmEq' k T (ReflCong dA= da=) = ReflCong (WeakTyEq' k T dA=) (WeakTmEq' k T da=)
WeakTmEq' k T {u = jj A P d a b p} (JJCong dA dA= dP= dd= da= db= dp=) =
  congTmEqTy
    (! (weaken-subst3Ty P))
    (JJCong
      (WeakTy' k T dA)
      (WeakTyEq' k T dA=)
      (congTyCtxEq (Ctx+= (Ctx+= refl (! (weakenTyCommutes _ _))) (ap-id-Ty (! (ap weakenTy (weakenTyCommutes _ _) ∙ weakenTyCommutes _ _)) refl refl)) (WeakTyEq' (prev (prev (prev k))) T dP=))
      (congTmEqTy (weaken-subst3Ty (weakenTy' (prev (prev (prev last))) P) ∙ ap-subst3Ty (! (weakenTyCommutes3 _ P)) refl refl (ap-refl-Tm (! (weakenTyCommutes _ _)) refl)) (WeakTmEq' (prev k) T dd=))
      (WeakTmEq' k T da=)
      (WeakTmEq' k T db=)
      (WeakTmEq' k T dp=))
WeakTmEq' k T {u = app A B (lam A B u) a} (BetaPi dA dB du da) rewrite ! (weakenCommutesSubstTy k B a) | ! (weakenCommutesSubstTm k u a)= BetaPi (WeakTy' k T dA) (WeakTy' (prev k) T dB) (WeakTm' (prev k) T du) (WeakTm' k T da)
WeakTmEq' k T {u = pr1 A B (pair A B a b)} (BetaSig1 dA dB da db) = BetaSig1 (WeakTy' k T dA) (WeakTy' (prev k) T dB) (WeakTm' k T da) ((congTm (! (weakenCommutesSubstTy k B a)) refl (WeakTm' k T db)))
WeakTmEq' k T {u = pr2 A B (pair A B a b)} (BetaSig2 dA dB da db) rewrite ! (weakenCommutesSubstTy k B a) = BetaSig2 (WeakTy' k T dA) (WeakTy' (prev k) T dB) (WeakTm' k T da) (congTm (! (weakenCommutesSubstTy k B a)) refl (WeakTm' k T db))
WeakTmEq' k T {u = u} (BetaNatZero dP ddO ddS) =
  congTmEqTy (weakenCommutesSubstTy _ _ _) (BetaNatZero (WeakTy' _ T dP) (congTmTy! (weakenCommutesSubstTy _ _ _) (WeakTm' _ T ddO)) (congTmTy! (ap weakenTy (ap2 substTy (weakenTyCommutesprev _ _) refl ∙ weakenCommutesSubstTy _ _ _) ∙ weakenTyCommutes _ _) (WeakTm' _ T ddS)))
WeakTmEq' k T {u = u} (BetaNatSuc {dS = dS} dP ddO ddS du) =
  congTmEq refl (subst2-weakenTm dS) (weakenCommutesSubstTy _ _ _) (BetaNatSuc (WeakTy' _ T dP) (congTmTy! (weakenCommutesSubstTy _ _ _) (WeakTm' _ T ddO)) (congTmTy! (ap weakenTy (ap2 substTy (weakenTyCommutesprev _ _) refl ∙ weakenCommutesSubstTy _ _ _) ∙ weakenTyCommutes _ _) (WeakTm' _ T ddS)) (WeakTm' _ T du))
WeakTmEq' k T {u = u} (BetaIdRefl {d = d} dA dP dd da) =
  congTmEq refl (weakenCommutesSubstTm _ d _) (! (weaken-subst3Ty _))
    (BetaIdRefl
      (WeakTy' k T dA)
      (congTyCtx (Ctx+= (Ctx+= refl (! (weakenTyCommutes _ _))) (ap-id-Ty (! (ap weakenTy (weakenTyCommutes _ _) ∙ weakenTyCommutes _ _)) refl refl)) (WeakTy' (prev (prev (prev k))) T dP))
      (congTmTy (weaken-subst3Ty _ ∙ ap-subst3Ty (! (weakenTyCommutes3 _ _)) refl refl (ap-refl-Tm (! (weakenTyCommutes _ _)) refl)) (WeakTm' (prev k) T dd))
      (WeakTm' k T da))

WeakTy : {Γ : Ctx n}  (T : TyExpr n) {A : TyExpr n} → Derivable (Γ ⊢ A) → Derivable ((Γ , T) ⊢ weakenTy A)
WeakTm : {Γ : Ctx n} (T : TyExpr n) {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → Derivable ((Γ , T)  ⊢ weakenTm u :> weakenTy A)
WeakTyEq : {Γ : Ctx n} (T : TyExpr n) {A A' : TyExpr n} → Derivable (Γ ⊢ A == A') → Derivable ((Γ , T) ⊢ weakenTy A == weakenTy A')
WeakTmEq : {Γ : Ctx n} (T : TyExpr n) {u u' : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u == u' :> A) → Derivable ((Γ , T) ⊢ weakenTm u == weakenTm u' :> weakenTy A)

WeakTy = WeakTy' last
WeakTm = WeakTm' last
WeakTyEq = WeakTyEq' last
WeakTmEq = WeakTmEq' last



-- It does not seem easy to prove [SubstTyFullEq] directly instead of proving both [SubstTyEq] and
-- [SubstTyMorEq]. The reason is that in the [TySymm] case we would need [MorSymm] which is probably
-- bad for termination checking. On the other hand, neither [SubstTyEq] nor [SubstTyMorEq] require
-- [MorSymm]

-- Should those functions be replaced by [SubstTyMorEq2]?

SubstTyFullEq : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m} → Derivable (Δ ⊢ A') → (Γ ⊢ δ ∷> Δ)
       → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
SubstTyFullEq dA' dδ dA= dδ= = TyTran (SubstTy dA' dδ) (SubstTyEq dA= dδ) (SubstTyMorEq dA' dδ dδ=)

SubstTmFullEq : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m} →  Derivable (Δ ⊢ u' :> A) → (Γ ⊢ δ ∷> Δ) 
       → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u' [ δ' ]Tm :> A [ δ ]Ty)
SubstTmFullEq du' dδ du= dδ= = TmTran (SubstTm du' dδ) (SubstTmEq du= dδ) (SubstTmMorEq du' dδ dδ=)


SubstMor : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ : Mor m k} {δ : Mor n m} → (Δ ⊢ θ ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ θ [ δ ]Mor ∷> Θ)
SubstMor {Θ = ◇} {θ = ◇} tt dδ = tt
SubstMor {Θ = Θ , C} {θ = θ , w} (dθ , dw) dδ = (SubstMor dθ dδ , congTm ([]Ty-assoc _ θ C) refl (SubstTm dw dδ))

SubstMorEq : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ θ' : Mor m k} {δ : Mor n m} → (Δ ⊢ θ == θ' ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ' [ δ ]Mor ∷> Θ)
SubstMorEq {Θ = ◇} {θ = ◇} {θ' = ◇} dθ= dδ = tt
SubstMorEq {Θ = Θ , C} {θ = θ , w} {θ' = θ' , w'} (dθ= , dw) dδ = SubstMorEq dθ= dδ , congTmEqTy ([]Ty-assoc _ θ C) (SubstTmEq dw dδ)


SubstMorMorEq : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ : Mor m k} {δ δ' : Mor n m} → (Δ ⊢ θ ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ [ δ' ]Mor ∷> Θ)
SubstMorMorEq {Θ = ◇} {◇} tt dδ dδ= = tt
SubstMorMorEq {Θ = Θ , C} {θ , w} (dθ , dw) dδ dδ= = SubstMorMorEq dθ dδ dδ= , congTmEqTy ([]Ty-assoc _ θ C) (SubstTmMorEq dw dδ dδ=)




{- Derivability of the identity morphism -}

idMorDerivable : {Γ : Ctx n} →  ⊢ Γ → (Γ ⊢ idMor n ∷> Γ)
idMorDerivable {Γ = ◇} tt = tt
idMorDerivable {Γ = Γ , A} (dΓ , dA) = WeakMor A (idMorDerivable dΓ) , congTm (ap weakenTy (! ([idMor]Ty A)) ∙ weaken[]Ty A (idMor _) last) refl (VarLast dA)


{- Conversion rules for types and terms are admissible -}

ConvTy : {Γ Δ : Ctx n} {A : TyExpr n} → Derivable (Γ ⊢ A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ A)
ConvTyEq : {Γ Δ : Ctx n} {A B : TyExpr n} → Derivable (Γ ⊢ A == B) → (⊢ Γ == Δ) → Derivable (Δ ⊢ A == B)
ConvTm : {Γ Δ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ u :> A)
ConvTmEq : {Γ Δ : Ctx n} {A : TyExpr n} {u v : TmExpr n} → Derivable (Γ ⊢ u == v :> A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ u == v :> A)

ConvTm2' : {Γ Δ : Ctx n} {u : TmExpr n} {A A' : TyExpr n} → Derivable (Γ ⊢ u :> A) → (⊢ Γ == Δ) → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A') → Derivable (Δ ⊢ u :> A')
ConvTm2' du dΓ= dA dA= = Conv (ConvTy dA dΓ=) (ConvTm du dΓ=) (ConvTyEq dA= dΓ=)

ConvTy {Γ = Γ} {Δ = Δ} {A = A} (Pi dA dB) dΓ= = Pi (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
ConvTy UU dΓ= = UU
ConvTy (El dv) dΓ= = El (ConvTm dv dΓ=)
ConvTy (Sig dA dB) dΓ= = Sig (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
ConvTy Nat dΓ= = Nat
ConvTy (Id dA da db) dΓ= = Id (ConvTy dA dΓ=) (ConvTm da dΓ=) (ConvTm db dΓ=)

ConvTyEq (TySymm dA=) dΓ= = TySymm (ConvTyEq dA= dΓ=)
ConvTyEq (TyTran dB dA= dB=) dΓ= = TyTran (ConvTy dB dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= dΓ=)
ConvTyEq (PiCong dA dA= dB=) dΓ= = PiCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
ConvTyEq UUCong dΓ= = UUCong
ConvTyEq (ElCong dv=) dΓ= = ElCong (ConvTmEq dv= dΓ=)
ConvTyEq ElUU= dΓ= = ElUU=
ConvTyEq (ElPi= da db) dΓ= = ElPi= (ConvTm da dΓ=) (ConvTm db (dΓ= , El da , ConvTy (El da) dΓ= , TyRefl (El da) , TyRefl (ConvTy (El da) dΓ=)))
ConvTyEq (SigCong dA dA= dB=) dΓ= = SigCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
ConvTyEq (ElSig= da db) dΓ= = ElSig= (ConvTm da dΓ=) (ConvTm db ((dΓ= , El da , ConvTy (El da) dΓ= , TyRefl (El da) , TyRefl (ConvTy (El da) dΓ=))))
ConvTyEq NatCong dΓ= = NatCong
ConvTyEq ElNat= dΓ= = ElNat=
ConvTyEq (IdCong dA= da= db=) dΓ= = IdCong (ConvTyEq dA= dΓ=)  (ConvTmEq da= dΓ=) (ConvTmEq db= dΓ=)
ConvTyEq (ElId= da du dv) dΓ= = ElId= (ConvTm da dΓ=) (ConvTm du dΓ=) (ConvTm dv dΓ=)


ConvTm {Δ = Δ , B} {var last} (VarLast {A = A} dA) (dΓ= , dA' , dB , dA= , dA=') = Conv (WeakTy B dB) (VarLast dB) (WeakTyEq B (TySymm dA='))
ConvTm {Γ = Γ , A} {Δ = Δ , B} (VarPrev dA dk) (dΓ= , dA , dB , dA=) = VarPrev (ConvTy dA dΓ=) (ConvTm dk dΓ=)
ConvTm (Conv dA du dA=) dΓ= = Conv (ConvTy dA dΓ=) (ConvTm du dΓ=) (ConvTyEq dA= dΓ=)
ConvTm (Lam dA dB du) dΓ= = Lam (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm du (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
ConvTm (App dA dB df da) dΓ= = App (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm df dΓ=) (ConvTm da dΓ=)
ConvTm UUUU dΓ= = UUUU
ConvTm (PiUU da db) dΓ= = PiUU (ConvTm da dΓ=) (ConvTm db (dΓ= , El da , ConvTy (El da) dΓ= , TyRefl (El da) , TyRefl (ConvTy (El da) dΓ=)))
ConvTm (SigUU da db) dΓ= = SigUU (ConvTm da dΓ=) (ConvTm db (dΓ= , El da , ConvTy (El da) dΓ= , TyRefl (El da) , TyRefl (ConvTy (El da) dΓ=)))
ConvTm (Pair dA dB da db) dΓ= = Pair (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm da dΓ=) (ConvTm db dΓ=)
ConvTm (Pr1 dA dB du) dΓ= = Pr1 (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm du dΓ=)
ConvTm (Pr2 dA dB du) dΓ= = Pr2 (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm du dΓ=)
ConvTm NatUU dΓ= = NatUU
ConvTm Zero dΓ= = Zero
ConvTm (Suc du) dΓ= = Suc (ConvTm du dΓ=)
ConvTm (Natelim dP ddO ddS du) dΓ= = Natelim (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)) (ConvTm ddO dΓ=) (ConvTm ddS ((dΓ= , Nat , Nat , NatCong , NatCong) , dP , ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong) , TyRefl dP , TyRefl (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)))) (ConvTm du dΓ=)
ConvTm (IdUU da du dv) dΓ= = IdUU (ConvTm da dΓ=) (ConvTm du dΓ=) (ConvTm dv dΓ=)
ConvTm (Refl dA da) dΓ= = Refl (ConvTy dA dΓ=) (ConvTm da dΓ=)
ConvTm (JJ dA dP dd da db dp) dΓ= = JJ (ConvTy dA dΓ=) (ConvTy dP ((((dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)) , WeakTy _ dA , WeakTy _ (ConvTy dA dΓ=) , TyRefl (WeakTy _ dA) , TyRefl (WeakTy _ (ConvTy dA dΓ=))) , Id (WeakTy _ (WeakTy _ dA)) (VarPrev (WeakTy _ dA) (VarLast dA)) (VarLast (WeakTy _ dA)) , Id (WeakTy _ (WeakTy _ (ConvTy dA dΓ=))) (VarPrev (WeakTy _ (ConvTy dA dΓ=)) (VarLast (ConvTy dA dΓ=))) (VarLast (WeakTy _ (ConvTy dA dΓ=))) , TyRefl (Id (WeakTy _ (WeakTy _ dA)) (VarPrev (WeakTy _ dA) (VarLast dA)) (VarLast (WeakTy _ dA))) , TyRefl (Id (WeakTy _ (WeakTy _ (ConvTy dA dΓ=))) (VarPrev (WeakTy _ (ConvTy dA dΓ=)) (VarLast (ConvTy dA dΓ=))) (VarLast (WeakTy _ (ConvTy dA dΓ=))))))) (ConvTm dd (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm da dΓ=) (ConvTm db dΓ=) (ConvTm dp dΓ=)

ConvTmEq  {Δ = Δ , B} (VarLastCong {A = A} dA) (dΓ= , dA' , dB , dA= , dA=') = ConvEq (WeakTy B dB) (VarLastCong dB) (WeakTyEq B (TySymm dA='))
ConvTmEq {Γ = Γ , B} {Δ , B'} (VarPrevCong {A = A} dA dk=) (dΓ= , dA , dB , dA=) = VarPrevCong (ConvTy dA dΓ=) (ConvTmEq dk= dΓ=)
ConvTmEq (TmSymm du=) dΓ= = TmSymm (ConvTmEq du= dΓ=)
ConvTmEq (TmTran dv du= dv=) dΓ= = TmTran (ConvTm dv dΓ=) (ConvTmEq du= dΓ=) (ConvTmEq dv= dΓ=)
ConvTmEq (ConvEq dA du= dA=) dΓ= = ConvEq (ConvTy dA dΓ=) (ConvTmEq du= dΓ=) (ConvTyEq dA= dΓ=)
ConvTmEq UUUUCong dΓ= = UUUUCong
ConvTmEq (PiUUCong da da= db=) dΓ= = PiUUCong (ConvTm da dΓ=) (ConvTmEq da= dΓ=) (ConvTmEq db= (dΓ= , El da , ConvTy (El da) dΓ= , TyRefl (El da) , TyRefl (ConvTy (El da) dΓ=)))
ConvTmEq (LamCong dA dA= dB= du=) dΓ= = LamCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq du= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
ConvTmEq (AppCong dA dA= dB= df= da=) dΓ= = AppCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq df= dΓ=) (ConvTmEq da= dΓ=)
ConvTmEq (SigUUCong da da= db=) dΓ= = SigUUCong (ConvTm da dΓ=) (ConvTmEq da= dΓ=) (ConvTmEq db= (dΓ= , El da , ConvTy (El da) dΓ= , TyRefl (El da) , TyRefl (ConvTy (El da) dΓ=)))
ConvTmEq (PairCong dA dA= dB= da= db=) dΓ= = PairCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq da= dΓ=) (ConvTmEq db= dΓ=)
ConvTmEq (Pr1Cong dA dA= dB= du=) dΓ= = Pr1Cong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq du= dΓ=)
ConvTmEq (Pr2Cong dA dA= dB= du=) dΓ= = Pr2Cong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dB= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq du= dΓ=)
ConvTmEq NatUUCong dΓ= = NatUUCong
ConvTmEq ZeroCong dΓ= = ZeroCong
ConvTmEq (SucCong du=) dΓ= = SucCong (ConvTmEq du= dΓ=)
ConvTmEq (NatelimCong dP dP= ddO= ddS= du=) dΓ= = NatelimCong (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)) (ConvTyEq dP= (dΓ= , Nat , Nat , NatCong , NatCong)) (ConvTmEq ddO= dΓ=) (ConvTmEq ddS= ((dΓ= , Nat , Nat , NatCong , NatCong) , dP , ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong) , TyRefl dP , TyRefl (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)))) (ConvTmEq du= dΓ=)
ConvTmEq (IdUUCong da= du= dv=) dΓ= = IdUUCong (ConvTmEq da= dΓ=) (ConvTmEq du= dΓ=) (ConvTmEq dv= dΓ=)
ConvTmEq (ReflCong dA= da=) dΓ= = ReflCong (ConvTyEq dA= dΓ=) (ConvTmEq da= dΓ=)
ConvTmEq (JJCong dA dA= dP= dd= da= db= dp=) dΓ= = JJCong (ConvTy dA dΓ=) (ConvTyEq dA= dΓ=) (ConvTyEq dP= ((((dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)) , WeakTy _ dA , WeakTy _ (ConvTy dA dΓ=) , TyRefl (WeakTy _ dA) , TyRefl (WeakTy _ (ConvTy dA dΓ=))) , Id (WeakTy _ (WeakTy _ dA)) (VarPrev (WeakTy _ dA) (VarLast dA)) (VarLast (WeakTy _ dA)) , Id (WeakTy _ (WeakTy _ (ConvTy dA dΓ=))) (VarPrev (WeakTy _ (ConvTy dA dΓ=)) (VarLast (ConvTy dA dΓ=))) (VarLast (WeakTy _ (ConvTy dA dΓ=))) , TyRefl (Id (WeakTy _ (WeakTy _ dA)) (VarPrev (WeakTy _ dA) (VarLast dA)) (VarLast (WeakTy _ dA))) , TyRefl (Id (WeakTy _ (WeakTy _ (ConvTy dA dΓ=))) (VarPrev (WeakTy _ (ConvTy dA dΓ=)) (VarLast (ConvTy dA dΓ=))) (VarLast (WeakTy _ (ConvTy dA dΓ=))))))) (ConvTmEq dd= (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTmEq da= dΓ=) (ConvTmEq db= dΓ=) (ConvTmEq dp= dΓ=)
ConvTmEq (BetaPi dA dB du da) dΓ= = BetaPi (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm du (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm da dΓ=)
ConvTmEq (BetaSig1 dA dB da db) dΓ= = BetaSig1 (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm da dΓ=) (ConvTm db dΓ=)
ConvTmEq (BetaSig2 dA dB da db) dΓ= = BetaSig2 (ConvTy dA dΓ=) (ConvTy dB (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))) (ConvTm da dΓ=) (ConvTm db dΓ=)
ConvTmEq (BetaNatZero dP ddO ddS) dΓ= = BetaNatZero (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)) (ConvTm ddO dΓ=) (ConvTm ddS ((dΓ= , Nat , Nat , NatCong , NatCong) , dP , ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong) , TyRefl dP , TyRefl (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong))))
ConvTmEq (BetaNatSuc dP ddO ddS du) dΓ= = BetaNatSuc (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)) (ConvTm ddO dΓ=) (ConvTm ddS ((dΓ= , Nat , Nat , NatCong , NatCong) , dP , ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong) , TyRefl dP , TyRefl (ConvTy dP (dΓ= , Nat , Nat , NatCong , NatCong)))) (ConvTm du dΓ=)
ConvTmEq (BetaIdRefl dA dP dd da) dΓ= =
  BetaIdRefl
    (ConvTy dA dΓ=)
    (ConvTy dP (((dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=))
               , (WeakTy _ dA , WeakTy _ (ConvTy dA dΓ=) , TyRefl (WeakTy _ dA) , TyRefl (WeakTy _ (ConvTy dA dΓ=))))
               , (Id (WeakTy _ (WeakTy _ dA)) (VarPrev (WeakTy _ dA) (VarLast dA)) (VarLast (WeakTy _ dA))
                , Id (WeakTy _ (WeakTy _ (ConvTy dA dΓ=))) (VarPrev (WeakTy _ (ConvTy dA dΓ=)) (VarLast (ConvTy dA dΓ=))) (VarLast (WeakTy _ (ConvTy dA dΓ=)))
                , TyRefl (Id (WeakTy _ (WeakTy _ dA)) (VarPrev (WeakTy _ dA) (VarLast dA)) (VarLast (WeakTy _ dA)))
                , TyRefl (Id (WeakTy _ (WeakTy _ (ConvTy dA dΓ=))) (VarPrev (WeakTy _ (ConvTy dA dΓ=)) (VarLast (ConvTy dA dΓ=))) (VarLast (WeakTy _ (ConvTy dA dΓ=)))))))
    (ConvTm dd (dΓ= , dA , ConvTy dA dΓ= , TyRefl dA , TyRefl (ConvTy dA dΓ=)))
    (ConvTm da dΓ=)

{- Subst3 -}

Subst1Tm : {Γ : Ctx n} {B : TyExpr n} {A : TyExpr (suc n)} {t : TmExpr (suc n)} {u : TmExpr n}
         → ⊢ Γ → Derivable ((Γ , B) ⊢ t :> A) → Derivable (Γ ⊢ u :> B)
         → Derivable (Γ ⊢ substTm t u :> substTy A u)
Subst1Tm dΓ dt du = SubstTm dt (idMorDerivable dΓ , congTmTy! ([idMor]Ty _) du)

Subst3Ty : {Γ : Ctx n} {B : TyExpr n} {C : TyExpr (suc n)} {D : TyExpr (suc (suc n))} {A : TyExpr (suc (suc (suc n)))} {u v w : TmExpr n}
         → ⊢ Γ → Derivable ((((Γ , B) , C) , D) ⊢ A) → Derivable (Γ ⊢ u :> B) → Derivable (Γ ⊢ v :> substTy C u) → Derivable (Γ ⊢ w :> subst2Ty D u v)
         → Derivable (Γ ⊢ subst3Ty A u v w)
Subst3Ty dΓ dA du dv dw = SubstTy dA (((idMorDerivable dΓ , (congTmTy! ([idMor]Ty _) du)) , dv) , dw)

Subst3TyEq : {Γ : Ctx n} {B : TyExpr n} {C : TyExpr (suc n)} {D : TyExpr (suc (suc n))} {A A' : TyExpr (suc (suc (suc n)))} {u u' v v' w w' : TmExpr n}
           → ⊢ Γ → Derivable ((((Γ , B) , C) , D) ⊢ A') → Derivable (Γ ⊢ u :> B) → Derivable (Γ ⊢ v :> substTy C u) → Derivable (Γ ⊢ w :> subst2Ty D u v)
           → Derivable ((((Γ , B) , C) , D) ⊢ A == A') → Derivable (Γ ⊢ u == u' :> B) → Derivable (Γ ⊢ v == v' :> substTy C u) → Derivable (Γ ⊢ w == w' :> subst2Ty D u v)
           → Derivable (Γ ⊢ subst3Ty A u v w == subst3Ty A' u' v' w')
Subst3TyEq dΓ dA' du dv dw dA= du= dv= dw= = SubstTyFullEq dA' (((idMorDerivable dΓ , congTmTy! ([idMor]Ty _) du) , dv) , dw) dA= (((MorRefl (idMorDerivable dΓ) , congTmEqTy! ([idMor]Ty _) du=) , dv=) , dw=)

{- Various other admissible rules -}

CtxSymm : {Γ Δ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Γ
CtxSymm {Γ = ◇} {Δ = ◇} tt = tt
CtxSymm {Γ = Γ , A} {Δ , B} (dΓ= , dA , dB , dA= , dA=') = (CtxSymm dΓ=) , dB , dA , TySymm dA=' , TySymm dA=

CtxTran : {Γ Δ Θ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Θ → ⊢ Γ == Θ
CtxTran {Γ = ◇} {Δ = ◇} {Θ = ◇} tt tt = tt
CtxTran {Γ = Γ , A} {Δ , B} {Θ , C} (dΓ= , dA , dB , dA= , dA=') (dΔ= , dB' , dC , dB= , dB=') = CtxTran dΓ= dΔ= , dA , dC , TyTran (ConvTy dB (CtxSymm dΓ=)) dA= (ConvTyEq dB= (CtxSymm dΓ=)) , TyTran (ConvTy dB dΔ=) (ConvTyEq dA=' dΔ=) dB='


CtxEqCtx1 : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' → ⊢ Γ
CtxEqCtx1 {Γ = ◇} {Γ' = ◇} tt = tt
CtxEqCtx1 {Γ = Γ , A} {Γ' , A'} (dΓ= , dA , dA' , dA=) = (CtxEqCtx1 dΓ=) , dA

CtxEqCtx2 : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' → ⊢ Γ'
CtxEqCtx2 {Γ = ◇} {Γ' = ◇} tt = tt
CtxEqCtx2 {Γ = Γ , A} {Γ' = Γ' , A'} (dΓ= , dA , dA' , dA=) = CtxEqCtx2 dΓ= , dA'



TyEqTy1 : {Γ : Ctx n} {A B : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A)
TyEqTy2 : {Γ : Ctx n} {A B : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B)
TmEqTm1 : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u :> A)
TmEqTm2 : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u' :> A)

TyEqTy1 dΓ (TySymm dA=) = TyEqTy2 dΓ dA=
TyEqTy1 dΓ (TyTran dB dA= dB=) = TyEqTy1 dΓ dA=
TyEqTy1 dΓ (PiCong dA dA= dB=) = Pi dA (TyEqTy1 (dΓ , dA) dB=)
TyEqTy1 dΓ UUCong = UU
TyEqTy1 dΓ (ElCong dv=) = El (TmEqTm1 dΓ dv=) 
TyEqTy1 dΓ ElUU= = El UUUU
TyEqTy1 dΓ (ElPi= da db) = El (PiUU da db)
TyEqTy1 dΓ (SigCong dA dA= dB=) = Sig dA (TyEqTy1 (dΓ , dA) dB=)
TyEqTy1 dΓ (ElSig= da db) = El (SigUU da db)
TyEqTy1 dΓ NatCong = Nat
TyEqTy1 dΓ ElNat= = El NatUU
TyEqTy1 dΓ (IdCong dA= da= db=) = Id (TyEqTy1 dΓ dA=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)
TyEqTy1 dΓ (ElId= da du dv) = El (IdUU da du dv)


TyEqTy2 dΓ (TySymm dA=) = TyEqTy1 dΓ dA=
TyEqTy2 dΓ (TyTran dB dA= dB=) = TyEqTy2 dΓ dB=
TyEqTy2 dΓ (PiCong dA dA= dB=) = Pi (TyEqTy2 dΓ dA=) (ConvTy (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) ((CtxRefl dΓ) , dA , TyEqTy2 dΓ dA= , dA= , dA=))
TyEqTy2 dΓ UUCong = UU
TyEqTy2 dΓ (ElCong dv=) = El (TmEqTm2 dΓ dv=)
TyEqTy2 dΓ ElUU= = UU
TyEqTy2 dΓ (ElPi= da db) = Pi (El da) (El db)
TyEqTy2 dΓ (SigCong dA dA= dB=) = Sig (TyEqTy2 dΓ dA=) (ConvTy (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) ((CtxRefl dΓ) , dA , TyEqTy2 dΓ dA= , dA= , dA=))
TyEqTy2 dΓ (ElSig= da db) = Sig (El da) (El db)
TyEqTy2 dΓ NatCong = Nat
TyEqTy2 dΓ ElNat= = Nat
TyEqTy2 dΓ (IdCong dA= da= db=) = Id (TyEqTy2 dΓ dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ da=) dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ db=) dA=)
TyEqTy2 dΓ (ElId= da du dv) = Id (El da) du dv

TmEqTm1 dΓ (VarLastCong dA) = VarLast dA
TmEqTm1 (dΓ , dA) (VarPrevCong dA' dk=) = VarPrev dA' (TmEqTm1 dΓ dk=)
TmEqTm1 dΓ (TmSymm du=) = TmEqTm2 dΓ du= 
TmEqTm1 dΓ (TmTran dv du= dv=) = TmEqTm1 dΓ du=
TmEqTm1 dΓ (ConvEq dA du= dA=) = Conv dA (TmEqTm1 dΓ du=) dA=
TmEqTm1 dΓ UUUUCong = UUUU
TmEqTm1 dΓ (PiUUCong da da= db=) = PiUU da (TmEqTm1 (dΓ , El da) db=)
TmEqTm1 dΓ (LamCong dA dA= dB= du=) = Lam (TyEqTy1 dΓ dA=) (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 (dΓ , dA) du=)
TmEqTm1 dΓ (AppCong dA dA= dB= df= da=) = App (TyEqTy1 dΓ dA=) (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 dΓ df=) (TmEqTm1 dΓ da=)
TmEqTm1 dΓ (SigUUCong da da= db=) = SigUU da (TmEqTm1 (dΓ , El da) db=)
TmEqTm1 dΓ (PairCong dA dA= dB= da= db=) = Pair dA (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)
TmEqTm1 dΓ (Pr1Cong dA dA= dB= du=) = Pr1 dA (TyEqTy1  (dΓ , dA) dB=) (TmEqTm1 dΓ du=)
TmEqTm1 dΓ (Pr2Cong dA dA= dB= du=) = Pr2 dA (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 dΓ du=)
TmEqTm1 dΓ NatUUCong = NatUU
TmEqTm1 dΓ ZeroCong = Zero
TmEqTm1 dΓ (SucCong du=) = Suc (TmEqTm1 dΓ du=)
TmEqTm1 dΓ (NatelimCong dP dP= ddO= ddS= du=) = Natelim (TyEqTy1 (dΓ , Nat) dP=) (TmEqTm1 dΓ ddO=) (TmEqTm1 ((dΓ , Nat) , dP) ddS=) (TmEqTm1 dΓ du=)
TmEqTm1 dΓ (IdUUCong da= du= dv=) = IdUU (TmEqTm1 dΓ da=) (TmEqTm1 dΓ du=) (TmEqTm1 dΓ dv=)
TmEqTm1 dΓ (ReflCong dA= da=) = Refl (TyEqTy1 dΓ dA=) (TmEqTm1 dΓ da=)
TmEqTm1 dΓ (JJCong dA dA= dP= dd= da= db= dp=) = JJ dA (TyEqTy1 (((dΓ , dA) , (WeakTy _ dA)) , (Id (WeakTy _ (WeakTy _ dA)) (VarPrev (WeakTy _ dA) (VarLast dA)) (VarLast (WeakTy _ dA)))) dP=) (TmEqTm1 (dΓ , dA) dd=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=) (TmEqTm1 dΓ dp=)
TmEqTm1 dΓ (BetaPi dA dB du da) = App dA dB (Lam dA dB du) da
TmEqTm1 dΓ (BetaSig1 dA dB da db) = Pr1 dA dB (Pair dA dB da db)
TmEqTm1 dΓ (BetaSig2 {B = B} dA dB da db) = Conv (SubstTy dB ((idMorDerivable dΓ) , (congTm (! ([idMor]Ty _)) refl (Pr1 dA dB (Pair dA dB da db))))) (Pr2 dA dB (Pair dA dB da db)) (SubstTyMorEq dB ((idMorDerivable dΓ) , (congTm (! ([idMor]Ty _)) refl (Pr1 dA dB (Pair dA dB da db)))) ((MorRefl (idMorDerivable dΓ)) , (congTmEqTy (! ([idMor]Ty _)) (BetaSig1 dA dB da db))))
TmEqTm1 dΓ (BetaNatZero dP ddO ddS) = Natelim dP ddO ddS Zero
TmEqTm1 dΓ (BetaNatSuc dP ddO ddS du) = Natelim dP ddO ddS (Suc du)
TmEqTm1 dΓ (BetaIdRefl dA dP dd da) = JJ dA dP dd da da (Refl dA da)

TmEqTm2 dΓ (VarLastCong dA) = VarLast dA
TmEqTm2 (dΓ , dA) (VarPrevCong dA' dk=) = VarPrev dA' (TmEqTm2 dΓ dk=)
TmEqTm2 dΓ (TmSymm du=) = TmEqTm1 dΓ du=
TmEqTm2 dΓ (TmTran dv du= dv=) = TmEqTm2 dΓ dv=
TmEqTm2 dΓ (ConvEq dA du= dA=) =  Conv dA (TmEqTm2 dΓ du=) dA=
TmEqTm2 dΓ UUUUCong = UUUU
TmEqTm2 dΓ (PiUUCong da da= db=) = PiUU (TmEqTm2 dΓ da=) (ConvTm (TmEqTm2 (dΓ , El da) db=) (CtxRefl dΓ , El da , El (TmEqTm2 dΓ da=) , ElCong da= , ElCong da=))
TmEqTm2 dΓ (LamCong dA dA= dB= du=) = Conv
             (Pi
               (TyEqTy2 dΓ dA=)
               (ConvTy (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) ((CtxRefl dΓ) , dA , TyEqTy2 dΓ dA= , dA= , dA=))
             )
             (Lam
               (TyEqTy2 dΓ dA=)
               (ConvTy (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) ((CtxRefl dΓ) , dA , TyEqTy2 dΓ dA= , dA= , dA=))
               (ConvTm (Conv (TyEqTy1 (dΓ , dA) dB=) (TmEqTm2 (dΓ , dA) du=) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=)))
             (PiCong
               (TyEqTy2 dΓ dA=)
               (TySymm dA=)
               (ConvTyEq (TySymm dB=) (CtxRefl dΓ , dA , ConvTy (TyEqTy2 dΓ dA=) (CtxRefl dΓ) , dA= , dA=))
             )             
TmEqTm2 dΓ (AppCong dA dA= dB= df= da=) = Conv
             (SubstTy (TyEqTy2 (dΓ , dA) dB=) ((idMorDerivable dΓ) , (Conv dA (TmEqTm2 dΓ da=) (congTyEq refl (! ([idMor]Ty _)) (TyRefl dA)))))
             (App
               (TyEqTy2 dΓ dA=)
               (ConvTy (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) ((CtxRefl dΓ) , dA , TyEqTy2 dΓ dA= , dA= , dA=))
               (Conv (Pi dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ df=) (PiCong dA dA= dB=))
               (Conv dA (TmEqTm2 dΓ da=) dA=)
             )
             (TySymm
               (SubstTyFullEq
                 (TyEqTy2 (dΓ , dA) dB=)
                 (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl (TmEqTm1 dΓ da=))
                 dB=
                 ((MorRefl (idMorDerivable dΓ)) , (congTmEqTy (! ([idMor]Ty _)) da=))
               )
             )
TmEqTm2 dΓ (SigUUCong da da= db=) = SigUU (TmEqTm2 dΓ da=) (ConvTm (TmEqTm2 (dΓ , El da) db=) (CtxRefl dΓ , El da , El (TmEqTm2 dΓ da=) , ElCong da= , ElCong da=))
TmEqTm2 {Γ = Γ} dΓ (PairCong dA dA= dB= da= db=) = Conv
             (Sig
               (TyEqTy2 dΓ dA=)
               (ConvTy (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=))
             )
             (Pair
               (TyEqTy2 dΓ dA=)
               (ConvTy (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=))
               (Conv dA (TmEqTm2 dΓ da=) dA=)
               (Conv
                 (SubstTy (TyEqTy1 (dΓ , dA) dB=) (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl (TmEqTm1 dΓ da=)))
                 (TmEqTm2 dΓ db=)
                 (SubstTyFullEq
                   (TyEqTy2 (dΓ , dA) dB=)
                   (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl (TmEqTm1 dΓ da=))
                   dB=
                   ((MorRefl (idMorDerivable dΓ)) , (congTmEqTy (! ([idMor]Ty _)) da=))
                 )
               )
             )
             (SigCong
               (TyEqTy2 dΓ dA=)
               (TySymm dA=)
               (ConvTyEq (TySymm dB=)
               (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=))
             )
TmEqTm2 dΓ (Pr1Cong dA dA= dB= du=) = Conv
             (TyEqTy2 dΓ dA=)
             (Pr1
               (TyEqTy2 dΓ dA=)
               (ConvTy (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=))
               (Conv (Sig dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ du=) (SigCong dA dA= dB=))
             )
             (TySymm dA=)
TmEqTm2 dΓ (Pr2Cong dA dA= dB= du=) = Conv (SubstTy (TyEqTy2 (dΓ , dA) dB=) (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl (Conv (TyEqTy2 dΓ dA=) (Pr1 (TyEqTy2 dΓ dA=) (ConvTy (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=)) (Conv (Sig dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ du=) (SigCong dA dA= dB=))) (TySymm dA=)))) (Pr2 (TyEqTy2 dΓ dA=) (ConvTy (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=)) (Conv (Sig dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ du=) (SigCong dA dA= dB=))) (SubstTyFullEq (TyEqTy1 (dΓ , dA) dB=) (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl (Conv (TyEqTy2 dΓ dA=) (Pr1 (TyEqTy2 dΓ dA=) (ConvTy (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , dA , TyEqTy2 dΓ dA= , dA= , dA=)) (Conv (Sig dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ du=) (SigCong dA dA= dB=))) (TySymm dA=))) (TySymm dB=) ((MorRefl (idMorDerivable dΓ)) , (TmSymm (congTmEqTy (! ([idMor]Ty _)) (Pr1Cong dA dA= dB= du=)))))
TmEqTm2 dΓ NatUUCong = NatUU
TmEqTm2 dΓ ZeroCong = Zero
TmEqTm2 dΓ (SucCong du=) = Suc (TmEqTm2 dΓ du=)
TmEqTm2 dΓ (NatelimCong dP dP= ddO= ddS= du=) =
  let dP' = TyEqTy2 (dΓ , Nat) dP= in
  let ddO' = Conv (SubstTy dP (idMorDerivable dΓ , Zero)) (TmEqTm2 dΓ ddO=) (SubstTyEq dP= (idMorDerivable dΓ , Zero)) in
  let ddS' = ConvTm2' (TmEqTm2 ((dΓ , Nat) , dP) ddS=) (CtxRefl (dΓ , Nat) , dP , dP' , dP= , dP=) (WeakTy _ (SubstTy (WeakTy' _ _ dP) (idMorDerivable (dΓ , Nat) , Suc (VarLast Nat)))) (WeakTyEq _ (SubstTyEq (WeakTyEq' _ _ dP=) (idMorDerivable (dΓ , Nat) , (Suc (VarLast Nat))))) in
  let du' = TmEqTm2 dΓ du= in
  Conv (SubstTy dP' (idMorDerivable dΓ , du')) (Natelim dP' ddO' ddS' du') (TySymm (SubstTyFullEq dP' (idMorDerivable dΓ , TmEqTm1 dΓ du=) dP= (MorRefl (idMorDerivable dΓ) , du=)))
TmEqTm2 dΓ (IdUUCong da= du= dv=) = IdUU (TmEqTm2 dΓ da=) (Conv (El (TmEqTm1 dΓ da=)) (TmEqTm2 dΓ du=) (ElCong da=)) (Conv (El (TmEqTm1 dΓ da=)) (TmEqTm2 dΓ dv=) (ElCong da=))
TmEqTm2 dΓ (ReflCong dA= da=) = Conv (Id (TyEqTy2 dΓ dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ da=) dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ da=) dA=)) (Refl (TyEqTy2 dΓ dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ da=) dA=)) (IdCong (TySymm dA=) (ConvEq (TyEqTy1 dΓ dA=) (TmSymm da=) dA=) (ConvEq (TyEqTy1 dΓ dA=) (TmSymm da=) dA=))
TmEqTm2 dΓ (JJCong dA dA= dP= dd= da= db= dp=) =
          let dA' = TyEqTy2 dΓ dA=
              dP' = ConvTy (TyEqTy2 (((dΓ , dA) , (WeakTy _ dA)) , (Id (WeakTy _ (WeakTy _ dA)) (VarPrev (WeakTy _ dA) (VarLast dA)) (VarLast (WeakTy _ dA)))) dP=) (((CtxRefl dΓ , dA , dA' , dA= , dA=) , WeakTy _ dA , WeakTy _ dA' , WeakTyEq _ dA= , WeakTyEq _ dA=) , Id (WeakTy _ (WeakTy _ dA)) (VarPrev (WeakTy _ dA) (VarLast dA)) (VarLast (WeakTy _ dA)) , Id (WeakTy _ (WeakTy _ dA')) (VarPrev (WeakTy _ dA') (VarLast dA')) (VarLast (WeakTy _ dA')) , IdCong (WeakTyEq _ (WeakTyEq _ dA=)) (VarPrevCong (WeakTy _ dA) (VarLastCong dA)) (VarLastCong (WeakTy _ dA)) , IdCong (WeakTyEq _ (WeakTyEq _ dA=)) (VarPrevCong (WeakTy _ dA) (ConvTmEq (VarLastCong dA) ((CtxRefl dΓ) , dA , dA' , dA= , dA=))) (ConvTmEq (VarLastCong (WeakTy _ dA)) (((CtxRefl dΓ) , (dA , dA' , dA= , dA=)) , WeakTy _ dA , WeakTy _ dA' , WeakTyEq _ dA= , WeakTyEq _ dA=)))
              dd' = ConvTm2' (TmEqTm2 (dΓ , dA) dd=) (CtxRefl dΓ , dA , dA' , dA= , dA=) (Subst3Ty (dΓ , dA) (WeakTy' _ _ (TyEqTy1 (((dΓ , dA) , WeakTy _ dA) , Id (WeakTy _ (WeakTy _ dA)) (VarPrev (WeakTy _ dA) (VarLast dA)) (VarLast (WeakTy _ dA))) dP=)) (VarLast dA) (congTmTy! (weakenTyInsert' _ _ _ _ ∙ [idMor]Ty _) (VarLast dA)) (congTmTy! (ap-id-Ty (weakenTyInsert' _ _ _ _ ∙ weakenTyInsert _ _ _ ∙ [idMor]Ty _) refl refl) (Refl (WeakTy _ dA) (VarLast dA)))) (Subst3TyEq (dΓ , dA) (WeakTy' _ _ (TyEqTy2 (((dΓ , dA) , WeakTy _ dA) , Id (WeakTy _ (WeakTy _ dA)) (VarPrev (WeakTy _ dA) (VarLast dA)) (VarLast (WeakTy _ dA))) dP=)) (VarLast dA) (congTmTy! (weakenTyInsert' _ _ _ _ ∙ [idMor]Ty _) (VarLast dA)) (congTmTy! (ap-id-Ty (weakenTyInsert' _ _ _ _ ∙ weakenTyInsert _ _ _ ∙ [idMor]Ty _) refl refl) (Refl (WeakTy _ dA) (VarLast dA))) (WeakTyEq' _ _ dP=) (VarLastCong dA) (congTmEqTy! (weakenTyInsert' _ _ _ _ ∙ [idMor]Ty _) (VarLastCong dA)) (congTmEqTy! (ap-id-Ty (weakenTyInsert' _ _ _ _ ∙ weakenTyInsert _ _ _ ∙ [idMor]Ty _) refl refl) (ReflCong (WeakTyEq _ dA=) (VarLastCong dA))))
              da' = Conv dA (TmEqTm2 dΓ da=) dA=
              db' = Conv dA (TmEqTm2 dΓ db=) dA=
              dp' = Conv (Id dA (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)) (TmEqTm2 dΓ dp=) (IdCong dA= da= db=) in         
          Conv (SubstTy dP' (((idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl da') , congTm (! (weakenTyInsert _ _ _ ∙ [idMor]Ty _)) refl db') , congTm (ap-id-Ty (! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _ ∙ [idMor]Ty _)) refl refl) refl dp')) (JJ dA' dP' dd' da' db' dp') (SubstTyFullEq (TyEqTy1 (((dΓ , dA) , (WeakTy _ dA)) , (Id (WeakTy _ (WeakTy _ dA)) (VarPrev (WeakTy _ dA) (VarLast dA)) (VarLast (WeakTy _ dA)))) dP=) ((((idMorDerivable dΓ) , (congTm (! ([idMor]Ty _)) refl (TmEqTm2 dΓ da=))) , (congTm (! (weakenTyInsert _ _ _ ∙ [idMor]Ty _)) refl (TmEqTm2 dΓ db=))) , Conv (Id dA' da' db') dp' (IdCong (congTyEq refl (! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _ ∙ [idMor]Ty _)) (TySymm dA=)) (TmRefl da') (TmRefl db'))) (TySymm dP=) ((((MorRefl (idMorDerivable dΓ)) , (congTmEqTy (! ([idMor]Ty _)) (TmSymm da=))) , (congTmEqTy (! (weakenTyInsert _ _ _ ∙ [idMor]Ty _)) (TmSymm db=))) , (ConvEq (Id (TyEqTy1 dΓ dA=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)) (TmSymm dp=) (IdCong (congTyEq refl (! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _ ∙ [idMor]Ty _)) (TyRefl dA)) da= db=))))
TmEqTm2 dΓ (BetaPi dA dB du da) = SubstTm du ((idMorDerivable dΓ) , congTm (! ([idMor]Ty _)) refl da)
TmEqTm2 dΓ (BetaSig1 dA dB da db) = da
TmEqTm2 dΓ (BetaSig2 {B = B} dA dB da db) = db
TmEqTm2 dΓ (BetaNatZero dP ddO ddS) = ddO
TmEqTm2 dΓ (BetaNatSuc {P = P} dP ddO ddS du) = Conv (SubstTy (WeakTy P (SubstTy (WeakTy' (prev last) nat dP) (idMorDerivable (dΓ , Nat) , Suc (VarLast Nat)))) ((idMorDerivable dΓ , du) , Natelim dP ddO ddS du)) (SubstTm ddS ((idMorDerivable dΓ , du) , Natelim dP ddO ddS du)) (congTyRefl' (SubstTy dP (idMorDerivable dΓ , Suc du)) (weakenTyInsert _ _ _ ∙ ap (λ z → z [ idMor _ , _ ]Ty) (weakenTyInsert' (prev last) _ (weakenMor (idMor _) , suc (var last)) (var last)) ∙ []Ty-assoc _ _ _ ∙ ap (λ z → _ [ z , suc _ ]Ty) (weakenMorInsert _ _ _ ∙ idMor[]Mor _)))
TmEqTm2 dΓ (BetaIdRefl {A = A} {P = P} {a = a} dA dP dd da) = congTmTy ([]Ty-assoc _ _ _ ∙ weakenTyInsert' (prev (prev (prev last))) _ ((((weakenMor (idMor _) [ idMor _ , a ]Mor) , a) , a) , refl (weakenTy A [ idMor _ , a ]Ty) a) a ∙ ap (λ z → P [ ((z , a) , a) , refl (weakenTy A [ idMor _ , a ]Ty) a ]Ty) (weakenMorInsert _ _ _ ∙ [idMor]Mor _) ∙ ap (λ z → P [ ((idMor _ , a) , a) , z ]Ty) (ap-refl-Tm (weakenTyInsert _ _ _ ∙ [idMor]Ty A) refl)) (Subst1Tm dΓ dd da)

MorEqMor1 : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → (⊢ Γ) → (⊢ Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ δ ∷> Δ)
MorEqMor2 : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → (⊢ Γ) → (⊢ Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ δ' ∷> Δ)

MorEqMor1 {Δ = ◇} {δ = ◇} {◇} _ _ dδ= = tt
MorEqMor1 {Δ = Δ , B} {δ = δ , u} {δ' , u'} dΓ (dΔ , _) (dδ= , du=) = (MorEqMor1 dΓ dΔ dδ=) , TmEqTm1 dΓ du=

MorEqMor2 {Δ = ◇} {δ = ◇} {◇} _ _ dδ= = tt
MorEqMor2 {Δ = Δ , B} {δ = δ , u} {δ' , u'} dΓ (dΔ , dB) (dδ= , du=) = (MorEqMor2 dΓ dΔ dδ=) , Conv (SubstTy dB (MorEqMor1 dΓ dΔ dδ=)) (TmEqTm2 dΓ du=) (SubstTyMorEq dB (MorEqMor1 dΓ dΔ dδ=) dδ=)


MorSymm : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → ⊢ Γ → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ ∷> Δ
MorSymm {Δ = ◇} {◇} {◇} _ _ tt = tt
MorSymm {Δ = Δ , B} {δ , u} {δ' , u'} dΓ (dΔ , dB) (dδ , du) = MorSymm dΓ dΔ dδ , ConvEq (SubstTy dB (MorEqMor1 dΓ dΔ dδ)) (TmSymm du) (SubstTyMorEq dB (MorEqMor1 dΓ dΔ dδ) dδ)

MorTran : {Γ : Ctx n} {Δ : Ctx m} {δ δ' δ'' : Mor n m} → ⊢ Γ → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ'' ∷> Δ → Γ ⊢ δ == δ'' ∷> Δ
MorTran {Δ = ◇} {◇} {◇} {◇} _ _ tt tt = tt
MorTran {Δ = Δ , B} {δ , u} {δ' , u'} {δ'' , u''} dΓ (dΔ , dB) (dδ , du) (dδ' , du') = (MorTran dΓ dΔ dδ dδ') , TmTran (TmEqTm2 dΓ du) du (ConvEq (SubstTy dB (MorEqMor2 dΓ dΔ dδ)) du' (SubstTyMorEq dB (MorEqMor2 dΓ dΔ dδ) (MorSymm dΓ dΔ dδ)))


ConvTm2 : {Γ Δ : Ctx n} {u : TmExpr n} {A A' : TyExpr n} → Derivable (Γ ⊢ u :> A) → (⊢ Γ == Δ) → Derivable (Γ ⊢ A == A') → Derivable (Δ ⊢ u :> A')
ConvTm2 du dΓ= dA= = Conv (ConvTy (TyEqTy1 (CtxEqCtx1 dΓ=) dA=) dΓ=) (ConvTm du dΓ=) (ConvTyEq dA= dΓ=)

ConvTmEq2 : {Γ Δ : Ctx n} {u u' : TmExpr n} {A A' : TyExpr n} → Derivable (Γ ⊢ u == u' :> A) → (⊢ Γ == Δ) → Derivable (Γ ⊢ A == A') → Derivable (Δ ⊢ u == u' :> A')
ConvTmEq2 du= dΓ= dA= = ConvTmEq (ConvEq (TyEqTy1 (CtxEqCtx1 dΓ=) dA=) du= dA=) dΓ=

ConvMor : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ : Mor n m} → (Γ ⊢ δ ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ ∷> Δ')
ConvMor {Δ = ◇} {Δ' = ◇} {δ = ◇} dδ dΓ= dΔ= = tt
ConvMor {Δ = Δ , B} {Δ' = Δ' , B'} {δ = δ , u} (dδ , du) dΓ= (dΔ= , dB , dB' ,  dB= , dB=') =
        ConvMor dδ dΓ= dΔ= , Conv (ConvTy (SubstTy dB dδ) dΓ=) (ConvTm du dΓ=) (SubstTyEq dB= (ConvMor dδ dΓ= (CtxRefl (CtxEqCtx1 dΔ=))))

ConvMorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} → (Γ ⊢ δ == δ' ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ == δ' ∷> Δ')
ConvMorEq {Δ = ◇} {Δ' = ◇} {δ = ◇} {◇} dδ= dΓ= dΔ= = tt
ConvMorEq {Δ = Δ , B} {Δ' = Δ' , B'} {δ = δ , u} {δ' , u₁} (dδ= , du=) dΓ= (dΔ= , dB , dB' , dB= , dB=') = (ConvMorEq dδ= dΓ= dΔ=) , ConvTmEq (ConvEq (SubstTy dB (MorEqMor1 (CtxEqCtx1 dΓ=) (CtxEqCtx1 dΔ=) dδ=)) du= (SubstTyEq dB= (MorEqMor1 (CtxEqCtx1 dΓ=) (CtxEqCtx1 dΔ=) dδ=))) dΓ=

eqMorDer : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' → Γ' ⊢ idMor n ∷> Γ
eqMorDer dΓ= = ConvMor (idMorDerivable (CtxEqCtx1 dΓ=)) dΓ= (CtxRefl (CtxEqCtx1 dΓ=))

SubstMorFullEq : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ θ' : Mor m k} {δ δ' : Mor n m} → (⊢ Δ) → (⊢ Θ) → (Δ ⊢ θ' ∷> Θ) → (Δ ⊢ θ == θ' ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ' [ δ' ]Mor ∷> Θ)
SubstMorFullEq {Θ = ◇} {◇} {◇} dΔ tt dθ' tt dδ dδ= = tt
SubstMorFullEq {Θ = Θ , C} {θ , w} {θ' , w'} dΔ (dΘ , dC) (dθ' , dw') (dθ= , dw=) dδ dδ= = (SubstMorFullEq dΔ dΘ dθ' dθ= dδ dδ=) , congTmEqTy ([]Ty-assoc _ θ C) (SubstTmFullEq (Conv (SubstTy dC dθ') dw' (SubstTyMorEq dC dθ' (MorSymm dΔ dΘ dθ=))) dδ dw= dδ=) 


SubstTyMorEq2 : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m}
              → ⊢ Γ → ⊢ Δ → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
SubstTyMorEq2 dΓ dΔ dA= dδ= =
  let dδ = MorEqMor1 dΓ dΔ dδ=
      dA' = TyEqTy2 dΔ dA=
  in
  SubstTyFullEq dA' dδ dA= dδ=


_,,_ : {Γ Γ' : Ctx n} {A A' : TyExpr n} → ⊢ Γ == Γ' → Derivable (Γ ⊢ A == A') → ⊢ (Γ , A) == (Γ' , A')
dΓ= ,, dA= =
  let dΓ = CtxEqCtx1 dΓ=
  in
  (dΓ= , TyEqTy1 dΓ dA= , ConvTy (TyEqTy2 dΓ dA=) dΓ= , dA= , ConvTyEq dA= dΓ=)
