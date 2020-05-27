{-# OPTIONS --rewriting --prop #-}

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
  Var : {Γ : Ctx n} (k : VarPos n)
    → Derivable (Γ ⊢ getTy k Γ)
    → Derivable (Γ ⊢ var k :> getTy k Γ)
          
  -- Reflexivity, symmetry and transitivity for types
  TyRefl : {Γ : Ctx n} {A : TyExpr n}
    → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A == A)
  TySymm : {Γ : Ctx n} {A B : TyExpr n}
    → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B == A)
  TyTran : {Γ : Ctx n} {A B C : TyExpr n}
    → Derivable (Γ ⊢ B) → Derivable (Γ ⊢ A == B)→ Derivable (Γ ⊢ B == C) → Derivable (Γ ⊢ A == C)

  -- Reflexivity, symmetry and transitivity for terms
  TmRefl : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n}
    → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u == u :> A)
  TmSymm : {Γ : Ctx n} {u v : TmExpr n} {A : TyExpr n}
    → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ v == u :> A)
  TmTran : {Γ : Ctx n} {u v w : TmExpr n} {A : TyExpr n}
    → Derivable (Γ ⊢ v :> A) → Derivable (Γ ⊢ u == v :> A)→ Derivable (Γ ⊢ v == w :> A) → Derivable (Γ ⊢ u == w :> A)

  -- The derivability of [B] and of [v] in [TyTran]/[TmTran] is used in
  -- [⟦⟧TyEq]/[⟦⟧TmEq]

  -- Conversion rules, the derivability of [A] is used in [⟦⟧Tm₁], and cannot be
  -- derived from the other two arguments because we would need [Γ] derivable
  Conv : {Γ : Ctx n} {u : TmExpr n} {A B : TyExpr n} → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u :> B)
  ConvEq : {Γ : Ctx n} {u u' : TmExpr n} {A B : TyExpr n} → Derivable (Γ ⊢ A)
    → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ u == u' :> B)


  -- Rules for UU
  UU : {i : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ uu i)
  UUCong :  {i : ℕ} {Γ : Ctx n}
    → Derivable (Γ ⊢ uu i == uu i)

  -- Rules for uu
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


  -- Rules for Sum
  Sum : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr n} 
    → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ B) → Derivable (Γ ⊢ sum A B)
  SumCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr n} 
    → Derivable (Γ ⊢ A == A') → Derivable (Γ ⊢ B == B') → Derivable (Γ ⊢ sum A B == sum A' B')

  -- Rules for sum
  SumUU : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {b : TmExpr n}
        → Derivable (Γ ⊢ a :> uu i) → Derivable (Γ ⊢ b :> uu i) → Derivable (Γ ⊢ sum i a b :> uu i)
  SumUUCong : {i : ℕ} {Γ : Ctx n} {a a' : TmExpr n} {b b' : TmExpr n}
        → Derivable (Γ ⊢ a == a' :> uu i) → Derivable (Γ ⊢ b == b' :> uu i) → Derivable (Γ ⊢ sum i a b == sum i a' b' :> uu i)
  ElSum= : {i : ℕ} {Γ : Ctx n} {a : TmExpr n} {b : TmExpr n}
        → Derivable (Γ ⊢ a :> uu i) → Derivable (Γ ⊢ b :> uu i) → Derivable (Γ ⊢ el i (sum i a b) == sum (el i a) (el i b))

  -- Rules for inl
  Inl : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr n} {a : TmExpr n}
      → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ B) → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ inl A B a :> sum A B)
  InlCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr n} {a a' : TmExpr n}
      → Derivable (Γ ⊢ A == A') → Derivable (Γ ⊢ B == B') → Derivable (Γ ⊢ a == a' :> A) → Derivable (Γ ⊢ inl A B a  == inl A' B' a' :> sum A B)

  -- Rules for inr
  Inr : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr n} {b : TmExpr n}
      → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ B) → Derivable (Γ ⊢ b :> B) → Derivable (Γ ⊢ inr A B b :> sum A B)
  InrCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr n} {b b' : TmExpr n}
      → Derivable (Γ ⊢ A == A') → Derivable (Γ ⊢ B == B') → Derivable (Γ ⊢ b == b' :> B) → Derivable (Γ ⊢ inr A B b  == inr A' B' b' :> sum A B)

  -- Rules for match
  Match : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr n} {C : TyExpr (suc n)} {da : TmExpr (suc n)} {db : TmExpr (suc n)} {u : TmExpr n}
        → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ B) → Derivable ((Γ , sum A B) ⊢ C)
        → Derivable ((Γ , A) ⊢ da :> substTy (weakenTy' (prev last) C) (inl (weakenTy A) (weakenTy B) (var last)))
        → Derivable ((Γ , B) ⊢ db :> substTy (weakenTy' (prev last) C) (inr (weakenTy A) (weakenTy B) (var last)))
        → Derivable (Γ ⊢ u :> sum A B) → Derivable (Γ ⊢ match A B C da db u :> substTy C u)
  MatchCong : {Γ : Ctx n} {A A' : TyExpr n} {B B' : TyExpr n} {C C' : TyExpr (suc n)} {da da' : TmExpr (suc n)} {db db' : TmExpr (suc n)} {u u' : TmExpr n}
        → Derivable (Γ ⊢ A == A') → Derivable (Γ ⊢ B == B') → Derivable ((Γ , sum A B) ⊢ C == C')
        → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ da == da' :> substTy (weakenTy' (prev last) C) (inl (weakenTy A) (weakenTy B) (var last)))
        → Derivable (Γ ⊢ B) → Derivable ((Γ , B) ⊢ db == db' :> substTy (weakenTy' (prev last) C) (inr (weakenTy A) (weakenTy B) (var last)))
        → Derivable (Γ ⊢ u == u' :> sum A B) → Derivable (Γ ⊢ match A B C da db u == match A' B' C' da' db' u' :> substTy C u)


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


  -- Rules for Empty
  Empty : {Γ : Ctx n}
      → Derivable (Γ ⊢ empty)
  EmptyCong : {Γ : Ctx n}
      → Derivable (Γ ⊢ empty == empty)

  -- Rules for empty
  EmptyUU : {i : ℕ} {Γ : Ctx n}
     → Derivable (Γ ⊢ empty i :> uu i)
  EmptyUUCong : {i : ℕ} {Γ : Ctx n}
     → Derivable (Γ ⊢ empty i == empty i :> uu i)
  ElEmpty= : {i : ℕ} {Γ : Ctx n}
     → Derivable (Γ ⊢ el i (empty i) == empty)

  -- Rules for emptyelim
  Emptyelim : {Γ : Ctx n} {A : TyExpr (suc n)} {u : TmExpr n}
     → Derivable ((Γ , empty) ⊢ A) → Derivable (Γ ⊢ u :> empty) → Derivable (Γ ⊢ emptyelim A u :> substTy A u)
  EmptyelimCong : {Γ : Ctx n} {A A' : TyExpr (suc n)} {u u' : TmExpr n}
     → Derivable ((Γ , empty) ⊢ A == A') → Derivable (Γ ⊢ u == u' :> empty) → Derivable (Γ ⊢ emptyelim A u == emptyelim A' u' :> substTy A u)

  -- Rules for Unit
  Unit : {Γ : Ctx n}
     → Derivable (Γ ⊢ unit)
  UnitCong : {Γ : Ctx n}
     → Derivable (Γ ⊢ unit == unit)

  -- Rules for unit
  UnitUU : {i : ℕ} {Γ : Ctx n}
     → Derivable (Γ ⊢ unit i :> uu i)
  UnitUUCong : {i : ℕ} {Γ : Ctx n}
     → Derivable (Γ ⊢ unit i == unit i :> uu i)
  ElUnit= : {i : ℕ} {Γ : Ctx n}
     → Derivable (Γ ⊢ el i (unit i) == unit)

  -- Rules for tt
  TT : {Γ : Ctx n}
     → Derivable (Γ ⊢ tt :> unit)
  TTCong : {Γ : Ctx n}
     → Derivable (Γ ⊢ tt == tt :> unit)

  -- Rules for unitelim
  Unitelim : {Γ : Ctx n} {A : TyExpr (suc n)} {dtt : TmExpr n} {u : TmExpr n}
     → Derivable ((Γ , unit) ⊢ A) → Derivable (Γ ⊢ dtt :> substTy A tt) → Derivable (Γ ⊢ u :> unit) → Derivable (Γ ⊢ unitelim A dtt u :> substTy A u)
  UnitelimCong : {Γ : Ctx n} {A A' : TyExpr (suc n)} {dtt dtt' : TmExpr n} {u u' : TmExpr n}
     → Derivable ((Γ , unit) ⊢ A == A') → Derivable (Γ ⊢ dtt == dtt' :> substTy A tt) → Derivable (Γ ⊢ u == u' :> unit) → Derivable (Γ ⊢ unitelim A dtt u == unitelim A' dtt' u' :> substTy A u)
    

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
    → Derivable ((Γ , nat) ⊢ P) → Derivable (Γ ⊢ dO :> substTy P zero) → Derivable (((Γ , nat) , P) ⊢ dS :> substTy (weakenTy' (prev last) (weakenTy' (prev last) P)) (suc (var (prev last)))) → Derivable (Γ ⊢ u :> nat) → Derivable (Γ ⊢ natelim P dO dS u :> substTy P u)
  NatelimCong : {Γ : Ctx n} {P P' : TyExpr (suc n)} {dO dO' : TmExpr n} {dS dS' : TmExpr (suc (suc n))} {u u' : TmExpr n}
    → Derivable ((Γ , nat) ⊢ P) → Derivable ((Γ , nat) ⊢ P == P') → Derivable (Γ ⊢ dO == dO' :> substTy P zero) → Derivable (((Γ , nat) , P) ⊢ dS == dS' :> substTy (weakenTy' (prev last) (weakenTy' (prev last) P)) (suc (var (prev last)))) → Derivable (Γ ⊢ u == u' :> nat) → Derivable (Γ ⊢ natelim P dO dS u == natelim P' dO' dS' u' :> substTy P u)


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
  BetaInl : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr n} {C : TyExpr (suc n)} {da : TmExpr (suc n)} {db : TmExpr (suc n)} {a : TmExpr n}
          → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ B) → Derivable ((Γ , sum A B) ⊢ C)
          → Derivable ((Γ , A) ⊢ da :> substTy (weakenTy' (prev last) C) (inl (weakenTy A) (weakenTy B) (var last)))
          → Derivable ((Γ , B) ⊢ db :> substTy (weakenTy' (prev last) C) (inr (weakenTy A) (weakenTy B) (var last)))
          → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ match A B C da db (inl A B a) == substTm da a :> substTy C (inl A B a))
  BetaInr : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr n} {C : TyExpr (suc n)} {da : TmExpr (suc n)} {db : TmExpr (suc n)} {b : TmExpr n}
          → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ B) → Derivable ((Γ , sum A B) ⊢ C)
          → Derivable ((Γ , A) ⊢ da :> substTy (weakenTy' (prev last) C) (inl (weakenTy A) (weakenTy B) (var last)))
          → Derivable ((Γ , B) ⊢ db :> substTy (weakenTy' (prev last) C) (inr (weakenTy A) (weakenTy B) (var last)))
          → Derivable (Γ ⊢ b :> B) → Derivable (Γ ⊢ match A B C da db (inr A B b) == substTm db b :> substTy C (inr A B b))
  BetaPi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr (suc n)} {a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable ((Γ , A) ⊢ u :> B) → Derivable (Γ ⊢ a :> A)
    → Derivable (Γ ⊢ app A B (lam A B u) a == substTm u a :> substTy B a)
  BetaSig1 : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {a : TmExpr n} {b : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ b :> substTy B a) → Derivable (Γ ⊢ pr1 A B (pair A B a b) == a :> A)
  BetaSig2 : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {a : TmExpr n} {b : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ a :> A) → Derivable (Γ ⊢ b :> substTy B a) → Derivable (Γ ⊢ pr2 A B (pair A B a b) == b :> substTy B a)
  BetaUnit : {Γ : Ctx n} {A : TyExpr (suc n)} {dtt : TmExpr n}
    → Derivable ((Γ , unit) ⊢ A) → Derivable (Γ ⊢ dtt :> substTy A tt) → Derivable (Γ ⊢ unitelim A dtt tt == dtt :> substTy A tt)
  BetaNatZero : {Γ : Ctx n} {P : TyExpr (suc n)} {dO : TmExpr n} {dS : TmExpr (suc (suc n))}
    → Derivable ((Γ , nat) ⊢ P) → Derivable (Γ ⊢ dO :> substTy P zero) → Derivable (((Γ , nat) , P) ⊢ dS :> substTy (weakenTy' (prev last) (weakenTy' (prev last) P)) (suc (var (prev last))))
    → Derivable (Γ ⊢ natelim P dO dS zero == dO :> substTy P zero)
  BetaNatSuc : {Γ : Ctx n} {P : TyExpr (suc n)} {dO : TmExpr n} {dS : TmExpr (suc (suc n))} {u : TmExpr n}
    → Derivable ((Γ , nat) ⊢ P) → Derivable (Γ ⊢ dO :> substTy P zero) → Derivable (((Γ , nat) , P) ⊢ dS :> substTy (weakenTy' (prev last) (weakenTy' (prev last) P)) (suc (var (prev last)))) → Derivable (Γ ⊢ u :> nat)
    → Derivable (Γ ⊢ natelim P dO dS (suc u) == subst2Tm dS u (natelim P dO dS u) :> substTy P (suc u))
  BetaIdRefl : {Γ : Ctx n} {A : TyExpr n} {P : TyExpr (suc (suc (suc n)))} {d : TmExpr (suc n)} {a : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((((Γ , A) , weakenTy A) , id (weakenTy (weakenTy A)) (var (prev last)) (var last)) ⊢ P) → Derivable ((Γ , A) ⊢ d :> subst3Ty (weakenTy' (prev (prev (prev last))) P) (var last) (var last) (refl (weakenTy A) (var last))) → Derivable (Γ ⊢ a :> A)
    → Derivable (Γ ⊢ jj A P d a a (refl A a) == substTm d a :> subst3Ty P a a (refl A a))

  -- Eta-equivalences
  EtaSum : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr n} {u : TmExpr n}
         → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ B) → Derivable (Γ ⊢ u :> sum A B)
         → Derivable (Γ ⊢ u == match A B (weakenTy (sum A B)) (inl (weakenTy A) (weakenTy B) (var last)) (inr (weakenTy A) (weakenTy B) (var last)) u :> sum A B)
  EtaPi : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {f : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ f :> pi A B)
    → Derivable (Γ ⊢ f == lam A B (app (weakenTy A) (weakenTy' (prev last) B) (weakenTm f) (var last)) :> pi A B)
  EtaSig : {Γ : Ctx n} {A : TyExpr n} {B : TyExpr (suc n)} {u : TmExpr n}
    → Derivable (Γ ⊢ A) → Derivable ((Γ , A) ⊢ B) → Derivable (Γ ⊢ u :> sig A B)
    → Derivable (Γ ⊢ u == pair A B (pr1 A B u) (pr2 A B u) :> sig A B)

{- Derivability of contexts, context equality, context morphisms, and context morphism equality -}

data ⊢_ : Ctx n → Prop where
  tt : ⊢ ◇
  _,_ : {Γ : Ctx n} {A : _} → (⊢ Γ) → Derivable (Γ ⊢ A) → ⊢ (Γ , A)

data ⊢_==_ : Ctx n → Ctx n → Prop where
  tt : ⊢ ◇ == ◇
  _,_ : {Γ Γ' : Ctx n} {A A' : TyExpr n} → (⊢ Γ == Γ') → Derivable (Γ ⊢ A == A') → ⊢ (Γ , A) == (Γ' , A')

data _⊢_∷>_ (Γ : Ctx n) : Mor n m → Ctx m → Prop where
  tt : Γ ⊢ ◇ ∷> ◇
  _,_ : {Δ : Ctx m} {δ : Mor n m} {u : TmExpr n} {A : TyExpr m} → (Γ ⊢ δ ∷> Δ) → Derivable (Γ ⊢ u :> A [ δ ]Ty) → (Γ ⊢ (δ , u) ∷> (Δ , A))

data _⊢_==_∷>_ (Γ : Ctx n) : Mor n m → Mor n m → Ctx m → Prop where
  tt : Γ ⊢ ◇ == ◇ ∷> ◇
  _,_ : {Δ : Ctx m} {δ δ' : Mor n m} {u u' : TmExpr n} {A : TyExpr m} → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ u == u' :> A [ δ ]Ty) → (Γ ⊢ (δ , u) == (δ' , u') ∷> (Δ , A))

{- Congruence with respect to the type in derivability of term expressions -}

congCtx : {Γ Γ' : Ctx n} → Γ ≡ Γ' → ⊢ Γ → ⊢ Γ'
congCtx refl dΓ = dΓ

congCtxEq : {Γ Γ' Δ Δ' : Ctx n} → Γ ≡ Γ' → Δ ≡ Δ' → ⊢ Γ == Δ → ⊢ Γ' == Δ'
congCtxEq refl refl dΓ= = dΓ=

congTy : {Γ : Ctx n} {A A' : TyExpr n} → A ≡ A' → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A')
congTy refl dA = dA

congTy! : {Γ : Ctx n} {A A' : TyExpr n} → A' ≡ A → Derivable (Γ ⊢ A) → Derivable (Γ ⊢ A')
congTy! refl dA = dA

congTyCtx :  {Γ Γ' : Ctx n} {A : TyExpr n} → Γ ≡ Γ' → Derivable (Γ ⊢ A) → Derivable (Γ' ⊢ A)
congTyCtx refl dA = dA

congTyCtxEq : {Γ Γ' : Ctx n} {A B : TyExpr n} → Γ ≡ Γ' → Derivable (Γ ⊢ A == B) → Derivable (Γ' ⊢ A == B)
congTyCtxEq refl dA= = dA=

congTyEq : {Γ : Ctx n} {A A' B B' : TyExpr n} → A ≡ A' → B ≡ B' → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A' == B')
congTyEq refl refl dA= = dA=

congTyEq! : {Γ : Ctx n} {A A' B B' : TyExpr n} → A' ≡ A → B' ≡ B → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A' == B')
congTyEq! refl refl dA= = dA=

congTm : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A ≡ A' → u ≡ u' → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u' :> A')
congTm refl refl du = du

congTm! : {Γ : Ctx n} {A A' : TyExpr n} {u u' : TmExpr n} → A' ≡ A → u' ≡ u → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ u' :> A')
congTm! refl refl du = du

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

congTmEq! : {Γ : Ctx n} {A A' : TyExpr n} {u u' v v' : TmExpr n} → v ≡ u → v' ≡ u' → A' ≡ A → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ v == v' :> A')
congTmEq! refl refl refl du= = du=

congMor : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} → Γ ≡ Γ' → Δ ≡ Δ' → δ ≡ δ' → Γ ⊢ δ ∷> Δ → Γ' ⊢ δ' ∷> Δ'
congMor refl refl refl dδ = dδ

congMorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' θ θ' : Mor n m} → Γ ≡ Γ' → Δ ≡ Δ' → δ ≡ δ' → θ ≡ θ' → Γ ⊢ δ == θ ∷> Δ → Γ' ⊢ δ' == θ' ∷> Δ'
congMorEq refl refl refl refl dδ= = dδ=

congMorEqCtxEq : {Γ Γ' : Ctx n} {Δ : Ctx m} {δ θ : Mor n m} → Γ ≡ Γ' → Γ ⊢ δ == θ ∷> Δ → Γ' ⊢ δ == θ ∷> Δ
congMorEqCtxEq refl dδ= = dδ=


{- Reflexivity rules -}

congTyRefl : {Γ : Ctx n} {A A' : TyExpr n} → Derivable (Γ ⊢ A) → A ≡ A' → Derivable (Γ ⊢ A == A')
congTyRefl dA refl = TyRefl dA

congTyRefl' : {Γ : Ctx n} {A A' : TyExpr n} → Derivable (Γ ⊢ A') → A ≡ A' → Derivable (Γ ⊢ A == A')
congTyRefl' dA refl = TyRefl dA

congTmRefl : {Γ : Ctx n} {A : TyExpr n} {u u' : TmExpr n} → Derivable (Γ ⊢ u :> A) → u ≡ u' → Derivable (Γ ⊢ u == u' :> A)
congTmRefl du refl = TmRefl du

CtxRefl : {Γ : Ctx n} → ⊢ Γ → ⊢ Γ == Γ
CtxRefl tt = tt
CtxRefl {Γ = Γ , A} (dΓ , dA) = (CtxRefl dΓ , TyRefl dA)

MorRefl : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ δ == δ ∷> Δ)
MorRefl tt = tt
MorRefl (dδ , du) = MorRefl dδ , TmRefl du

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

WeakTy : {k : WeakPos n} {Γ : Ctx n} {T : TyExpr (n -WeakPos k)} {A : TyExpr n}
     → Derivable (Γ ⊢ A) → Derivable (weakenCtx k Γ T ⊢ weakenTy' k A)
WeakTm : {k : WeakPos n} {Γ : Ctx n} {T : TyExpr (n -WeakPos k)} {u : TmExpr n} {A : TyExpr n}
     → Derivable (Γ ⊢ u :> A) → Derivable (weakenCtx k Γ T ⊢ weakenTm' k u :> weakenTy' k A)
WeakTyEq : {k : WeakPos n} {Γ : Ctx n} {T : TyExpr (n -WeakPos k)} {A A' : TyExpr n}
     → Derivable (Γ ⊢ A == A') → Derivable (weakenCtx k Γ T ⊢ weakenTy' k A == weakenTy' k A')
WeakTmEq : {k : WeakPos n} {Γ : Ctx n} {T : TyExpr (n -WeakPos k)} {u u' : TmExpr n} {A : TyExpr n}
     → Derivable (Γ ⊢ u == u' :> A) → Derivable (weakenCtx k Γ T ⊢ weakenTm' k u == weakenTm' k u' :> weakenTy' k A)

WeakMor : {Γ : Ctx n} {Δ : Ctx m} {T : TyExpr n} {δ : Mor n m} → Γ ⊢ δ ∷> Δ → (Γ , T) ⊢ weakenMor δ ∷> Δ
WeakMor {Δ = ◇} {δ = ◇} tt = tt
WeakMor {Δ = Δ , B} {δ = δ , u} (dδ , du) = (WeakMor dδ , congTmTy (weaken[]Ty _ _ _) (WeakTm du))

WeakMorEq : {Γ : Ctx n } {Δ : Ctx m} {T : TyExpr n} {δ δ' : Mor n m} → (Γ ⊢ δ == δ' ∷> Δ) → ((Γ , T) ⊢ weakenMor δ == weakenMor δ' ∷> Δ)
WeakMorEq {Δ = ◇} {δ = ◇} {◇} dδ = tt
WeakMorEq {Δ = Δ , B} {δ = δ , u} {δ' , u'} (dδ , du) = (WeakMorEq dδ , congTmEqTy (weaken[]Ty _ _ _) (WeakTmEq du))

WeakMor+~ : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m} → Derivable (Γ ⊢ A [ δ ]Ty) → Γ ⊢ δ ∷> Δ → (Γ , A [ δ ]Ty) ⊢ weakenMor+ δ ∷> (Δ , A)
WeakMor+~ dAδ dδ = (WeakMor dδ , congTmTy (weaken[]Ty _ _ _) (Var last (WeakTy dAδ)))

WeakMor+ : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ : Mor n m} → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → (Γ , A [ δ ]Ty) ⊢ weakenMor+ δ ∷> (Δ , A)
WeakMor+ dA dδ = WeakMor+~ (SubstTy dA dδ) dδ

WeakMor+Eq : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m} → Derivable (Δ ⊢ A) → Γ ⊢ δ ∷> Δ → Γ ⊢ δ == δ' ∷> Δ → (Γ , A [ δ ]Ty) ⊢ weakenMor+ δ == weakenMor+ δ' ∷> (Δ , A)
WeakMor+Eq dA dδ dδ= = (WeakMorEq dδ= , TmRefl (congTmTy (weaken[]Ty _ _ _) (Var last (WeakTy (SubstTy dA dδ)))))


{- Simplified rules for variables -}

VarLast : {Γ : Ctx n} {A : TyExpr n}
  → Derivable (Γ ⊢ A)
  → Derivable ((Γ , A) ⊢ var last :> weakenTy A)
VarLast dA = Var last (WeakTy dA)

VarPrevLast : {Γ : Ctx n} {B : TyExpr (suc n)} {A : TyExpr n}
  → Derivable (Γ ⊢ A)
  → Derivable (((Γ , A) , B) ⊢ var (prev last) :> weakenTy (weakenTy A))
VarPrevLast dA = Var (prev last) (WeakTy (WeakTy dA))

VarLastCong : {Γ : Ctx n} {A : TyExpr n}
  → Derivable (Γ ⊢ A)
  → Derivable ((Γ , A) ⊢ var last == var last :> weakenTy A)
VarLastCong dA = TmRefl (VarLast dA)

{- Rules about getTy -}

getTySubst : {Γ : Ctx n} (k : VarPos m) {δ : Mor n m} {Δ : Ctx m}
           → Γ ⊢ δ ∷> Δ
           → Derivable (Γ ⊢ k [ δ ]Var :> (getTy k Δ [ δ ]Ty))
getTySubst last (dδ , du) = congTmTy! (weakenTyInsert _ _ _) du
getTySubst (prev k) (dδ , du) = congTmTy! (weakenTyInsert _ _ _) (getTySubst k dδ)

getTySubstEq : {Γ : Ctx n} (k : VarPos m) {δ δ' : Mor n m} {Δ : Ctx m}
           → Γ ⊢ δ == δ' ∷> Δ
           → Derivable (Γ ⊢ (var k) [ δ ]Tm == (var k) [ δ' ]Tm :> (getTy k Δ [ δ ]Ty))
getTySubstEq last (dδ= , du=) = congTmEqTy! (weakenTyInsert _ _ _) du=
getTySubstEq (prev k) (dδ= , du=) = congTmEqTy! (weakenTyInsert _ _ _) (getTySubstEq k dδ=)

SubstTy (Pi dA dB) dδ = Pi (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ))
SubstTy UU dδ = UU
SubstTy (Sum dA dB) dδ = Sum (SubstTy dA dδ) (SubstTy dB dδ)
SubstTy (El dA) dδ = El (SubstTm dA dδ)
SubstTy (Sig dA dB) dδ = Sig (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ))
SubstTy Empty dδ = Empty
SubstTy Unit dΓ = Unit
SubstTy Nat dδ = Nat
SubstTy (Id dA du dv) dδ = Id (SubstTy dA dδ) (SubstTm du dδ) (SubstTm dv dδ)

SubstTm (Conv dA du dA=) dδ = Conv (SubstTy dA dδ) (SubstTm du dδ) (SubstTyEq dA= dδ)
SubstTm (Var k dA) dδ = getTySubst k dδ

SubstTm (SumUU da db) dδ = SumUU (SubstTm da dδ) (SubstTm db dδ)
SubstTm (Inl dA dB da) dδ = Inl (SubstTy dA dδ) (SubstTy dB dδ) (SubstTm da dδ)
SubstTm (Inr dA dB db) dδ = Inr (SubstTy dA dδ) (SubstTy dB dδ) (SubstTm db dδ)
SubstTm (Match dA dB dC dda ddb du) dδ = congTmTy! []Ty-substTy (Match (SubstTy dA dδ)
                                                                       (SubstTy dB dδ)
                                                                       (SubstTy dC (WeakMor+ (Sum dA dB) dδ))
                                                                       (congTmTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1 (ap-inl-Tm []Ty-weakenTy []Ty-weakenTy refl) )
                                                                       (SubstTm dda (WeakMor+ dA dδ)))
                                                                       (congTmTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1 (ap-inr-Tm []Ty-weakenTy []Ty-weakenTy refl) )
                                                                       (SubstTm ddb (WeakMor+ dB dδ)))
                                                                       (SubstTm du dδ))
SubstTm (Lam dA dB du) dδ = Lam (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm du (WeakMor+ dA dδ))
SubstTm {δ = δ} (App dA dB df da) dδ = congTmTy! []Ty-substTy (App (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm df dδ) (SubstTm da dδ))
SubstTm UUUU dδ = UUUU
SubstTm (PiUU da db) dδ = PiUU (SubstTm da dδ) (SubstTm db (WeakMor+ (El da) dδ))
SubstTm (SigUU da db) dδ = SigUU (SubstTm da dδ) (SubstTm db (WeakMor+ (El da) dδ))
SubstTm (Pair dA dB da db) dδ = Pair (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm da dδ) (congTmTy []Ty-substTy (SubstTm db dδ))
SubstTm (Pr1 dA dB du) dδ = Pr1 (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm du dδ)
SubstTm (Pr2 dA dB du) dδ = congTmTy! []Ty-substTy (Pr2 (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm du dδ))
SubstTm EmptyUU dδ = EmptyUU
SubstTm (Emptyelim dA du) dδ = congTmTy! []Ty-substTy (Emptyelim (SubstTy dA (WeakMor+ Empty dδ)) (SubstTm du dδ))
SubstTm UnitUU dδ = UnitUU
SubstTm TT dδ = TT
SubstTm (Unitelim dA ddtt du) dδ = congTmTy! []Ty-substTy (Unitelim (SubstTy dA (WeakMor+ Unit dδ)) (congTmTy []Ty-substTy (SubstTm ddtt dδ)) (SubstTm du dδ))
SubstTm NatUU dδ = NatUU
SubstTm Zero dδ = Zero
SubstTm (Suc du) dδ = Suc (SubstTm du dδ)
SubstTm (Natelim dP ddO ddS du) dδ =
  congTmTy! []Ty-substTy
    (Natelim (SubstTy dP (WeakMor+ Nat dδ))
             (congTmTy []Ty-substTy (SubstTm ddO dδ))
             (congTmTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1-weakenTy1 refl) (SubstTm ddS (WeakMor+ dP (WeakMor+ Nat dδ))))
             (SubstTm du dδ))
SubstTm (IdUU da du dv) dδ = IdUU (SubstTm da dδ) (SubstTm du dδ) (SubstTm dv dδ)
SubstTm (Refl dA da) dδ = Refl (SubstTy dA dδ) (SubstTm da dδ)
SubstTm (JJ dA dP dd da db dp) dδ =
 let dwA = congTy! []Ty-weakenTy (WeakTy (SubstTy dA dδ)) in
  congTmTy! ([]Ty-subst3Ty)
            (JJ (SubstTy dA dδ)
                (congTyCtx (Ctx+= (Ctx+= refl []Ty-weakenTy) (ap-id-Ty ([]Ty-weakenTy ∙ ap weakenTy []Ty-weakenTy) refl refl))
                           (SubstTy dP (WeakMor+~ (Id (congTy! ([]Ty-weakenTy ∙ ap weakenTy []Ty-weakenTy) (WeakTy (WeakTy (SubstTy dA dδ))))
                                                      (congTmTy! ([]Ty-weakenTy ∙ ap weakenTy []Ty-weakenTy) (VarPrevLast (SubstTy dA dδ)))
                                                      (congTmTy! []Ty-weakenTy (VarLast dwA)))
                                                  (WeakMor+~ dwA (WeakMor+ dA dδ)))))                
                (congTmTy ([]Ty-subst3Ty ∙ ap-subst3Ty []Ty-weakenTy3 refl refl (ap-refl-Tm []Ty-weakenTy refl))
                          (SubstTm dd (WeakMor+ dA dδ)))
                (SubstTm da dδ)
                (SubstTm db dδ)
                (SubstTm dp dδ))

SubstTyEq (TyRefl dA) dδ = TyRefl (SubstTy dA dδ)
SubstTyEq (TySymm dA=) dδ = TySymm (SubstTyEq dA= dδ)
SubstTyEq (TyTran dB dA= dB=) dδ = TyTran (SubstTy dB dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= dδ)

SubstTyEq UUCong dδ = UUCong
SubstTyEq (ElCong dv=) dδ = ElCong (SubstTmEq dv= dδ)
SubstTyEq ElUU= dδ = ElUU=
SubstTyEq (SumCong dA= dB=) dδ = SumCong (SubstTyEq dA= dδ) (SubstTyEq dB= dδ)
SubstTyEq (ElSum= da db) dδ = ElSum= (SubstTm da dδ) (SubstTm db dδ)
SubstTyEq (PiCong dA dA= dB=) dδ = PiCong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ))
SubstTyEq (ElPi= da db) dδ = ElPi= (SubstTm da dδ) (SubstTm db (WeakMor+ (El da) dδ))
SubstTyEq (SigCong dA dA= dB=) dδ = SigCong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ))
SubstTyEq (ElSig= da db) dδ = ElSig= (SubstTm da dδ) (SubstTm db (WeakMor+ (El da) dδ))
SubstTyEq EmptyCong dδ = EmptyCong
SubstTyEq ElEmpty= dδ = ElEmpty=
SubstTyEq UnitCong dδ = UnitCong
SubstTyEq ElUnit= dδ = ElUnit=
SubstTyEq NatCong dδ = NatCong
SubstTyEq ElNat= dδ = ElNat=
SubstTyEq (IdCong dA= da= db=) dδ = IdCong (SubstTyEq dA= dδ) (SubstTmEq da= dδ) (SubstTmEq db= dδ)
SubstTyEq (ElId= da du dv) dδ = ElId= (SubstTm da dδ) (SubstTm du dδ) (SubstTm dv dδ)

SubstTmEq (TmRefl du) dδ = TmRefl (SubstTm du dδ)
SubstTmEq (TmSymm du=) dδ = TmSymm (SubstTmEq du= dδ)
SubstTmEq (TmTran dv du= dv=) dδ = TmTran (SubstTm dv dδ) (SubstTmEq du= dδ) (SubstTmEq dv= dδ)
SubstTmEq (ConvEq dA du= dA=) dδ = ConvEq (SubstTy dA dδ) (SubstTmEq du= dδ) (SubstTyEq dA= dδ) 
SubstTmEq UUUUCong dδ = UUUUCong

SubstTmEq (SumUUCong da= db=) dδ = SumUUCong (SubstTmEq da= dδ) (SubstTmEq db= dδ)
SubstTmEq (InlCong dA= dB= da=) dδ = InlCong (SubstTyEq dA= dδ) (SubstTyEq dB= dδ) (SubstTmEq da= dδ)
SubstTmEq (InrCong dA= dB= db=) dδ = InrCong (SubstTyEq dA= dδ) (SubstTyEq dB= dδ) (SubstTmEq db= dδ)
SubstTmEq (MatchCong dA= dB= dC= dA dda= dB ddb= du=) dδ =
          congTmEqTy! []Ty-substTy (MatchCong (SubstTyEq dA= dδ)
                                              (SubstTyEq dB= dδ)
                                              (SubstTyEq dC= (WeakMor+ (Sum dA dB) dδ))
                                              (SubstTy dA dδ)
                                              (congTmEqTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1 (ap-inl-Tm []Ty-weakenTy []Ty-weakenTy refl)) (SubstTmEq dda= (WeakMor+ dA dδ)))
                                              (SubstTy dB dδ)
                                              (congTmEqTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1 (ap-inr-Tm []Ty-weakenTy []Ty-weakenTy refl)) (SubstTmEq ddb= (WeakMor+ dB dδ)))
                                              (SubstTmEq du= dδ))
SubstTmEq (PiUUCong da da= db=) dδ = PiUUCong (SubstTm da dδ) (SubstTmEq da= dδ) (SubstTmEq db= (WeakMor+ (El da) dδ))
SubstTmEq (LamCong dA dA= dB= du=) dδ = LamCong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ)) (SubstTmEq du= (WeakMor+ dA dδ))
SubstTmEq (AppCong dA dA= dB= df= da=) dδ = congTmEqTy! []Ty-substTy (AppCong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ)) (SubstTmEq df= dδ) (SubstTmEq da= dδ))
SubstTmEq (SigUUCong da da= db=) dδ = SigUUCong (SubstTm da dδ) (SubstTmEq da= dδ) (SubstTmEq db= (WeakMor+ (El da) dδ))
SubstTmEq (PairCong dA dA= dB= da= db=) dδ = PairCong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ)) (SubstTmEq da= dδ) (congTmEqTy []Ty-substTy (SubstTmEq db= dδ))
SubstTmEq (Pr1Cong dA dA= dB= du=) dδ = Pr1Cong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ)) (SubstTmEq du= dδ)
SubstTmEq (Pr2Cong dA dA= dB= du=) dδ = congTmEqTy! []Ty-substTy (Pr2Cong (SubstTy dA dδ) (SubstTyEq dA= dδ) (SubstTyEq dB= (WeakMor+ dA dδ)) (SubstTmEq du= dδ))
SubstTmEq EmptyUUCong dδ = EmptyUUCong
SubstTmEq (EmptyelimCong dA= du=) dδ = congTmEqTy! []Ty-substTy (EmptyelimCong (SubstTyEq dA= (WeakMor+ Empty dδ)) (SubstTmEq du= dδ))
SubstTmEq UnitUUCong dδ = UnitUUCong
SubstTmEq TTCong dδ = TTCong
SubstTmEq (UnitelimCong dA= ddtt= du=) dδ = congTmEqTy! []Ty-substTy (UnitelimCong (SubstTyEq dA= (WeakMor+ Unit dδ)) (congTmEqTy []Ty-substTy (SubstTmEq ddtt= dδ)) (SubstTmEq du= dδ))
SubstTmEq NatUUCong dδ = NatUUCong
SubstTmEq ZeroCong dδ = ZeroCong
SubstTmEq (SucCong du=) dδ = SucCong (SubstTmEq du= dδ)
SubstTmEq (NatelimCong dP dP= ddO= ddS= du=) dδ =
  congTmEqTy! []Ty-substTy
    (NatelimCong (SubstTy dP (WeakMor+ Nat dδ))
                 (SubstTyEq dP= (WeakMor+ Nat dδ))
                 (congTmEqTy []Ty-substTy (SubstTmEq ddO= dδ))
                 (congTmEqTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1-weakenTy1 refl) (SubstTmEq ddS= (WeakMor+ dP (WeakMor+ Nat dδ))))
                 (SubstTmEq du= dδ))
SubstTmEq (IdUUCong da= du= dv=) dδ = IdUUCong (SubstTmEq da= dδ) (SubstTmEq du= dδ) (SubstTmEq dv= dδ)
SubstTmEq (ReflCong dA= da=) dδ = ReflCong (SubstTyEq dA= dδ) (SubstTmEq da= dδ)
SubstTmEq (JJCong dA dA= dP= dd= da= db= dp=) dδ =
  let dwA = congTy! []Ty-weakenTy (WeakTy (SubstTy dA dδ)) in
  congTmEqTy! ([]Ty-subst3Ty)
              (JJCong (SubstTy dA dδ)
                      (SubstTyEq dA= dδ)
                      (congTyCtxEq (Ctx+= (Ctx+= refl []Ty-weakenTy) (ap-id-Ty ([]Ty-weakenTy ∙ ap weakenTy []Ty-weakenTy) refl refl))
                                   (SubstTyEq dP= (WeakMor+~ (Id (congTy! ([]Ty-weakenTy ∙ ap weakenTy []Ty-weakenTy) (WeakTy (WeakTy (SubstTy dA dδ))))
                                                                 (congTmTy! ([]Ty-weakenTy ∙ ap weakenTy []Ty-weakenTy) (VarPrevLast (SubstTy dA dδ)))
                                                                 (congTmTy! []Ty-weakenTy (VarLast dwA)))
                                                             (WeakMor+~ dwA (WeakMor+ dA dδ)))))
                      (congTmEqTy ([]Ty-subst3Ty ∙ ap-subst3Ty []Ty-weakenTy3 refl refl (ap-refl-Tm []Ty-weakenTy refl)) (SubstTmEq dd= (WeakMor+ dA dδ)))
                      (SubstTmEq da= dδ)
                      (SubstTmEq db= dδ)
                      (SubstTmEq dp= dδ))

SubstTmEq (BetaInl {da = da'} dA dB dC dda ddb da) dδ = congTmEq! refl ([]Tm-substTm da') []Ty-substTy (BetaInl (SubstTy dA dδ) (SubstTy dB dδ) (SubstTy dC (WeakMor+ (Sum dA dB) dδ)) (congTmTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1 (ap-inl-Tm []Ty-weakenTy []Ty-weakenTy refl)) (SubstTm dda (WeakMor+ dA dδ))) (congTmTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1 (ap-inr-Tm []Ty-weakenTy []Ty-weakenTy refl)) (SubstTm ddb (WeakMor+ dB dδ))) (SubstTm da dδ))
SubstTmEq (BetaInr {db = db'} dA dB dC dda ddb db) dδ = congTmEq! refl ([]Tm-substTm db') []Ty-substTy (BetaInr (SubstTy dA dδ) (SubstTy dB dδ) (SubstTy dC (WeakMor+ (Sum dA dB) dδ)) (congTmTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1 (ap-inl-Tm []Ty-weakenTy []Ty-weakenTy refl)) (SubstTm dda (WeakMor+ dA dδ))) (congTmTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1 (ap-inr-Tm []Ty-weakenTy []Ty-weakenTy refl)) (SubstTm ddb (WeakMor+ dB dδ))) (SubstTm db dδ))
SubstTmEq (BetaPi {u = u} dA dB du da) dδ = congTmEq! refl ([]Tm-substTm u) []Ty-substTy (BetaPi (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm du (WeakMor+ dA dδ )) (SubstTm da dδ))
SubstTmEq (BetaSig1 dA dB da db) dδ = BetaSig1 (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm da dδ) (congTmTy []Ty-substTy (SubstTm db dδ))
SubstTmEq (BetaSig2 dA dB da db) dδ = congTmEqTy! []Ty-substTy (BetaSig2 (SubstTy dA dδ) (SubstTy dB (WeakMor+ dA dδ)) (SubstTm da dδ) (congTmTy []Ty-substTy (SubstTm db dδ)))
SubstTmEq (BetaNatZero dP ddO ddS) dδ =
  congTmEqTy! []Ty-substTy
              (BetaNatZero (SubstTy dP (WeakMor+ Nat dδ))
                           (congTmTy []Ty-substTy (SubstTm ddO dδ))
                           (congTmTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1-weakenTy1 refl) (SubstTm ddS (WeakMor+ dP (WeakMor+ Nat dδ)))))
SubstTmEq (BetaUnit dA ddtt) dδ = congTmEq! refl refl []Ty-substTy (BetaUnit (SubstTy dA (WeakMor+ Unit dδ)) (congTmTy []Ty-substTy (SubstTm ddtt dδ)))
SubstTmEq (BetaNatSuc {dS = dS} dP ddO ddS du) dδ =
  congTmEq! refl ([]Tm-substTm2 dS) []Ty-substTy
            (BetaNatSuc (SubstTy dP (WeakMor+ Nat dδ))
                        (congTmTy []Ty-substTy (SubstTm ddO dδ))
                        (congTmTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1-weakenTy1 refl) (SubstTm ddS (WeakMor+ dP (WeakMor+ Nat dδ))))
                        (SubstTm du dδ))
SubstTmEq (BetaIdRefl {A = A} {d = d} dA dP dd da) dδ =  -- Using WeakMor+ in this clause creates termination errors
  let dwA = congTy! []Ty-weakenTy (WeakTy (SubstTy dA dδ)) in
  congTmEq! refl ([]Tm-substTm d) []Ty-subst3Ty
            (BetaIdRefl (SubstTy dA dδ)
                        (congTyCtx (Ctx+= (Ctx+= refl []Ty-weakenTy) (ap-id-Ty ([]Ty-weakenTy ∙ ap weakenTy []Ty-weakenTy) refl refl))
                                   (SubstTy dP (WeakMor+~ (Id (congTy! ([]Ty-weakenTy ∙ ap weakenTy []Ty-weakenTy) (WeakTy (WeakTy (SubstTy dA dδ))))
                                                              (congTmTy! ([]Ty-weakenTy ∙ ap weakenTy []Ty-weakenTy) (VarPrevLast (SubstTy dA dδ)))
                                                              (congTmTy! []Ty-weakenTy (VarLast dwA)))
                                                          (WeakMor+~ dwA (WeakMor+ dA dδ)))))
                        (congTmTy ([]Ty-subst3Ty ∙ ap-subst3Ty []Ty-weakenTy3 refl refl (ap-refl-Tm []Ty-weakenTy refl)) (SubstTm dd (WeakMor+ dA dδ)))
                        (SubstTm da dδ))

SubstTmEq (EtaSum dA dB du) dδ = congTmEq! refl (ap-match-Tm refl refl []Ty-weakenTy (ap-inl-Tm []Ty-weakenTy []Ty-weakenTy refl) (ap-inr-Tm []Ty-weakenTy []Ty-weakenTy refl) refl) refl (EtaSum (SubstTy dA dδ) (SubstTy dB dδ) (SubstTm du dδ))
SubstTmEq (EtaPi {f = f} dA dB df) dδ =
  congTmEq! refl (ap-lam-Tm refl refl (ap-app-Tm []Ty-weakenTy []Ty-weakenTy1 ([]Tm-weakenTm f) refl)) refl
            (EtaPi (SubstTy dA dδ)
                   (SubstTy dB (WeakMor+ dA dδ))
                   (SubstTm df dδ))
SubstTmEq (EtaSig {u = u} dA dB du) dδ =
  EtaSig (SubstTy dA dδ)
         (SubstTy dB (WeakMor+ dA dδ))
         (SubstTm du dδ)

SubstTyMorEq UU dδ dδ= = UUCong
SubstTyMorEq (El dv) dδ dδ= = ElCong (SubstTmMorEq dv dδ dδ=)
SubstTyMorEq (Sum dA dB) dδ dδ= = SumCong (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB dδ dδ=)
SubstTyMorEq (Pi dA dB) dδ dδ= = PiCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=))
SubstTyMorEq (Sig dA dB) dδ dδ= = SigCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=))
SubstTyMorEq Empty dδ dδ= = EmptyCong
SubstTyMorEq Unit dδ dδ= = UnitCong
SubstTyMorEq Nat dδ dδ= = NatCong
SubstTyMorEq (Id dA da db) dδ dδ= = IdCong (SubstTyMorEq dA dδ dδ=) (SubstTmMorEq da dδ dδ=) (SubstTmMorEq db dδ dδ=)

SubstTmMorEq (Var k dA) dδ dδ= = getTySubstEq k dδ=
SubstTmMorEq (Conv dA du dA=) dδ dδ= = ConvEq (SubstTy dA dδ) (SubstTmMorEq du dδ dδ=) (SubstTyEq dA= dδ)

SubstTmMorEq UUUU dδ dδ= = UUUUCong
SubstTmMorEq (PiUU da db) dδ dδ= = PiUUCong (SubstTm da dδ) (SubstTmMorEq da dδ dδ=) (SubstTmMorEq db (WeakMor+ (El da) dδ) (WeakMor+Eq (El da) dδ dδ=))
SubstTmMorEq (SumUU da db) dδ dδ= = SumUUCong (SubstTmMorEq da dδ dδ=) (SubstTmMorEq db dδ dδ=)
SubstTmMorEq (Inl dA dB da) dδ dδ= = InlCong (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB dδ dδ=) (SubstTmMorEq da dδ dδ=)
SubstTmMorEq (Inr dA dB db) dδ dδ= = InrCong (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB dδ dδ=) (SubstTmMorEq db dδ dδ=)
SubstTmMorEq (Match dA dB dC dda ddb du) dδ dδ= = congTmEqTy! []Ty-substTy (MatchCong (SubstTyMorEq dA dδ dδ=)
                                                                                      (SubstTyMorEq dB dδ dδ=)
                                                                                      (SubstTyMorEq dC (WeakMor+ (Sum dA dB) dδ) (WeakMor+Eq (Sum dA dB) dδ dδ=))
                                                                                      (SubstTy dA dδ)
                                                                                      (congTmEqTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1 (ap-inl-Tm []Ty-weakenTy []Ty-weakenTy refl))
                                                                                                  (SubstTmMorEq dda (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=)))
                                                                                      (SubstTy dB dδ)
                                                                                      (congTmEqTy ([]Ty-substTy ∙ ap-substTy []Ty-weakenTy1 (ap-inr-Tm []Ty-weakenTy []Ty-weakenTy refl))
                                                                                                  (SubstTmMorEq ddb (WeakMor+ dB dδ) (WeakMor+Eq dB dδ dδ=)))
                                                                                      (SubstTmMorEq du dδ dδ=))
SubstTmMorEq (Lam dA dB du) dδ dδ= = LamCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=)) (SubstTmMorEq du (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=))
SubstTmMorEq (App dA dB df da) dδ dδ= = congTmEqTy! []Ty-substTy (AppCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=)) (SubstTmMorEq df dδ dδ=) (SubstTmMorEq da dδ dδ=))
SubstTmMorEq (SigUU da db) dδ dδ= = SigUUCong (SubstTm da dδ) (SubstTmMorEq da dδ dδ=) (SubstTmMorEq db (WeakMor+ (El da) dδ) (WeakMor+Eq (El da) dδ dδ=))
SubstTmMorEq (Pair dA dB da db) dδ dδ= = PairCong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=)) (SubstTmMorEq da dδ dδ=) (congTmEqTy []Ty-substTy (SubstTmMorEq db  dδ dδ=))
SubstTmMorEq (Pr1 dA dB du) dδ dδ= = Pr1Cong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=)) (SubstTmMorEq du dδ dδ=)
SubstTmMorEq (Pr2 dA dB du) dδ dδ= = congTmEqTy! []Ty-substTy (Pr2Cong (SubstTy dA dδ) (SubstTyMorEq dA dδ dδ=) (SubstTyMorEq dB (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=)) (SubstTmMorEq du dδ dδ=))

SubstTmMorEq EmptyUU dδ dδ= = EmptyUUCong
SubstTmMorEq (Emptyelim dA du) dδ dδ= = congTmEqTy! []Ty-substTy (EmptyelimCong (SubstTyMorEq dA (WeakMor+ Empty dδ) (WeakMor+Eq Empty dδ dδ=)) (SubstTmMorEq du dδ dδ=))
SubstTmMorEq UnitUU dδ dδ= = UnitUUCong
SubstTmMorEq TT dδ dδ= = TTCong
SubstTmMorEq (Unitelim dA ddtt du) dδ dδ= = congTmEqTy! []Ty-substTy (UnitelimCong (SubstTyMorEq dA (WeakMor+ Unit dδ) (WeakMor+Eq Unit dδ dδ=)) (congTmEqTy []Ty-substTy (SubstTmMorEq ddtt dδ dδ=)) (SubstTmMorEq du dδ dδ=))

SubstTmMorEq NatUU dδ dδ= = NatUUCong
SubstTmMorEq Zero dδ dδ= = ZeroCong
SubstTmMorEq (Suc du) dδ dδ= = SucCong (SubstTmMorEq du dδ dδ=)
SubstTmMorEq (Natelim dP ddO ddS du) dδ dδ= =
  congTmEqTy! []Ty-substTy
              (NatelimCong (SubstTy dP (WeakMor+ Nat dδ))
                           (SubstTyMorEq dP (WeakMor+ Nat dδ) (WeakMor+Eq Nat dδ dδ=))
                           (congTmEqTy []Ty-substTy (SubstTmMorEq ddO dδ dδ=))
                           (congTmEqTy ([]Ty-substTy ∙ ap-substTy ([]Ty-weakenTy1 ∙ ap (weakenTy' (prev last)) []Ty-weakenTy1) refl) (SubstTmMorEq ddS (WeakMor+ dP (WeakMor+ Nat dδ)) (WeakMor+Eq dP (WeakMor+ Nat dδ) (WeakMor+Eq Nat dδ dδ=))))
                           (SubstTmMorEq du dδ dδ=))
SubstTmMorEq (IdUU da du dv) dδ dδ= = IdUUCong (SubstTmMorEq da dδ dδ=) (SubstTmMorEq du dδ dδ=) (SubstTmMorEq dv dδ dδ=)
SubstTmMorEq (Refl dA da) dδ dδ= = ReflCong (SubstTyMorEq dA dδ dδ=) (SubstTmMorEq da dδ dδ=)
SubstTmMorEq (JJ dA dP dd da db dp) dδ dδ= =
  let dwA = congTy! []Ty-weakenTy (WeakTy (SubstTy dA dδ)) in
  congTmEqTy! []Ty-subst3Ty
              (JJCong (SubstTy dA dδ)
                      (SubstTyMorEq dA dδ dδ=)
                      ((congTyCtxEq (Ctx+= (Ctx+= refl []Ty-weakenTy) (ap-id-Ty ([]Ty-weakenTy ∙ ap weakenTy []Ty-weakenTy) refl refl))
                                   (SubstTyMorEq dP (WeakMor+~ (Id (congTy! ([]Ty-weakenTy ∙ ap weakenTy []Ty-weakenTy) (WeakTy (WeakTy (SubstTy dA dδ))))
                                                                   (congTmTy! ([]Ty-weakenTy ∙ ap weakenTy []Ty-weakenTy) (VarPrevLast (SubstTy dA dδ)))
                                                                   (congTmTy! []Ty-weakenTy (VarLast dwA)))
                                                               (WeakMor+~ dwA (WeakMor+ dA dδ)))
                                                    (WeakMor+Eq (Id (WeakTy (WeakTy dA)) (VarPrevLast dA) (VarLast (WeakTy dA)))
                                                                (WeakMor+ (WeakTy dA) (WeakMor+ dA dδ))
                                                                (WeakMor+Eq (WeakTy dA) (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=))))))
                             (congTmEqTy ([]Ty-subst3Ty ∙ ap-subst3Ty []Ty-weakenTy3 refl refl (ap-refl-Tm []Ty-weakenTy refl)) (SubstTmMorEq dd (WeakMor+ dA dδ) (WeakMor+Eq dA dδ dδ=)))
                             (SubstTmMorEq da dδ dδ=)
                             (SubstTmMorEq db dδ dδ=)
                             (SubstTmMorEq dp dδ dδ=))

WeakTy (Pi dA dB) = Pi (WeakTy dA) (WeakTy dB)
WeakTy UU = UU
WeakTy (Sum dA dB) = Sum (WeakTy dA) (WeakTy dB)
WeakTy (El dv) = El (WeakTm dv)
WeakTy (Sig dA dB) = Sig (WeakTy dA) (WeakTy dB)
WeakTy Empty = Empty
WeakTy Unit = Unit
WeakTy Nat = Nat
WeakTy (Id dA da db) = Id (WeakTy dA) (WeakTm da) (WeakTm db)

WeakTm (Conv dA du dA=) = Conv (WeakTy dA) (WeakTm du) (WeakTyEq dA=)
WeakTm {k = last} (Var k' dA) = Var (prev k') (WeakTy dA)
WeakTm {k = prev k} {Γ = Γ , A} (Var last dA) = congTmTy! weakenTy-weakenTy (Var _ (congTy weakenTy-weakenTy (WeakTy dA)))
WeakTm {k = prev k} {Γ = Γ , A} (Var (prev k') dA) = congTmTy! (weakenTy-weakenTy ∙ ap weakenTy (weaken-getTy k k' Γ _)) (Var _ (congTy (weakenTy-weakenTy ∙ ap weakenTy (weaken-getTy _ _ _ _)) (WeakTy {k = prev k} dA)))
WeakTm (PiUU da db) = PiUU (WeakTm da) (WeakTm db)
WeakTm (Lam dA dB du) = Lam (WeakTy dA) (WeakTy dB) (WeakTm du)
WeakTm (App dA dB df da) = congTmTy! weakenTy-substTy (App (WeakTy dA) (WeakTy dB) (WeakTm df) (WeakTm da))
WeakTm UUUU = UUUU
WeakTm (SumUU da db) = SumUU (WeakTm da) (WeakTm db)
WeakTm (Inl dA dB da) = Inl (WeakTy dA) (WeakTy dB) (WeakTm da)
WeakTm (Inr dA dB db) = Inr (WeakTy dA) (WeakTy dB) (WeakTm db)
WeakTm (Match dA dB dC dda ddb du) = congTmTy! weakenTy-substTy (Match (WeakTy dA) (WeakTy dB) (WeakTy dC)
                                                                       (congTmTy (weakenTy-substTy ∙ ap-substTy weakenTy-weakenTy1 (ap-inl-Tm weakenTy-weakenTy weakenTy-weakenTy refl))
                                                                                 (WeakTm dda))
                                                                       (congTmTy (weakenTy-substTy ∙ ap-substTy weakenTy-weakenTy1 (ap-inr-Tm weakenTy-weakenTy weakenTy-weakenTy refl))
                                                                                 (WeakTm ddb))
                                                                       (WeakTm du))
WeakTm (SigUU da db) = SigUU (WeakTm da) (WeakTm db)
WeakTm (Pair dA dB da db) = Pair (WeakTy dA) (WeakTy dB) (WeakTm da) (congTmTy weakenTy-substTy (WeakTm db))
WeakTm (Pr1 dA dB du) = Pr1 (WeakTy dA) (WeakTy dB) (WeakTm du)
WeakTm (Pr2 dA dB du) = congTmTy! weakenTy-substTy (Pr2 (WeakTy dA) (WeakTy dB) (WeakTm du))

WeakTm EmptyUU = EmptyUU
WeakTm (Emptyelim dA du) = congTmTy! weakenTy-substTy (Emptyelim (WeakTy dA) (WeakTm du))
WeakTm UnitUU = UnitUU
WeakTm TT = TT
WeakTm (Unitelim dA ddtt du) = congTmTy! weakenTy-substTy (Unitelim (WeakTy dA) (congTmTy weakenTy-substTy (WeakTm ddtt)) (WeakTm du))
WeakTm NatUU = NatUU
WeakTm Zero = Zero
WeakTm (Suc du) = Suc (WeakTm du)
WeakTm (Natelim dP ddO ddS du) =
  congTmTy! weakenTy-substTy
            (Natelim (WeakTy dP)
                     (congTmTy weakenTy-substTy (WeakTm ddO))
                     (congTmTy (weakenTy-substTy ∙ ap-substTy weakenTy-weakenTy-weakenTy1 refl) (WeakTm ddS))
                     (WeakTm du))
WeakTm (IdUU da du dv) = IdUU (WeakTm da) (WeakTm du) (WeakTm dv)
WeakTm (Refl dA da) = Refl (WeakTy dA) (WeakTm da)
WeakTm (JJ dA dP dd da db dp) =
  congTmTy! weakenTy-subst3Ty
            (JJ (WeakTy dA)
                (congTyCtx (Ctx+= (Ctx+= refl weakenTy-weakenTy) (ap-id-Ty (weakenTy-weakenTy ∙ ap weakenTy weakenTy-weakenTy) refl refl)) (WeakTy dP))
                (congTmTy (weakenTy-subst3Ty ∙ ap-subst3Ty weakenTy-weakenTy3 refl refl (ap-refl-Tm weakenTy-weakenTy refl)) (WeakTm dd))
                (WeakTm da)
                (WeakTm db)
                (WeakTm dp))

WeakTyEq (TyRefl dA) = TyRefl (WeakTy dA)
WeakTyEq (TySymm dA=) = TySymm (WeakTyEq dA=)
WeakTyEq (TyTran dB dA= dB=) = TyTran (WeakTy dB) (WeakTyEq dA=) (WeakTyEq dB=)
WeakTyEq UUCong = UUCong
WeakTyEq (ElCong dv=) = ElCong (WeakTmEq dv=)
WeakTyEq ElUU= = ElUU=
WeakTyEq (SumCong dA= dB=) = SumCong (WeakTyEq dA=) (WeakTyEq dB=)
WeakTyEq (ElSum= da db) = ElSum= (WeakTm da) (WeakTm db)
WeakTyEq (PiCong dA dA= dB=) = PiCong (WeakTy dA) (WeakTyEq dA=) (WeakTyEq dB=)
WeakTyEq (ElPi= da db) = ElPi= (WeakTm da) (WeakTm db)
WeakTyEq (SigCong dA dA= dB=) = SigCong (WeakTy dA) (WeakTyEq dA=) (WeakTyEq dB=)
WeakTyEq (ElSig= da db) = ElSig= (WeakTm da) (WeakTm db)
WeakTyEq EmptyCong = EmptyCong
WeakTyEq ElEmpty= = ElEmpty=
WeakTyEq UnitCong = UnitCong
WeakTyEq ElUnit= = ElUnit=
WeakTyEq NatCong = NatCong
WeakTyEq ElNat= = ElNat=
WeakTyEq (IdCong dA= da= db=) = IdCong (WeakTyEq dA=) (WeakTmEq da=) (WeakTmEq db=)
WeakTyEq (ElId= da du dv) = ElId= (WeakTm da) (WeakTm du) (WeakTm dv)

WeakTmEq (TmRefl du) = TmRefl (WeakTm du)
WeakTmEq (TmSymm du=) = TmSymm (WeakTmEq du=)
WeakTmEq (TmTran dv du= dv=) = TmTran (WeakTm dv) (WeakTmEq du=) (WeakTmEq dv=)
WeakTmEq (ConvEq dA du= dA=) = ConvEq (WeakTy dA) (WeakTmEq du=) (WeakTyEq dA=)
WeakTmEq UUUUCong = UUUUCong
WeakTmEq (SumUUCong da= db=) = SumUUCong (WeakTmEq da=) (WeakTmEq db=)
WeakTmEq (InlCong dA= dB= da=) = InlCong (WeakTyEq dA=) (WeakTyEq dB=) (WeakTmEq da=)
WeakTmEq (InrCong dA= dB= db=) = InrCong (WeakTyEq dA=) (WeakTyEq dB=) (WeakTmEq db=)
WeakTmEq (MatchCong dA= dB= dC= dA dda= dB ddb= du=) =
                    congTmEqTy! weakenTy-substTy (MatchCong (WeakTyEq dA=) (WeakTyEq dB=) (WeakTyEq dC=)
                                                            (WeakTy dA)
                                                            (congTmEqTy (weakenTy-substTy ∙ ap-substTy weakenTy-weakenTy1 (ap-inl-Tm weakenTy-weakenTy weakenTy-weakenTy refl))
                                                                        (WeakTmEq dda=))
                                                            (WeakTy dB)
                                                            (congTmEqTy (weakenTy-substTy ∙ ap-substTy weakenTy-weakenTy1 (ap-inr-Tm weakenTy-weakenTy weakenTy-weakenTy refl))
                                                                        (WeakTmEq ddb=))
                                                            (WeakTmEq du=))
WeakTmEq (PiUUCong da da= db=) = PiUUCong (WeakTm da) (WeakTmEq da=) (WeakTmEq db=)
WeakTmEq (LamCong dA dA= dB= du=) = LamCong (WeakTy dA) (WeakTyEq dA=) (WeakTyEq dB=) (WeakTmEq du=)
WeakTmEq (AppCong dA dA= dB= df= da=) = congTmEqTy! weakenTy-substTy (AppCong (WeakTy dA) (WeakTyEq dA=) (WeakTyEq dB=) (WeakTmEq  df=) (WeakTmEq da=))
WeakTmEq (SigUUCong da da= db=) = SigUUCong (WeakTm da) (WeakTmEq da=) (WeakTmEq db=)
WeakTmEq (PairCong dA dA= dB= da= db=) = PairCong (WeakTy dA) (WeakTyEq dA=) (WeakTyEq dB=) (WeakTmEq da=) (congTmEqTy weakenTy-substTy (WeakTmEq db=))
WeakTmEq (Pr1Cong dA dA= dB= du=) = Pr1Cong (WeakTy dA) (WeakTyEq dA=) (WeakTyEq dB=) (WeakTmEq du=)
WeakTmEq (Pr2Cong dA dA= dB= du=) = congTmEqTy! weakenTy-substTy (Pr2Cong (WeakTy dA) (WeakTyEq dA=) (WeakTyEq dB=) (WeakTmEq du=))
WeakTmEq EmptyUUCong = EmptyUUCong
WeakTmEq (EmptyelimCong dA= du=) = congTmEqTy! weakenTy-substTy (EmptyelimCong (WeakTyEq dA=) (WeakTmEq du=))
WeakTmEq UnitUUCong = UnitUUCong
WeakTmEq TTCong = TTCong
WeakTmEq (UnitelimCong dA= ddtt= du=) = congTmEqTy! weakenTy-substTy (UnitelimCong (WeakTyEq dA=) (congTmEqTy weakenTy-substTy (WeakTmEq ddtt=)) (WeakTmEq du=))
WeakTmEq NatUUCong = NatUUCong
WeakTmEq ZeroCong = ZeroCong
WeakTmEq (SucCong du=) = SucCong (WeakTmEq du=)
WeakTmEq (NatelimCong dP dP= ddO= ddS= du=) =
  congTmEqTy! weakenTy-substTy
              (NatelimCong (WeakTy dP)
                           (WeakTyEq dP=)
                           (congTmEqTy weakenTy-substTy (WeakTmEq ddO=))
                           (congTmEqTy (weakenTy-substTy ∙ ap-substTy weakenTy-weakenTy-weakenTy1 refl) (WeakTmEq ddS=))
                           (WeakTmEq du=))
WeakTmEq (IdUUCong da= du= dv=) = IdUUCong (WeakTmEq da=) (WeakTmEq du=) (WeakTmEq dv=)
WeakTmEq (ReflCong dA= da=) = ReflCong (WeakTyEq dA=) (WeakTmEq da=)
WeakTmEq (JJCong dA dA= dP= dd= da= db= dp=) =
  congTmEqTy! weakenTy-subst3Ty
              (JJCong (WeakTy dA)
                      (WeakTyEq dA=)
                      (congTyCtxEq (Ctx+= (Ctx+= refl weakenTy-weakenTy) (ap-id-Ty (weakenTy-weakenTy ∙ ap weakenTy weakenTy-weakenTy) refl refl)) (WeakTyEq dP=))
                      (congTmEqTy (weakenTy-subst3Ty ∙ ap-subst3Ty weakenTy-weakenTy3 refl refl (ap-refl-Tm weakenTy-weakenTy refl)) (WeakTmEq dd=))
                      (WeakTmEq da=)
                      (WeakTmEq db=)
                      (WeakTmEq dp=))

WeakTmEq {u = match _ _ _ da' _ _} (BetaInl dA dB dC dda ddb da) = congTmEq! refl (weakenTm-substTm da') weakenTy-substTy
                                                                             (BetaInl (WeakTy dA) (WeakTy dB) (WeakTy dC)
                                                                                      (congTmTy (weakenTy-substTy ∙ ap-substTy weakenTy-weakenTy1 (ap-inl-Tm weakenTy-weakenTy weakenTy-weakenTy refl))
                                                                                                (WeakTm dda))
                                                                                      (congTmTy (weakenTy-substTy ∙ ap-substTy weakenTy-weakenTy1 (ap-inr-Tm weakenTy-weakenTy weakenTy-weakenTy refl))
                                                                                                (WeakTm ddb))
                                                                                      (WeakTm da))
WeakTmEq {u = match _ _ _ _ db' _} (BetaInr dA dB dC dda ddb db) = congTmEq! refl (weakenTm-substTm db') weakenTy-substTy
                                                                             (BetaInr (WeakTy dA) (WeakTy dB) (WeakTy dC)
                                                                                      (congTmTy (weakenTy-substTy ∙ ap-substTy weakenTy-weakenTy1 (ap-inl-Tm weakenTy-weakenTy weakenTy-weakenTy refl))
                                                                                                (WeakTm dda))
                                                                                      (congTmTy (weakenTy-substTy ∙ ap-substTy weakenTy-weakenTy1 (ap-inr-Tm weakenTy-weakenTy weakenTy-weakenTy refl))
                                                                                                (WeakTm ddb))
                                                                                      (WeakTm db))
WeakTmEq {u = app A B (lam A B u) a} (BetaPi dA dB du da) = congTmEq! refl (weakenTm-substTm u) weakenTy-substTy (BetaPi (WeakTy dA) (WeakTy dB) (WeakTm du) (WeakTm da))
WeakTmEq {u = pr1 A B (pair A B a b)} (BetaSig1 dA dB da db) = BetaSig1 (WeakTy dA) (WeakTy dB) (WeakTm da) (congTmTy weakenTy-substTy (WeakTm db))
WeakTmEq {u = pr2 A B (pair A B a b)} (BetaSig2 dA dB da db) = congTmEqTy! weakenTy-substTy (BetaSig2 (WeakTy dA) (WeakTy dB) (WeakTm da) (congTmTy weakenTy-substTy (WeakTm db)))
WeakTmEq {u = u} (BetaUnit dA ddtt) = congTmEqTy! weakenTy-substTy (BetaUnit (WeakTy dA) (congTmTy weakenTy-substTy (WeakTm ddtt)))
WeakTmEq {u = u} (BetaNatZero dP ddO ddS) =
  congTmEqTy! weakenTy-substTy
              (BetaNatZero (WeakTy dP)
                           (congTmTy weakenTy-substTy (WeakTm ddO))
                           (congTmTy (weakenTy-substTy ∙ ap-substTy weakenTy-weakenTy-weakenTy1 refl) (WeakTm ddS)))
WeakTmEq (BetaNatSuc {dS = dS} dP ddO ddS du) =
  congTmEq! refl (weakenTm-subst2Tm dS) weakenTy-substTy
              (BetaNatSuc (WeakTy dP)
                          (congTmTy weakenTy-substTy (WeakTm ddO))
                          (congTmTy (weakenTy-substTy ∙ ap-substTy weakenTy-weakenTy-weakenTy1 refl) (WeakTm ddS))
                          (WeakTm du))
WeakTmEq (BetaIdRefl {d = d} dA dP dd da) =
  congTmEq! refl (weakenTm-substTm d) weakenTy-subst3Ty
            (BetaIdRefl (WeakTy dA)
                        (congTyCtx (Ctx+= (Ctx+= refl weakenTy-weakenTy) (ap-id-Ty (weakenTy-weakenTy ∙ ap weakenTy weakenTy-weakenTy) refl refl)) (WeakTy dP))
                        (congTmTy (weakenTy-subst3Ty ∙ ap-subst3Ty weakenTy-weakenTy3 refl refl (ap-refl-Tm weakenTy-weakenTy refl)) (WeakTm dd))
                        (WeakTm da))

WeakTmEq (EtaSum {A = A} {B = B} {u = u} dA dB du) = congTmEq! refl
                                                               (ap-match-Tm refl refl weakenTy-weakenTy
                                                                            (ap-inl-Tm weakenTy-weakenTy weakenTy-weakenTy refl)
                                                                              (ap-inr-Tm weakenTy-weakenTy weakenTy-weakenTy refl)
                                                                                refl)
                                                               refl
                                                               (EtaSum (WeakTy dA) (WeakTy dB) (WeakTm du)) 
WeakTmEq (EtaPi {f = f} dA dB df) =
  congTmEq! refl (ap-lam-Tm refl refl (ap-app-Tm weakenTy-weakenTy weakenTy-weakenTy1 (! (weakenTmCommutes0 _ f)) refl)) refl
            (EtaPi (WeakTy dA)
                   (WeakTy dB)
                   (WeakTm df))
WeakTmEq (EtaSig {u = u} dA dB du) =
  EtaSig (WeakTy dA)
         (WeakTy dB)
         (WeakTm du)



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


{- Derivability of the identity morphism -}

idMorDerivable : {Γ : Ctx n} →  ⊢ Γ → (Γ ⊢ idMor n ∷> Γ)
idMorDerivable tt = tt
idMorDerivable (dΓ , dA) = (WeakMor (idMorDerivable dΓ) , congTm (! ([idMor]Ty _) ∙ substTy-weakenTy') refl (VarLast dA))

{- Conversion rules for types and terms are admissible -}

getTyDer : {Γ : Ctx n} (k : VarPos n) → ⊢ Γ → Derivable (Γ ⊢ getTy k Γ)
getTyDer last (dΓ , dA) = WeakTy dA
getTyDer (prev k) (dΓ , dA) = WeakTy (getTyDer k dΓ)

getTyCong : {Γ Δ : Ctx n} (k : VarPos n) → ⊢ Γ == Δ → Derivable (Γ ⊢ getTy k Γ == getTy k Δ)
getTyCong last (dΓ= , dA=) = WeakTyEq dA=
getTyCong (prev k) (dΓ= , dA=) = WeakTyEq (getTyCong k dΓ=)

ConvTy' : {Γ Δ : Ctx n} {A : TyExpr n} → Derivable (Δ ⊢ A) → (⊢ Γ == Δ) → ⊢ Γ → Derivable (Γ ⊢ A)
ConvTyEq' : {Γ Δ : Ctx n} {A B : TyExpr n} → Derivable (Δ ⊢ A == B) → (⊢ Γ == Δ) → ⊢ Γ → Derivable (Γ ⊢ A == B)
ConvTm' : {Γ Δ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Δ ⊢ u :> A) → (⊢ Γ == Δ) → ⊢ Γ → Derivable (Γ ⊢ u :> A)
ConvTmEq' : {Γ Δ : Ctx n} {A : TyExpr n} {u v : TmExpr n} → Derivable (Δ ⊢ u == v :> A) → (⊢ Γ == Δ) → ⊢ Γ → Derivable (Γ ⊢ u == v :> A)

ConvTy' UU dΓ= dΔ = UU
ConvTy' (El dv) dΓ= dΔ = El (ConvTm' dv dΓ= dΔ)
ConvTy' (Sum dA dB) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in Sum dA' (ConvTy' dB dΓ= dΔ)
ConvTy' (Pi dA dB) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in Pi dA' (ConvTy' dB (dΓ= , TyRefl dA') (dΔ , dA'))
ConvTy' (Sig dA dB) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in Sig dA' (ConvTy' dB (dΓ= , TyRefl dA') (dΔ , dA'))
ConvTy' Empty dΓ= dΔ = Empty
ConvTy' Unit dΓ= dΔ = Unit
ConvTy' Nat dΓ= dΔ = Nat
ConvTy' (Id dA da db) dΓ= dΔ = let da' = ConvTm' da dΓ= dΔ in Id (ConvTy' dA dΓ= dΔ) da' (ConvTm' db dΓ= dΔ)

ConvTyEq' (TyRefl dA) dΓ= dΔ = TyRefl (ConvTy' dA dΓ= dΔ)
ConvTyEq' (TySymm dA=) dΓ= dΔ = TySymm (ConvTyEq' dA= dΓ= dΔ)
ConvTyEq' (TyTran dB dA= dB=) dΓ= dΔ = TyTran (ConvTy' dB dΓ= dΔ) (ConvTyEq' dA= dΓ= dΔ) (ConvTyEq' dB= dΓ= dΔ)
ConvTyEq' UUCong dΓ= dΔ = UUCong
ConvTyEq' (ElCong dv=) dΓ= dΔ = ElCong (ConvTmEq' dv= dΓ= dΔ)
ConvTyEq' ElUU= dΓ= dΔ = ElUU=
ConvTyEq' (SumCong dA= dB=) dΓ= dΔ = SumCong (ConvTyEq' dA= dΓ= dΔ) (ConvTyEq' dB= dΓ= dΔ)
ConvTyEq' (ElSum= da db) dΓ= dΔ = ElSum= (ConvTm' da dΓ= dΔ) (ConvTm' db dΓ= dΔ)
ConvTyEq' (PiCong dA dA= dB=) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in PiCong dA' (ConvTyEq' dA= dΓ= dΔ) (ConvTyEq' dB= (dΓ= , TyRefl dA') (dΔ , dA'))
ConvTyEq' (ElPi= da db) dΓ= dΔ = let da' = ConvTm' da dΓ= dΔ in ElPi= da' (ConvTm' db (dΓ= , TyRefl (El da')) (dΔ , El da'))
ConvTyEq' (SigCong dA dA= dB=) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in SigCong dA' (ConvTyEq' dA= dΓ= dΔ) (ConvTyEq' dB= (dΓ= , TyRefl dA') (dΔ , dA'))
ConvTyEq' (ElSig= da db) dΓ= dΔ = let da' = ConvTm' da dΓ= dΔ in ElSig= da' (ConvTm' db (dΓ= , TyRefl (El da')) (dΔ , El da'))
ConvTyEq' EmptyCong dΓ= dΔ = EmptyCong
ConvTyEq' ElEmpty= dΓ= dΔ = ElEmpty=
ConvTyEq' UnitCong dΓ= dΔ = UnitCong
ConvTyEq' ElUnit= dΓ= dΔ = ElUnit=
ConvTyEq' NatCong dΓ= dΔ = NatCong
ConvTyEq' ElNat= dΓ= dΔ = ElNat=
ConvTyEq' (IdCong dA= da= db=) dΓ= dΔ = IdCong (ConvTyEq' dA= dΓ= dΔ)  (ConvTmEq' da= dΓ= dΔ) (ConvTmEq' db= dΓ= dΔ)
ConvTyEq' (ElId= da du dv) dΓ= dΔ = let da' = ConvTm' da dΓ= dΔ in ElId= da' (ConvTm' du dΓ= dΔ) (ConvTm' dv dΓ= dΔ)


ConvTm' (Var k dA) dΓ= dΔ = Conv (getTyDer k dΔ) (Var k (getTyDer k dΔ)) (getTyCong k dΓ=) 
ConvTm' (Conv dA du dA=) dΓ= dΔ = Conv (ConvTy' dA dΓ= dΔ) (ConvTm' du dΓ= dΔ) (ConvTyEq' dA= dΓ= dΔ)
ConvTm' UUUU dΓ= dΔ = UUUU
ConvTm' (SumUU da db) dΓ= dΔ = SumUU (ConvTm' da dΓ= dΔ) (ConvTm' db dΓ= dΔ)
ConvTm' (Inl dA dB da) dΓ= dΔ = Inl (ConvTy' dA dΓ= dΔ) (ConvTy' dB dΓ= dΔ) (ConvTm' da dΓ= dΔ)
ConvTm' (Inr dA dB db) dΓ= dΔ = Inr (ConvTy' dA dΓ= dΔ) (ConvTy' dB dΓ= dΔ) (ConvTm' db dΓ= dΔ)
ConvTm' (Match dA dB dC dda ddb du) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ
                                                 dB' = ConvTy' dB dΓ= dΔ in Match dA' dB' (ConvTy' dC (dΓ= , TyRefl (Sum dA' dB')) (dΔ , Sum dA' dB'))
                                                                                          (ConvTm' dda (dΓ= , TyRefl dA') (dΔ , dA'))
                                                                                          (ConvTm' ddb (dΓ= , TyRefl dB') (dΔ , dB'))
                                                                                          (ConvTm' du dΓ= dΔ)
ConvTm' (PiUU da db) dΓ= dΔ = let da' = ConvTm' da dΓ= dΔ in PiUU da' (ConvTm' db (dΓ= , TyRefl (El da')) (dΔ , El da'))
ConvTm' (Lam dA dB du) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in Lam dA' (ConvTy' dB (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTm' du (dΓ= , TyRefl dA') (dΔ , dA'))
ConvTm' (App dA dB df da) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in App dA' (ConvTy' dB (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTm' df dΓ= dΔ) (ConvTm' da dΓ= dΔ)
ConvTm' (SigUU da db) dΓ= dΔ = let da' = ConvTm' da dΓ= dΔ in SigUU da' (ConvTm' db (dΓ= , TyRefl (El da')) (dΔ , El da'))
ConvTm' (Pair dA dB da db) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in Pair dA' (ConvTy' dB (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTm' da dΓ= dΔ) (ConvTm' db dΓ= dΔ)
ConvTm' (Pr1 dA dB du) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in Pr1 dA' (ConvTy' dB (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTm' du dΓ= dΔ)
ConvTm' (Pr2 dA dB du) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in Pr2 dA' (ConvTy' dB (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTm' du dΓ= dΔ)
ConvTm' EmptyUU dΓ= dΔ = EmptyUU
ConvTm' (Emptyelim dA du) dΓ= dΔ = Emptyelim (ConvTy' dA (dΓ= , EmptyCong) (dΔ , Empty)) (ConvTm' du dΓ= dΔ)
ConvTm' UnitUU dΓ= dΔ = UnitUU
ConvTm' TT dΓ= dΔ = TT
ConvTm' (Unitelim dA ddtt du) dΓ= dΔ = Unitelim (ConvTy' dA (dΓ= , UnitCong) (dΔ , Unit)) (ConvTm' ddtt dΓ= dΔ) (ConvTm' du dΓ= dΔ)
ConvTm' NatUU dΓ= dΔ = NatUU
ConvTm' Zero dΓ= dΔ = Zero
ConvTm' (Suc du) dΓ= dΔ = Suc (ConvTm' du dΓ= dΔ)
ConvTm' (Natelim dP ddO ddS du) dΓ= dΔ = let dP' = ConvTy' dP (dΓ= , NatCong) (dΔ , Nat) in Natelim dP' (ConvTm' ddO dΓ= dΔ) (ConvTm' ddS ((dΓ= , NatCong) , TyRefl dP') ((dΔ , Nat) , dP')) (ConvTm' du dΓ= dΔ)
ConvTm' (IdUU da du dv) dΓ= dΔ = let da' = ConvTm' da dΓ= dΔ in IdUU da' (ConvTm' du dΓ= dΔ) (ConvTm' dv dΓ= dΔ)
ConvTm' (Refl dA da) dΓ= dΔ = Refl (ConvTy' dA dΓ= dΔ) (ConvTm' da dΓ= dΔ)
ConvTm' (JJ dA dP dd da db dp) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in JJ dA' (ConvTy' dP ((((dΓ= , TyRefl dA') , TyRefl (WeakTy dA')) , TyRefl (Id (WeakTy (WeakTy dA')) (VarPrevLast dA') (VarLast (WeakTy dA'))))) (((dΔ , dA') , WeakTy dA') , Id (WeakTy (WeakTy dA')) (VarPrevLast dA') (VarLast (WeakTy dA')))) (ConvTm' dd (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTm' da dΓ= dΔ) (ConvTm' db dΓ= dΔ) (ConvTm' dp dΓ= dΔ)

ConvTmEq' (TmRefl du) dΓ= dΔ = TmRefl (ConvTm' du dΓ= dΔ)
ConvTmEq' (TmSymm du=) dΓ= dΔ = TmSymm (ConvTmEq' du= dΓ= dΔ)
ConvTmEq' (TmTran dv du= dv=) dΓ= dΔ = TmTran (ConvTm' dv dΓ= dΔ) (ConvTmEq' du= dΓ= dΔ) (ConvTmEq' dv= dΓ= dΔ)
ConvTmEq' (ConvEq dA du= dA=) dΓ= dΔ = ConvEq (ConvTy' dA dΓ= dΔ) (ConvTmEq' du= dΓ= dΔ) (ConvTyEq' dA= dΓ= dΔ)
ConvTmEq' UUUUCong dΓ= dΔ = UUUUCong
ConvTmEq' (SumUUCong da= db=) dΓ= dΔ = SumUUCong (ConvTmEq' da= dΓ= dΔ) (ConvTmEq' db= dΓ= dΔ)
ConvTmEq' (InlCong dA= dB= da=) dΓ= dΔ = InlCong (ConvTyEq' dA= dΓ= dΔ) (ConvTyEq' dB= dΓ= dΔ) (ConvTmEq' da= dΓ= dΔ)
ConvTmEq' (InrCong dA= dB= db=) dΓ= dΔ = InrCong (ConvTyEq' dA= dΓ= dΔ) (ConvTyEq' dB= dΓ= dΔ) (ConvTmEq' db= dΓ= dΔ)
ConvTmEq' (MatchCong dA= dB= dC= dA dda= dB ddb= du) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ
                                                                  dB' = ConvTy' dB dΓ= dΔ in MatchCong (ConvTyEq' dA= dΓ= dΔ) (ConvTyEq' dB= dΓ= dΔ)
                                                                                                       (ConvTyEq' dC= (dΓ= , TyRefl (Sum dA' dB')) (dΔ , Sum dA' dB'))
                                                                                                       dA' (ConvTmEq' dda= (dΓ= , TyRefl dA') (dΔ , dA'))
                                                                                                       dB' (ConvTmEq' ddb= (dΓ= , TyRefl dB') (dΔ , dB'))
                                                                                                       (ConvTmEq' du dΓ= dΔ)
ConvTmEq' (PiUUCong da da= db=) dΓ= dΔ = let da' = ConvTm' da dΓ= dΔ in PiUUCong da' (ConvTmEq' da= dΓ= dΔ) (ConvTmEq' db= (dΓ= , TyRefl (El da')) (dΔ , El da'))
ConvTmEq' (LamCong dA dA= dB= du=) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in LamCong dA' (ConvTyEq' dA= dΓ= dΔ) (ConvTyEq' dB= (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTmEq' du= (dΓ= , TyRefl dA') (dΔ , dA'))
ConvTmEq' (AppCong dA dA= dB= df= da=) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in AppCong dA' (ConvTyEq' dA= dΓ= dΔ) (ConvTyEq' dB= (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTmEq' df= dΓ= dΔ) (ConvTmEq' da= dΓ= dΔ)
ConvTmEq' (SigUUCong da da= db=) dΓ= dΔ = let da' = ConvTm' da dΓ= dΔ in SigUUCong da' (ConvTmEq' da= dΓ= dΔ) (ConvTmEq' db= (dΓ= , TyRefl (El da')) (dΔ , El da'))
ConvTmEq' (PairCong dA dA= dB= da= db=) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in PairCong dA' (ConvTyEq' dA= dΓ= dΔ) (ConvTyEq' dB= (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTmEq' da= dΓ= dΔ) (ConvTmEq' db= dΓ= dΔ)
ConvTmEq' (Pr1Cong dA dA= dB= du=) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in Pr1Cong dA' (ConvTyEq' dA= dΓ= dΔ) (ConvTyEq' dB= (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTmEq' du= dΓ= dΔ)
ConvTmEq' (Pr2Cong dA dA= dB= du=) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in Pr2Cong dA' (ConvTyEq' dA= dΓ= dΔ) (ConvTyEq' dB= (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTmEq' du= dΓ= dΔ)
ConvTmEq' EmptyUUCong dΓ= dΔ = EmptyUUCong
ConvTmEq' (EmptyelimCong dA= du=) dΓ= dΔ = EmptyelimCong (ConvTyEq' dA= (dΓ= , EmptyCong) (dΔ , Empty)) (ConvTmEq' du= dΓ= dΔ)
ConvTmEq' UnitUUCong dΓ= dΔ = UnitUUCong
ConvTmEq' TTCong dΓ= dΔ = TTCong
ConvTmEq' (UnitelimCong dA= ddtt= du=) dΓ= dΔ = UnitelimCong (ConvTyEq' dA= (dΓ= , UnitCong) (dΔ , Unit)) (ConvTmEq' ddtt= dΓ= dΔ) (ConvTmEq' du= dΓ= dΔ)
ConvTmEq' NatUUCong dΓ= dΔ = NatUUCong
ConvTmEq' ZeroCong dΓ= dΔ = ZeroCong
ConvTmEq' (SucCong du=) dΓ= dΔ = SucCong (ConvTmEq' du= dΓ= dΔ)
ConvTmEq' (NatelimCong dP dP= ddO= ddS= du=) dΓ= dΔ = let dP' = ConvTy' dP (dΓ= , NatCong) (dΔ , Nat) in NatelimCong dP' (ConvTyEq' dP= (dΓ= , NatCong) (dΔ , Nat)) (ConvTmEq' ddO= dΓ= dΔ) (ConvTmEq' ddS= ((dΓ= , NatCong) , TyRefl dP') ((dΔ , Nat) , dP')) (ConvTmEq' du= dΓ= dΔ)
ConvTmEq' (IdUUCong da= du= dv=) dΓ= dΔ = IdUUCong (ConvTmEq' da= dΓ= dΔ) (ConvTmEq' du= dΓ= dΔ) (ConvTmEq' dv= dΓ= dΔ)
ConvTmEq' (ReflCong dA= da=) dΓ= dΔ = ReflCong (ConvTyEq' dA= dΓ= dΔ) (ConvTmEq' da= dΓ= dΔ)
ConvTmEq' (JJCong dA dA= dP= dd= da= db= dp=) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in JJCong dA' (ConvTyEq' dA= dΓ= dΔ) (ConvTyEq' dP= ((((dΓ= , TyRefl dA') , TyRefl (WeakTy dA')) , TyRefl (Id (WeakTy (WeakTy dA')) (VarPrevLast dA') (VarLast (WeakTy dA'))))) (((dΔ , dA') , WeakTy dA') , Id (WeakTy (WeakTy dA')) (VarPrevLast dA') (VarLast (WeakTy dA')))) (ConvTmEq' dd= (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTmEq' da= dΓ= dΔ) (ConvTmEq' db= dΓ= dΔ) (ConvTmEq' dp= dΓ= dΔ)

ConvTmEq' (BetaInl dA dB dC dda ddb da) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ
                                                     dB' = ConvTy' dB dΓ= dΔ in BetaInl dA' dB' (ConvTy' dC (dΓ= , TyRefl (Sum dA' dB')) (dΔ , Sum dA' dB')) (ConvTm' dda (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTm' ddb (dΓ= , TyRefl dB') (dΔ , dB')) (ConvTm' da dΓ= dΔ)
                                                     
ConvTmEq' (BetaInr dA dB dC dda ddb db) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ
                                                     dB' = ConvTy' dB dΓ= dΔ in BetaInr dA' dB' (ConvTy' dC (dΓ= , TyRefl (Sum dA' dB')) (dΔ , Sum dA' dB')) (ConvTm' dda (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTm' ddb (dΓ= , TyRefl dB') (dΔ , dB')) (ConvTm' db dΓ= dΔ) 
ConvTmEq' (BetaPi dA dB du da) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in BetaPi dA' (ConvTy' dB (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTm' du (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTm' da dΓ= dΔ)
ConvTmEq' (BetaSig1 dA dB da db) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in BetaSig1 dA' (ConvTy' dB (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTm' da dΓ= dΔ) (ConvTm' db dΓ= dΔ)
ConvTmEq' (BetaSig2 dA dB da db) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in BetaSig2 dA' (ConvTy' dB (dΓ= , TyRefl dA') (dΔ , dA')) (ConvTm' da dΓ= dΔ) (ConvTm' db dΓ= dΔ)
ConvTmEq' (BetaUnit dA ddtt) dΓ= dΔ = BetaUnit (ConvTy' dA (dΓ= , UnitCong) (dΔ , Unit)) (ConvTm' ddtt dΓ= dΔ)
ConvTmEq' (BetaNatZero dP ddO ddS) dΓ= dΔ = let dP' = ConvTy' dP (dΓ= , NatCong) (dΔ , Nat) in BetaNatZero dP' (ConvTm' ddO dΓ= dΔ) (ConvTm' ddS ((dΓ= , NatCong) , TyRefl dP') ((dΔ , Nat) , dP'))
ConvTmEq' (BetaNatSuc dP ddO ddS du) dΓ= dΔ = let dP' = ConvTy' dP (dΓ= , NatCong) (dΔ , Nat) in BetaNatSuc dP' (ConvTm' ddO dΓ= dΔ) (ConvTm' ddS ((dΓ= , NatCong) , TyRefl dP') ((dΔ , Nat) , dP')) (ConvTm' du dΓ= dΔ)
ConvTmEq' (BetaIdRefl dA dP dd da) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in
  BetaIdRefl
    dA'
    (ConvTy' dP (((dΓ= , TyRefl dA') , TyRefl (WeakTy dA')) ,
                      TyRefl (Id (WeakTy (WeakTy dA')) (VarPrevLast dA') (VarLast (WeakTy dA')))) (((dΔ , dA') , WeakTy dA') , Id (WeakTy (WeakTy dA')) (VarPrevLast dA') (VarLast (WeakTy dA'))))
    (ConvTm' dd (dΓ= , TyRefl dA') (dΔ , dA'))
    (ConvTm' da dΓ= dΔ)

ConvTmEq' (EtaSum dA dB du) dΓ= dΔ = EtaSum (ConvTy' dA dΓ= dΔ) (ConvTy' dB dΓ= dΔ) (ConvTm' du dΓ= dΔ)
ConvTmEq' (EtaPi dA dB df) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in
  EtaPi dA'
        (ConvTy' dB (dΓ= , TyRefl dA') (dΔ , dA'))
        (ConvTm' df dΓ= dΔ)
ConvTmEq' (EtaSig dA dB du) dΓ= dΔ = let dA' = ConvTy' dA dΓ= dΔ in
  EtaSig dA'
         (ConvTy' dB (dΓ= , TyRefl dA') (dΔ , dA'))
         (ConvTm' du dΓ= dΔ)

{- Subst3 -}

Subst1Tm : {Γ : Ctx n} {B : TyExpr n} {A : TyExpr (suc n)} {t : TmExpr (suc n)} {u : TmExpr n}
         → ⊢ Γ → Derivable ((Γ , B) ⊢ t :> A) → Derivable (Γ ⊢ u :> B)
         → Derivable (Γ ⊢ substTm t u :> substTy A u)
Subst1Tm dΓ dt du = SubstTm dt (idMorDerivable dΓ , congTmTy! ([idMor]Ty _) du)

Subst2Ty : {Γ : Ctx n} {B : TyExpr n} {C : TyExpr (suc n)} {D : TyExpr (suc (suc n))} {u v : TmExpr n}
         → ⊢ Γ → Derivable ((((Γ , B) , C)) ⊢ D) → Derivable (Γ ⊢ u :> B) → Derivable (Γ ⊢ v :> substTy C u) → Derivable (Γ ⊢ subst2Ty D u v)
Subst2Ty dΓ dA du dv = SubstTy dA ((idMorDerivable dΓ , congTmTy! ([idMor]Ty _) du) , dv)

Subst3Ty : {Γ : Ctx n} {B : TyExpr n} {C : TyExpr (suc n)} {D : TyExpr (suc (suc n))} {A : TyExpr (suc (suc (suc n)))} {u v w : TmExpr n}
         → ⊢ Γ → Derivable ((((Γ , B) , C) , D) ⊢ A) → Derivable (Γ ⊢ u :> B) → Derivable (Γ ⊢ v :> substTy C u) → Derivable (Γ ⊢ w :> subst2Ty D u v)
         → Derivable (Γ ⊢ subst3Ty A u v w)
Subst3Ty dΓ dA du dv dw = SubstTy dA (((idMorDerivable dΓ , congTmTy! ([idMor]Ty _) du) , dv) , dw)

Subst3TyEq : {Γ : Ctx n} {B : TyExpr n} {C : TyExpr (suc n)} {D : TyExpr (suc (suc n))} {A A' : TyExpr (suc (suc (suc n)))} {u u' v v' w w' : TmExpr n}
           → ⊢ Γ → Derivable ((((Γ , B) , C) , D) ⊢ A') → Derivable (Γ ⊢ u :> B) → Derivable (Γ ⊢ v :> substTy C u) → Derivable (Γ ⊢ w :> subst2Ty D u v)
           → Derivable ((((Γ , B) , C) , D) ⊢ A == A') → Derivable (Γ ⊢ u == u' :> B) → Derivable (Γ ⊢ v == v' :> substTy C u) → Derivable (Γ ⊢ w == w' :> subst2Ty D u v)
           → Derivable (Γ ⊢ subst3Ty A u v w == subst3Ty A' u' v' w')
Subst3TyEq dΓ dA' du dv dw dA= du= dv= dw= = SubstTyFullEq dA' (((idMorDerivable dΓ , congTmTy! ([idMor]Ty _) du) , dv) , dw) dA= (((MorRefl (idMorDerivable dΓ) , congTmEqTy! ([idMor]Ty _) du=) , dv=) , dw=)

{- Various other admissible rules -}


ConvTm2' : {Γ Δ : Ctx n} {u : TmExpr n} {A A' : TyExpr n} → Derivable (Δ ⊢ u :> A) → (⊢ Γ == Δ) → ⊢ Γ → Derivable (Δ ⊢ A) → Derivable (Δ ⊢ A == A') → Derivable (Γ ⊢ u :> A')
ConvTm2' du dΓ= dΔ dA dA= = Conv (ConvTy' dA dΓ= dΔ) (ConvTm' du dΓ= dΔ) (ConvTyEq' dA= dΓ= dΔ)

TyEqTy1 : {Γ : Ctx n} {A B : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ A)
TyEqTy2 : {Γ : Ctx n} {A B : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B)
TmEqTm1 : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u :> A)
TmEqTm2 : {Γ : Ctx n} {u u' : TmExpr n} {A : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u == u' :> A) → Derivable (Γ ⊢ u' :> A)

CtxEqCtx1 : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' → ⊢ Γ
CtxEqCtx2 : {Γ Γ' : Ctx n} → ⊢ Γ == Γ' → ⊢ Γ'
CtxSymm : {Γ Δ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Γ

CtxEqCtx1 tt = tt
CtxEqCtx1 (dΓ= , dA=) = (CtxEqCtx1 dΓ= , TyEqTy1 (CtxEqCtx1 dΓ=) (ConvTyEq' dA= (CtxRefl (CtxEqCtx1 dΓ=)) (CtxEqCtx1 dΓ=)))

CtxEqCtx2 tt = tt
CtxEqCtx2 (dΓ= , dA=) = (CtxEqCtx2 dΓ= , ConvTy' (TyEqTy2 (CtxEqCtx1 dΓ=) dA=) (CtxSymm dΓ=) (CtxEqCtx2 dΓ=)) -- TyEqTy2 (CtxEqCtx2 dΓ=) (ConvTyEq' dA= dΓ=))

CtxSymm tt = tt
CtxSymm (dΓ= , dA=) = (CtxSymm dΓ= , ConvTyEq' (TySymm dA=) (CtxSymm dΓ=) (CtxEqCtx2 dΓ=))

CtxTran : {Γ Δ Θ : Ctx n} → ⊢ Γ == Δ → ⊢ Δ == Θ → ⊢ Γ == Θ
CtxTran tt tt = tt
CtxTran (dΓ= , dA=) (dΔ= , dB=) =
  (CtxTran dΓ= dΔ= , TyTran (ConvTy' (TyEqTy2 (CtxEqCtx1 dΓ=) dA=) (CtxRefl (CtxEqCtx1 dΓ=)) (CtxEqCtx1 dΓ=)) dA= (TySymm (ConvTyEq' (TySymm dB=) dΓ= (CtxEqCtx1 dΓ=)))) --TyTran ? {!(ConvTyEq' dA= dΔ= (CtxEqCtx2 dΔ=))!} dB=)

TyEqTy1 dΓ (TyRefl dA) = dA
TyEqTy1 dΓ (TySymm dA=) = TyEqTy2 dΓ dA=
TyEqTy1 dΓ (TyTran _ dA= dB=) = TyEqTy1 dΓ dA=
TyEqTy1 dΓ UUCong = UU
TyEqTy1 dΓ (ElCong dv=) = El (TmEqTm1 dΓ dv=)
TyEqTy1 dΓ (SumCong dA= dB=) = Sum (TyEqTy1 dΓ dA=) (TyEqTy1 dΓ dB=)
TyEqTy1 dΓ (PiCong dA dA= dB=) = Pi dA (TyEqTy1 (dΓ , dA) dB=)
TyEqTy1 dΓ (SigCong dA dA= dB=) = Sig dA (TyEqTy1 (dΓ , dA) dB=)
TyEqTy1 dΓ EmptyCong = Empty
TyEqTy1 dΓ UnitCong = Unit
TyEqTy1 dΓ NatCong = Nat
TyEqTy1 dΓ (IdCong dA= da= db=) = Id (TyEqTy1 dΓ dA=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)
TyEqTy1 dΓ ElUU= = El UUUU
TyEqTy1 dΓ (ElSum= da db) = El (SumUU da db)
TyEqTy1 dΓ (ElPi= da db) = El (PiUU da db)
TyEqTy1 dΓ (ElSig= da db) = El (SigUU da db)
TyEqTy1 dΓ ElEmpty= = El EmptyUU
TyEqTy1 dΓ ElUnit= = El UnitUU
TyEqTy1 dΓ ElNat= = El NatUU
TyEqTy1 dΓ (ElId= da du dv) = El (IdUU da du dv)


TyEqTy2 dΓ (TyRefl dA) = dA
TyEqTy2 dΓ (TySymm dA=) = TyEqTy1 dΓ dA=
TyEqTy2 dΓ (TyTran dB dA= dB=) = TyEqTy2 dΓ dB=
TyEqTy2 dΓ UUCong = UU
TyEqTy2 dΓ (ElCong dv=) = El (TmEqTm2 dΓ dv=)
TyEqTy2 dΓ (SumCong dA= dB=) = Sum (TyEqTy2 dΓ dA=) (TyEqTy2 dΓ dB=)
TyEqTy2 dΓ (PiCong dA dA= dB=) = Pi (TyEqTy2 dΓ dA=) (ConvTy' (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=))
TyEqTy2 dΓ (SigCong dA dA= dB=) = Sig (TyEqTy2 dΓ dA=) (ConvTy' (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=))
TyEqTy2 dΓ EmptyCong = Empty
TyEqTy2 dΓ UnitCong = Unit
TyEqTy2 dΓ NatCong = Nat
TyEqTy2 dΓ (IdCong dA= da= db=) = Id (TyEqTy2 dΓ dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ da=) dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ db=) dA=)
TyEqTy2 dΓ ElUU= = UU
TyEqTy2 dΓ (ElSum= da db) = Sum (El da) (El db)
TyEqTy2 dΓ (ElPi= da db) = Pi (El da) (El db)
TyEqTy2 dΓ (ElSig= da db) = Sig (El da) (El db)
TyEqTy2 dΓ ElEmpty= = Empty
TyEqTy2 dΓ ElUnit= = Unit
TyEqTy2 dΓ ElNat= = Nat
TyEqTy2 dΓ (ElId= da du dv) = Id (El da) du dv

TmEqTm1 dΓ (TmRefl du) = du
TmEqTm1 dΓ (TmSymm du=) = TmEqTm2 dΓ du= 
TmEqTm1 dΓ (TmTran _ du= dv=) = TmEqTm1 dΓ du=
TmEqTm1 dΓ (ConvEq dA du= dA=) = Conv dA (TmEqTm1 dΓ du=) dA=
TmEqTm1 dΓ UUUUCong = UUUU
TmEqTm1 dΓ (SumUUCong da= db=) = SumUU (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)
TmEqTm1 dΓ (InlCong dA= dB= da=) = Inl (TyEqTy1 dΓ dA=) (TyEqTy1 dΓ dB=) (TmEqTm1 dΓ da=)
TmEqTm1 dΓ (InrCong dA= dB= db=) = Inr (TyEqTy1 dΓ dA=) (TyEqTy1 dΓ dB=) (TmEqTm1 dΓ db=)
TmEqTm1 dΓ (MatchCong dA= dB= dC= dA dda= dB ddb= du=) = Match dA dB (TyEqTy1 (dΓ , Sum dA dB) dC=) (TmEqTm1 (dΓ , dA) dda=) (TmEqTm1 (dΓ , dB) ddb=) (TmEqTm1 dΓ du=)
TmEqTm1 dΓ (PiUUCong da da= db=) = PiUU da (TmEqTm1 (dΓ , El da) db=)
TmEqTm1 dΓ (LamCong dA dA= dB= du=) = Lam (TyEqTy1 dΓ dA=) (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 (dΓ , dA) du=)
TmEqTm1 dΓ (AppCong dA dA= dB= df= da=) = App (TyEqTy1 dΓ dA=) (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 dΓ df=) (TmEqTm1 dΓ da=)
TmEqTm1 dΓ (SigUUCong da da= db=) = SigUU da (TmEqTm1 (dΓ , El da) db=)
TmEqTm1 dΓ (PairCong dA dA= dB= da= db=) = Pair dA (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)
TmEqTm1 dΓ (Pr1Cong dA dA= dB= du=) = Pr1 dA (TyEqTy1  (dΓ , dA) dB=) (TmEqTm1 dΓ du=)
TmEqTm1 dΓ (Pr2Cong dA dA= dB= du=) = Pr2 dA (TyEqTy1 (dΓ , dA) dB=) (TmEqTm1 dΓ du=)
TmEqTm1 dΓ EmptyUUCong = EmptyUU
TmEqTm1 dΓ (EmptyelimCong dA= du=) = Emptyelim (TyEqTy1 (dΓ , Empty) dA=) (TmEqTm1 dΓ du=)
TmEqTm1 dΓ UnitUUCong = UnitUU
TmEqTm1 dΓ TTCong = TT
TmEqTm1 dΓ (UnitelimCong dA= ddtt= du=) = Unitelim (TyEqTy1 (dΓ , Unit) dA=) (TmEqTm1 dΓ ddtt=) (TmEqTm1 dΓ du=)
TmEqTm1 dΓ NatUUCong = NatUU
TmEqTm1 dΓ ZeroCong = Zero
TmEqTm1 dΓ (SucCong du=) = Suc (TmEqTm1 dΓ du=)
TmEqTm1 dΓ (NatelimCong dP dP= ddO= ddS= du=) = Natelim (TyEqTy1 (dΓ , Nat) dP=) (TmEqTm1 dΓ ddO=) (TmEqTm1 ((dΓ , Nat) , dP) ddS=) (TmEqTm1 dΓ du=)
TmEqTm1 dΓ (IdUUCong da= du= dv=) = IdUU (TmEqTm1 dΓ da=) (TmEqTm1 dΓ du=) (TmEqTm1 dΓ dv=)
TmEqTm1 dΓ (ReflCong dA= da=) = Refl (TyEqTy1 dΓ dA=) (TmEqTm1 dΓ da=)
TmEqTm1 dΓ (JJCong dA dA= dP= dd= da= db= dp=) = JJ dA (TyEqTy1 (((dΓ , dA) , (WeakTy dA)) , (Id (WeakTy (WeakTy dA)) (VarPrevLast dA) (VarLast (WeakTy dA)))) dP=) (TmEqTm1 (dΓ , dA) dd=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=) (TmEqTm1 dΓ dp=)

TmEqTm1 dΓ (BetaInl dA dB dC dda ddb da) = Match dA dB dC dda ddb (Inl dA dB da)
TmEqTm1 dΓ (BetaInr dA dB dC dda ddb db) = Match dA dB dC dda ddb (Inr dA dB db)
TmEqTm1 dΓ (BetaPi dA dB du da) = App dA dB (Lam dA dB du) da
TmEqTm1 dΓ (BetaSig1 dA dB da db) = Pr1 dA dB (Pair dA dB da db)
TmEqTm1 dΓ (BetaSig2 {B = B} dA dB da db) = Conv (SubstTy dB (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (Pr1 dA dB (Pair dA dB da db)))) (Pr2 dA dB (Pair dA dB da db)) (SubstTyMorEq dB (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (Pr1 dA dB (Pair dA dB da db))) (MorRefl (idMorDerivable dΓ) , congTmEqTy! ([idMor]Ty _) (BetaSig1 dA dB da db)))
TmEqTm1 dΓ (BetaUnit dA ddtt) = Unitelim dA ddtt TT
TmEqTm1 dΓ (BetaNatZero dP ddO ddS) = Natelim dP ddO ddS Zero
TmEqTm1 dΓ (BetaNatSuc dP ddO ddS du) = Natelim dP ddO ddS (Suc du)
TmEqTm1 dΓ (BetaIdRefl dA dP dd da) = JJ dA dP dd da da (Refl dA da)

TmEqTm1 dΓ (EtaSum dA dB du) = du
TmEqTm1 dΓ (EtaPi dA dB df) = df
TmEqTm1 dΓ (EtaSig dA dB du) = du

TmEqTm2 dΓ (TmRefl du) = du
TmEqTm2 dΓ (TmSymm du=) = TmEqTm1 dΓ du=
TmEqTm2 dΓ (TmTran _ du= dv=) = TmEqTm2 dΓ dv=
TmEqTm2 dΓ (ConvEq dA du= dA=) = Conv dA (TmEqTm2 dΓ du=) dA=
TmEqTm2 dΓ UUUUCong = UUUU
TmEqTm2 dΓ (SumUUCong da= db=) = SumUU (TmEqTm2 dΓ da=) (TmEqTm2 dΓ db=)
TmEqTm2 dΓ (InlCong dA= dB= da=) = Conv (Sum (TyEqTy2 dΓ dA=) (TyEqTy2 dΓ dB=)) (Inl (TyEqTy2 dΓ dA=) (TyEqTy2 dΓ dB=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ da=) dA=)) (SumCong (TySymm dA=) (TySymm dB=))
TmEqTm2 dΓ (InrCong dA= dB= db=) = Conv (Sum (TyEqTy2 dΓ dA=) (TyEqTy2 dΓ dB=)) (Inr (TyEqTy2 dΓ dA=) (TyEqTy2 dΓ dB=) (Conv (TyEqTy1 dΓ dB=) (TmEqTm2 dΓ db=) dB=)) (SumCong (TySymm dA=) (TySymm dB=))
TmEqTm2 dΓ (MatchCong dA= dB= dC= dA dda= dB ddb= du=) =
                      Conv (SubstTy (TyEqTy2 (dΓ , Sum (TyEqTy1 dΓ dA=) (TyEqTy1 dΓ dB=)) dC=) (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl (TmEqTm2 dΓ du=)))
                           (Match (TyEqTy2 dΓ dA=) (TyEqTy2 dΓ dB=)
                                  (ConvTy' (TyEqTy2 (dΓ , Sum (TyEqTy1 dΓ dA=) (TyEqTy1 dΓ dB=)) dC=) (CtxRefl dΓ , SumCong (TySymm dA=) (TySymm dB=)) (dΓ , Sum (TyEqTy2 dΓ dA=) (TyEqTy2 dΓ dB=)))
                                  (ConvTm' (Conv (SubstTy (WeakTy (TyEqTy1 (dΓ , Sum (TyEqTy1 dΓ dA=) (TyEqTy1 dΓ dB=)) dC=))
                                                          (idMorDerivable (dΓ , TyEqTy1 dΓ dA=)
                                                          , congTm! ([idMor]Ty _) refl (Inl (WeakTy (TyEqTy1 dΓ dA=)) (WeakTy (TyEqTy1 dΓ dB=)) (VarLast (TyEqTy1 dΓ dA=)))))
                                                 (TmEqTm2 (dΓ , TyEqTy1 dΓ dA=) dda=)
                                                 (SubstTyFullEq (WeakTy (TyEqTy2 (dΓ , Sum (TyEqTy1 dΓ dA=) (TyEqTy1 dΓ dB=)) dC=)) (idMorDerivable (dΓ , TyEqTy1 dΓ dA=) , congTm! ([idMor]Ty _) refl (Inl (WeakTy (TyEqTy1 dΓ dA=)) (WeakTy (TyEqTy1 dΓ dB=)) (VarLast (TyEqTy1 dΓ dA=)))) (WeakTyEq dC=) (MorRefl (idMorDerivable (dΓ , TyEqTy1 dΓ dA=)) , congTmEqTy! ([idMor]Ty _) (InlCong (WeakTyEq dA=) (WeakTyEq dB=) (TmRefl (VarLast (TyEqTy1 dΓ dA=)))))))
                                           (CtxRefl dΓ , TySymm dA=)
                                           (dΓ , TyEqTy2 dΓ dA=))
                                  (ConvTm' (Conv (SubstTy (WeakTy (TyEqTy1 (dΓ , Sum (TyEqTy1 dΓ dA=) (TyEqTy1 dΓ dB=)) dC=))
                                                          (idMorDerivable (dΓ , TyEqTy1 dΓ dB=)
                                                          , congTm! ([idMor]Ty _) refl (Inr (WeakTy (TyEqTy1 dΓ dA=)) (WeakTy (TyEqTy1 dΓ dB=)) (VarLast (TyEqTy1 dΓ dB=)))))
                                                 (TmEqTm2 (dΓ , TyEqTy1 dΓ dB=) ddb=)
                                                 (SubstTyFullEq (WeakTy (TyEqTy2 (dΓ , Sum (TyEqTy1 dΓ dA=) (TyEqTy1 dΓ dB=)) dC=))
                                                                (idMorDerivable (dΓ , TyEqTy1 dΓ dB=)
                                                                , congTm! ([idMor]Ty _) refl (Inr (WeakTy (TyEqTy1 dΓ dA=)) (WeakTy (TyEqTy1 dΓ dB=)) (VarLast (TyEqTy1 dΓ dB=))))
                                                                (WeakTyEq dC=)
                                                                (MorRefl (idMorDerivable (dΓ , TyEqTy1 dΓ dB=))
                                                                , congTmEqTy! ([idMor]Ty _) (InrCong (WeakTyEq dA=) (WeakTyEq dB=) (VarLastCong (TyEqTy1 dΓ dB=))))))
                                           (CtxRefl dΓ , TySymm dB=)
                                           (dΓ , TyEqTy2 dΓ dB=))
                                  (Conv (Sum (TyEqTy1 dΓ dA=) (TyEqTy1 dΓ dB=)) (TmEqTm2 dΓ du=) (SumCong dA= dB=)))
                           (SubstTyFullEq (TyEqTy1 (dΓ , Sum (TyEqTy1 dΓ dA=) (TyEqTy1 dΓ dB=)) dC=)
                                          (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl (TmEqTm2 dΓ du=))
                                          (TySymm dC=)
                                          (MorRefl (idMorDerivable dΓ) , congTmEqTy (! ([idMor]Ty _)) (TmSymm du=)))
TmEqTm2 dΓ (PiUUCong da da= db=) = PiUU (TmEqTm2 dΓ da=) (ConvTm' (TmEqTm2 (dΓ , El da) db=) (CtxRefl dΓ , TySymm (ElCong da=)) (dΓ , El (TmEqTm2 dΓ da=)))
TmEqTm2 dΓ (LamCong dA dA= dB= du=) = 
  Conv (Pi (TyEqTy2 dΓ dA=)
           (ConvTy' (TyEqTy2 (dΓ , (TyEqTy1 dΓ dA=)) dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=)))
       (Lam (TyEqTy2 dΓ dA=)
            (ConvTy' (TyEqTy2 (dΓ , TyEqTy1 dΓ dA=) dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=))
            (ConvTm' (Conv (TyEqTy1 (dΓ , dA) dB=) (TmEqTm2 (dΓ , dA) du=) dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=)))
       (PiCong (TyEqTy2 dΓ dA=)
               (TySymm dA=)
               (ConvTyEq' (TySymm dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=)))
TmEqTm2 dΓ (AppCong dA dA= dB= df= da=) =
  Conv (SubstTy (TyEqTy2 (dΓ , dA) dB=) (idMorDerivable dΓ , Conv dA (TmEqTm2 dΓ da=) (congTyEq! refl ([idMor]Ty _) (TyRefl dA))))
       (App (TyEqTy2 dΓ dA=)
            (ConvTy' (TyEqTy2 (dΓ , TyEqTy1 dΓ dA=) dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=))
            (Conv (Pi dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ df=) (PiCong dA dA= dB=))
            (Conv dA (TmEqTm2 dΓ da=) dA=))
       (TySymm (SubstTyFullEq (TyEqTy2 (dΓ , dA) dB=)
                              (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (TmEqTm1 dΓ da=))
                              dB=
                              (MorRefl (idMorDerivable dΓ) , congTmEqTy! ([idMor]Ty _) da=)))
TmEqTm2 dΓ (SigUUCong da da= db=) = SigUU (TmEqTm2 dΓ da=) (ConvTm' (TmEqTm2 (dΓ , El da) db=) (CtxRefl dΓ , TySymm (ElCong da=)) (dΓ , El (TmEqTm2 dΓ da=)))
TmEqTm2 dΓ (PairCong dA dA= dB= da= db=) =
  Conv (Sig (TyEqTy2 dΓ dA=)
            (ConvTy' (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=)))
       (Pair (TyEqTy2 dΓ dA=)
             (ConvTy' (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=))
             (Conv dA (TmEqTm2 dΓ da=) dA=)
             (Conv (SubstTy (TyEqTy1 (dΓ , dA) dB=) (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (TmEqTm1 dΓ da=)))
                   (TmEqTm2 dΓ db=)
                   (SubstTyFullEq (TyEqTy2 (dΓ , dA) dB=)
                                  (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (TmEqTm1 dΓ da=))
                                  dB=
                                  (MorRefl (idMorDerivable dΓ) , congTmEqTy! ([idMor]Ty _) da=))))
       (SigCong (TyEqTy2 dΓ dA=)
                (TySymm dA=)
                (ConvTyEq' (TySymm dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=)))
TmEqTm2 dΓ (Pr1Cong dA dA= dB= du=) =
  Conv (TyEqTy2 dΓ dA=)
       (Pr1 (TyEqTy2 dΓ dA=)
            (ConvTy' (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=))
            (Conv (Sig dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ du=) (SigCong dA dA= dB=)))
       (TySymm dA=)
TmEqTm2 dΓ (Pr2Cong dA dA= dB= du=) =
  Conv (SubstTy (TyEqTy2 (dΓ , dA) dB=)
                (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (Conv (TyEqTy2 dΓ dA=)
                                                                      (Pr1 (TyEqTy2 dΓ dA=)
                                                                           (ConvTy' (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=))
                                                                           (Conv (Sig dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ du=) (SigCong dA dA= dB=)))
                                                                      (TySymm dA=))))
       (Pr2 (TyEqTy2 dΓ dA=)
            (ConvTy' (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=))
            (Conv (Sig dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ du=) (SigCong dA dA= dB=)))
       (SubstTyFullEq (TyEqTy1 (dΓ , dA) dB=)
                      (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl (Conv (TyEqTy2 dΓ dA=)
                                                                            (Pr1 (TyEqTy2 dΓ dA=)
                                                                                 (ConvTy' (TyEqTy2 (dΓ , dA) dB=) (CtxRefl dΓ , TySymm dA=) (dΓ , TyEqTy2 dΓ dA=))
                                                                                 (Conv (Sig dA (TyEqTy1 (dΓ , dA) dB=)) (TmEqTm2 dΓ du=) (SigCong dA dA= dB=)))
                                                                            (TySymm dA=)))
                      (TySymm dB=)
                      (MorRefl (idMorDerivable dΓ) , TmSymm (congTmEqTy! ([idMor]Ty _) (Pr1Cong dA dA= dB= du=))))
TmEqTm2 dΓ EmptyUUCong = EmptyUU
TmEqTm2 dΓ (EmptyelimCong dA= du=) = Conv (SubstTy (TyEqTy2 (dΓ , Empty) dA=) (idMorDerivable dΓ , TmEqTm2 dΓ du=)) (Emptyelim (TyEqTy2 (dΓ , Empty) dA=) (TmEqTm2 dΓ du=)) (SubstTyFullEq (TyEqTy1 (dΓ , Empty) dA=) (idMorDerivable dΓ , TmEqTm2 dΓ du=) (TySymm dA=) (MorRefl (idMorDerivable dΓ) , TmSymm du=))
TmEqTm2 dΓ UnitUUCong = UnitUU
TmEqTm2 dΓ TTCong = TT
TmEqTm2 dΓ (UnitelimCong dA= ddtt= du=) = Conv (SubstTy (TyEqTy2 (dΓ , Unit) dA=)
                                               (idMorDerivable dΓ , TmEqTm2 dΓ du=))
                                               (Unitelim (TyEqTy2 (dΓ , Unit) dA=) (Conv (SubstTy (TyEqTy1 (dΓ , Unit) dA=) (idMorDerivable dΓ , TT)) (TmEqTm2 dΓ ddtt=) (SubstTyEq dA= (idMorDerivable dΓ , TT))) (TmEqTm2 dΓ du=)) (SubstTyFullEq (TyEqTy1 (dΓ , Unit) dA=) (idMorDerivable dΓ , TmEqTm2 dΓ du=) (TySymm dA=) (MorRefl (idMorDerivable dΓ) , TmSymm du=))
TmEqTm2 dΓ NatUUCong = NatUU
TmEqTm2 dΓ ZeroCong = Zero
TmEqTm2 dΓ (SucCong du=) = Suc (TmEqTm2 dΓ du=)
TmEqTm2 dΓ (NatelimCong dP dP= ddO= ddS= du=) =
  let dP' = TyEqTy2 (dΓ , Nat) dP=
      ddO' = Conv (SubstTy dP (idMorDerivable dΓ , Zero)) (TmEqTm2 dΓ ddO=) (SubstTyEq dP= (idMorDerivable dΓ , Zero))
      ddS' = ConvTm2' (TmEqTm2 ((dΓ , Nat) , dP) ddS=)
                      (CtxRefl (dΓ , Nat) , TySymm dP=)
                      ((dΓ , Nat) , dP')
                      (SubstTy (WeakTy (WeakTy dP)) (idMorDerivable ((dΓ , Nat) , dP) , Suc (VarPrevLast Nat))) 
                      (SubstTyEq (WeakTyEq (WeakTyEq dP=)) (idMorDerivable ((dΓ , Nat) , dP) , Suc (VarPrevLast Nat))) 
      du' = TmEqTm2 dΓ du= in
  Conv (SubstTy dP' (idMorDerivable dΓ , du'))
       (Natelim dP' ddO' ddS' du')
       (TySymm (SubstTyFullEq dP' (idMorDerivable dΓ , TmEqTm1 dΓ du=) dP= (MorRefl (idMorDerivable dΓ) , du=)))
TmEqTm2 dΓ (IdUUCong da= du= dv=) = IdUU (TmEqTm2 dΓ da=) (Conv (El (TmEqTm1 dΓ da=)) (TmEqTm2 dΓ du=) (ElCong da=)) (Conv (El (TmEqTm1 dΓ da=)) (TmEqTm2 dΓ dv=) (ElCong da=))
TmEqTm2 dΓ (ReflCong dA= da=) =
  Conv (Id (TyEqTy2 dΓ dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ da=) dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ da=) dA=))
       (Refl (TyEqTy2 dΓ dA=) (Conv (TyEqTy1 dΓ dA=) (TmEqTm2 dΓ da=) dA=))
       (IdCong (TySymm dA=) (ConvEq (TyEqTy1 dΓ dA=) (TmSymm da=) dA=) (ConvEq (TyEqTy1 dΓ dA=) (TmSymm da=) dA=))
TmEqTm2 dΓ (JJCong dA dA= dP= dd= da= db= dp=) =
  let dA' = TyEqTy2 dΓ dA=
      dP' = ConvTy' (TyEqTy2 (((dΓ , dA) , WeakTy dA) , Id (WeakTy (WeakTy dA)) (VarPrevLast dA) (VarLast (WeakTy dA))) dP=)
                   (((CtxRefl dΓ , TySymm dA=) , TySymm (WeakTyEq dA=)) ,
                      TySymm (IdCong (WeakTyEq (WeakTyEq dA=)) (TmRefl (Conv (WeakTy (WeakTy dA')) (VarPrevLast dA') (WeakTyEq (WeakTyEq (TySymm dA=)))))
                             (ConvTmEq' (VarLastCong (WeakTy dA)) ((CtxRefl dΓ , TySymm dA=) , TySymm (WeakTyEq dA=)) ((dΓ , TyEqTy2 dΓ dA=) , WeakTy dA'))))
                   (((dΓ , dA') , WeakTy dA') , Id (WeakTy (WeakTy dA')) (VarPrevLast dA') (VarLast (WeakTy dA')))
      dd' = ConvTm2' (TmEqTm2 (dΓ , dA) dd=)
                     (CtxRefl dΓ , TySymm dA=)
                     (dΓ , TyEqTy2 dΓ dA=)
                     (Subst3Ty (dΓ , dA)
                               (WeakTy (TyEqTy1 (((dΓ , dA) , WeakTy dA) , Id (WeakTy (WeakTy dA)) (VarPrevLast dA) (VarLast (WeakTy dA))) dP=))
                               (VarLast dA)
                               (congTmTy! (ap-substTy weakenTy-weakenTy refl ∙ substTy-weakenTy) (VarLast dA))
                               (congTmTy! (ap-id-Ty (substTy-weakenTy' ∙ substTy-weakenTy' ∙ [idMor]Ty _) refl refl) (Refl (WeakTy dA) (VarLast dA))))
                     (Subst3TyEq (dΓ , dA)
                                 (WeakTy (TyEqTy2 (((dΓ , dA) , WeakTy dA) , Id (WeakTy (WeakTy dA)) (VarPrevLast dA) (VarLast (WeakTy dA))) dP=))
                                 (VarLast dA)
                                 (congTmTy! (ap-substTy weakenTy-weakenTy refl ∙ substTy-weakenTy) (VarLast dA))
                                 (congTmTy! (ap-id-Ty (substTy-weakenTy' ∙ substTy-weakenTy' ∙ [idMor]Ty _) refl refl) (Refl (WeakTy dA) (VarLast dA)))
                                 (WeakTyEq dP=)
                                 (VarLastCong dA)
                                 (congTmEqTy! (ap-substTy weakenTy-weakenTy refl ∙ substTy-weakenTy) (VarLastCong dA))
                                 (congTmEqTy! (ap-id-Ty (substTy-weakenTy' ∙ substTy-weakenTy' ∙ [idMor]Ty _) refl refl) (ReflCong (WeakTyEq dA=) (VarLastCong dA))))
      da' = Conv dA (TmEqTm2 dΓ da=) dA=
      db' = Conv dA (TmEqTm2 dΓ db=) dA=
      dp' = Conv (Id dA (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)) (TmEqTm2 dΓ dp=) (IdCong dA= da= db=) in         
  Conv (Subst3Ty dΓ dP' da' (congTmTy! substTy-weakenTy db') (congTmTy! (ap-id-Ty subst2Ty-weakenTy refl refl) dp'))
       (JJ dA' dP' dd' da' db' dp')
       (Subst3TyEq dΓ
                   (TyEqTy1 (((dΓ , dA) , (WeakTy dA)) , (Id (WeakTy (WeakTy dA)) (VarPrevLast dA) (VarLast (WeakTy dA)))) dP=)
                   (TmEqTm2 dΓ da=)
                   (congTmTy! substTy-weakenTy (TmEqTm2 dΓ db=))
                   (Conv (Id (TyEqTy1 dΓ dA=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)) (TmEqTm2 dΓ dp=) (IdCong (congTyRefl dA (! subst2Ty-weakenTy)) da= db=))
                   (TySymm dP=)
                   (TmSymm da=)
                   (congTmEqTy! substTy-weakenTy (TmSymm db=))
                   (ConvEq (Id (TyEqTy1 dΓ dA=) (TmEqTm1 dΓ da=) (TmEqTm1 dΓ db=)) (TmSymm dp=) (IdCong (congTyRefl dA (! subst2Ty-weakenTy)) da= db=)))

TmEqTm2 dΓ (BetaInl dA dB dC dda ddb da) = congTmTy ([]Ty-substTy ∙ ap-substTy (weakenTyInsert' _ _ _ (weakenTm _) ∙ [idMor]Ty _) (ap-inl-Tm substTy-weakenTy substTy-weakenTy refl)) (SubstTm dda (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl da))
TmEqTm2 dΓ (BetaInr dA dB dC dda ddb db) = congTmTy ([]Ty-substTy ∙ ap-substTy (weakenTyInsert' _ _ _ (weakenTm _) ∙ [idMor]Ty _) (ap-inr-Tm substTy-weakenTy substTy-weakenTy refl)) (SubstTm ddb (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl db))
TmEqTm2 dΓ (BetaPi dA dB du da) = SubstTm du (idMorDerivable dΓ , congTm! ([idMor]Ty _) refl da)
TmEqTm2 dΓ (BetaSig1 dA dB da db) = da
TmEqTm2 dΓ (BetaSig2 dA dB da db) = db
TmEqTm2 dΓ (BetaUnit dA ddtt) = ddtt
TmEqTm2 dΓ (BetaNatZero dP ddO ddS) = ddO
TmEqTm2 dΓ (BetaNatSuc dP ddO ddS du) =
  Conv (SubstTy (SubstTy (WeakTy (WeakTy dP)) (idMorDerivable ((dΓ , Nat) , dP) , Suc (VarPrevLast Nat))) ((idMorDerivable dΓ , du) , Natelim dP ddO ddS du))
       (SubstTm ddS ((idMorDerivable dΓ , du) , Natelim dP ddO ddS du))
       (congTyRefl' (SubstTy dP (idMorDerivable dΓ , Suc du)) subst2Ty-substTy)  
TmEqTm2 dΓ (BetaIdRefl dA dP dd da) = congTmTy (substTy-subst3Ty ∙ ap-subst3Ty refl refl refl (ap-refl-Tm substTy-weakenTy refl)) (Subst1Tm dΓ dd da)

TmEqTm2 dΓ (EtaSum dA dB du) = congTmTy substTy-weakenTy (Match dA dB (WeakTy (Sum dA dB)) (congTmTy! (ap-substTy weakenTy-weakenTy refl ∙ substTy-weakenTy) (Inl (WeakTy dA) (WeakTy dB) (VarLast dA))) (congTmTy! (ap-substTy weakenTy-weakenTy refl ∙ substTy-weakenTy) (Inr (WeakTy dA) (WeakTy dB) (VarLast dB))) du)
TmEqTm2 dΓ (EtaPi dA dB df) = Lam dA dB (congTmTy (substTy-weakenTy' ∙ [idMor]Ty _) (App (WeakTy dA) (WeakTy dB) (WeakTm df) (VarLast dA)))
TmEqTm2 dΓ (EtaSig dA dB du) = Pair dA dB (Pr1 dA dB du) (Pr2 dA dB du)

MorEqMor1 : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → (⊢ Γ) → (⊢ Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ δ ∷> Δ)
MorEqMor2 : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → (⊢ Γ) → (⊢ Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ δ' ∷> Δ)

MorEqMor1 _ _ tt = tt
MorEqMor1 dΓ (dΔ , _) (dδ= , du=) = (MorEqMor1 dΓ dΔ dδ= , TmEqTm1 dΓ du=)

MorEqMor2 _ _ tt = tt
MorEqMor2 dΓ (dΔ , dB) (dδ= , du=) = (MorEqMor2 dΓ dΔ dδ= , Conv (SubstTy dB (MorEqMor1 dΓ dΔ dδ=)) (TmEqTm2 dΓ du=) (SubstTyMorEq dB (MorEqMor1 dΓ dΔ dδ=) dδ=))


MorSymm : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} → ⊢ Γ → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ ∷> Δ
MorSymm _ _ tt = tt
MorSymm dΓ (dΔ , dB) (dδ , du) = (MorSymm dΓ dΔ dδ , ConvEq (SubstTy dB (MorEqMor1 dΓ dΔ dδ)) (TmSymm du) (SubstTyMorEq dB (MorEqMor1 dΓ dΔ dδ) dδ))

MorTran : {Γ : Ctx n} {Δ : Ctx m} {δ δ' δ'' : Mor n m} → ⊢ Γ → ⊢ Δ → Γ ⊢ δ == δ' ∷> Δ → Γ ⊢ δ' == δ'' ∷> Δ → Γ ⊢ δ == δ'' ∷> Δ
MorTran _ _ tt tt = tt
MorTran dΓ (dΔ , dB) (dδ , du) (dδ' , du') =
  (MorTran dΓ dΔ dδ dδ' , TmTran (TmEqTm2 dΓ du) du (ConvEq (SubstTy dB (MorEqMor2 dΓ dΔ dδ)) du' (SubstTyMorEq dB (MorEqMor2 dΓ dΔ dδ) (MorSymm dΓ dΔ dδ))))


ConvTy : {Γ Δ : Ctx n} {A : TyExpr n} → Derivable (Γ ⊢ A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ A)
ConvTy dA dΓ= = ConvTy' dA (CtxSymm dΓ=) (CtxEqCtx2 dΓ=)

ConvTyEq : {Γ Δ : Ctx n} {A B : TyExpr n} → Derivable (Γ ⊢ A == B) → (⊢ Γ == Δ) → Derivable (Δ ⊢ A == B)
ConvTyEq dA= dΓ= = ConvTyEq' dA= (CtxSymm dΓ=) (CtxEqCtx2 dΓ=)

ConvTm : {Γ Δ : Ctx n} {u : TmExpr n} {A : TyExpr n} → Derivable (Γ ⊢ u :> A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ u :> A)
ConvTm du dΓ= = ConvTm' du (CtxSymm dΓ=) (CtxEqCtx2 dΓ=)

ConvTmEq : {Γ Δ : Ctx n} {A : TyExpr n} {u v : TmExpr n} → Derivable (Γ ⊢ u == v :> A) → (⊢ Γ == Δ) → Derivable (Δ ⊢ u == v :> A)
ConvTmEq du= dΓ= = ConvTmEq' du= (CtxSymm dΓ=) (CtxEqCtx2 dΓ=)


ConvTm2 : {Γ Δ : Ctx n} {u : TmExpr n} {A A' : TyExpr n} → Derivable (Γ ⊢ u :> A) → (⊢ Γ == Δ) → Derivable (Γ ⊢ A == A') → Derivable (Δ ⊢ u :> A')
ConvTm2 du dΓ= dA= = let dΔ = CtxEqCtx2 dΓ= in Conv (ConvTy' (TyEqTy1 (CtxEqCtx1 dΓ=) dA=) (CtxSymm dΓ=) dΔ) (ConvTm' du (CtxSymm dΓ=) dΔ) (ConvTyEq' dA= (CtxSymm dΓ=) dΔ)

ConvTmEq2 : {Γ Δ : Ctx n} {u u' : TmExpr n} {A A' : TyExpr n} → Derivable (Γ ⊢ u == u' :> A) → (⊢ Γ == Δ) → Derivable (Γ ⊢ A == A') → Derivable (Δ ⊢ u == u' :> A')
ConvTmEq2 du= dΓ= dA= = ConvTmEq' (ConvEq (TyEqTy1 (CtxEqCtx1 dΓ=) dA=) du= dA=) (CtxSymm dΓ=) (CtxEqCtx2 dΓ=)

ConvMor : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ : Mor n m} → (Γ ⊢ δ ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ ∷> Δ')
ConvMor tt dΓ= tt = tt
ConvMor (dδ , du) dΓ= (dΔ= , dB=) = let dδ' = ConvMor dδ dΓ= dΔ= in
  (dδ' , ConvTm2 du dΓ= (SubstTyEq dB= dδ)) 

ConvMorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} → (Γ ⊢ δ == δ' ∷> Δ) → (⊢ Γ == Γ') → (⊢ Δ == Δ') → (Γ' ⊢ δ == δ' ∷> Δ')
ConvMorEq tt dΓ= tt = tt
ConvMorEq (dδ= , du=) dΓ= (dΔ= , dB=') =
  let dδ=' = ConvMorEq dδ= dΓ= dΔ=
      dΓ' = CtxEqCtx2 dΔ=
      dΓ'' = CtxEqCtx2 dΓ=
  in
  (dδ=' , ConvEq (SubstTy (TyEqTy1 (CtxEqCtx1 dΔ=) dB=') (ConvMor (MorEqMor1 (CtxEqCtx1 dΓ=) (CtxEqCtx1 dΔ=) dδ=) dΓ= (CtxRefl (CtxEqCtx1 dΔ=)))) (ConvTmEq du= dΓ=) (SubstTyEq dB=' ((ConvMor (MorEqMor1 (CtxEqCtx1 dΓ=) (CtxEqCtx1 dΔ=) dδ=) dΓ= (CtxRefl (CtxEqCtx1 dΔ=)))))) --ConvEq (SubstTy (TyEqTy1 dΓ' dB=') (MorEqMor1 dΓ'' dΓ' dδ=')) (ConvTmEq' du= dΓ= dΓ'') (SubstTyEq dB=' (MorEqMor1 dΓ'' dΓ' dδ=')))

SubstMor : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ : Mor m k} {δ : Mor n m} → (Δ ⊢ θ ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ θ [ δ ]Mor ∷> Θ)
SubstMor tt dδ = tt
SubstMor (dθ , dw) dδ = (SubstMor dθ dδ , congTm ([]Ty-assoc _ _ _) refl (SubstTm dw dδ))

SubstMorEq : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ θ' : Mor m k} {δ : Mor n m} → (Δ ⊢ θ == θ' ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ' [ δ ]Mor ∷> Θ)
SubstMorEq tt dδ = tt
SubstMorEq (dθ= , dw) dδ = SubstMorEq dθ= dδ , congTmEqTy ([]Ty-assoc _ _ _) (SubstTmEq dw dδ)

SubstMorMorEq : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ : Mor m k} {δ δ' : Mor n m} → (Δ ⊢ θ ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ [ δ' ]Mor ∷> Θ)
SubstMorMorEq tt dδ dδ= = tt
SubstMorMorEq (dθ , dw) dδ dδ= = SubstMorMorEq dθ dδ dδ= , congTmEqTy ([]Ty-assoc _ _ _) (SubstTmMorEq dw dδ dδ=)
 
SubstMorFullEq : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ θ' : Mor m k} {δ δ' : Mor n m} → (⊢ Δ) → (Δ ⊢ θ ∷> Θ) → (Δ ⊢ θ == θ' ∷> Θ) → (Γ ⊢ δ ∷> Δ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ' [ δ' ]Mor ∷> Θ)
SubstMorFullEq dΔ tt tt dδ dδ= = tt
SubstMorFullEq dΔ (dθ , dw) (dθ= , dw=) dδ dδ= =
  (SubstMorFullEq dΔ dθ dθ= dδ dδ= , congTmEqTy ([]Ty-assoc _ _ _) (SubstTmFullEq (TmEqTm2 dΔ dw=) dδ dw= dδ=))

SubstTyFullEq' : {Γ : Ctx n} {Δ : Ctx m} {A A' : TyExpr m} {δ δ' : Mor n m}
              → ⊢ Γ → ⊢ Δ → Derivable (Δ ⊢ A == A') → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A' [ δ' ]Ty)
SubstTyFullEq' dΓ dΔ dA= dδ= =
  let dδ = MorEqMor1 dΓ dΔ dδ=
      dA' = TyEqTy2 dΔ dA=
  in
  SubstTyFullEq dA' dδ dA= dδ=

SubstTyMorEq' : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m}
              → ⊢ Γ → ⊢ Δ → Derivable (Δ ⊢ A) → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ A [ δ ]Ty == A [ δ' ]Ty)
SubstTyMorEq' dΓ dΔ dA dδ= = SubstTyMorEq dA (MorEqMor1 dΓ dΔ dδ=) dδ=

SubstTmFullEq' : {Γ : Ctx n} {Δ : Ctx m} {u u' : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m}
              → ⊢ Γ → ⊢ Δ → Derivable (Δ ⊢ u == u' :> A) → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u' [ δ' ]Tm :> A [ δ ]Ty)
SubstTmFullEq' dΓ dΔ du= dδ= =
  let dδ = MorEqMor1 dΓ dΔ dδ=
      du' = TmEqTm2 dΔ du=
  in
  SubstTmFullEq du' dδ du= dδ=


SubstTmMorEq' : {Γ : Ctx n} {Δ : Ctx m} {u : TmExpr m} {A : TyExpr m} {δ δ' : Mor n m} → ⊢ Γ → ⊢ Δ → Derivable (Δ ⊢ u :> A)
             → (Γ ⊢ δ == δ' ∷> Δ) → Derivable (Γ ⊢ u [ δ ]Tm == u [ δ' ]Tm :> A [ δ ]Ty)
SubstTmMorEq' dΓ dΔ dA dδ= = SubstTmMorEq dA (MorEqMor1 dΓ dΔ dδ=) dδ=

SubstMorMorEq' : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ : Mor m k} {δ δ' : Mor n m} → (⊢ Γ) → (⊢ Δ) → (Δ ⊢ θ ∷> Θ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ [ δ' ]Mor ∷> Θ)
SubstMorMorEq' dΓ dΔ dθ dδ= = SubstMorMorEq dθ (MorEqMor1 dΓ dΔ dδ=) dδ=

SubstMorFullEq' : {Γ : Ctx n} {Δ : Ctx m} {Θ : Ctx k} {θ θ' : Mor m k} {δ δ' : Mor n m} → (⊢ Γ) → (⊢ Δ) → (⊢ Θ) → (Δ ⊢ θ == θ' ∷> Θ) → (Γ ⊢ δ == δ' ∷> Δ) → (Γ ⊢ θ [ δ ]Mor == θ' [ δ' ]Mor ∷> Θ)
SubstMorFullEq' dΓ dΔ tt tt dδ= = tt
SubstMorFullEq' dΓ dΔ (dΘ , dC) (dθ= , dw=) dδ= =
  (SubstMorFullEq' dΓ dΔ dΘ dθ= dδ= , congTmEqTy ([]Ty-assoc _ _ _) (SubstTmFullEq (Conv (SubstTy dC (MorEqMor2 dΔ dΘ dθ=)) (TmEqTm2 dΔ (ConvEq (SubstTy dC (MorEqMor1 dΔ dΘ dθ=)) dw= (SubstTyMorEq dC (MorEqMor1 dΔ dΘ dθ=) dθ=))) (SubstTyMorEq dC (MorEqMor2 dΔ dΘ dθ=) (MorSymm dΔ dΘ dθ=))) (MorEqMor1 dΓ dΔ dδ=) dw= dδ=))


WeakMor+Eq' : {Γ : Ctx n} {Δ : Ctx m} {A : TyExpr m} {δ δ' : Mor n m} → ⊢ Γ → ⊢ Δ → Derivable (Δ ⊢ A) → Γ ⊢ δ == δ' ∷> Δ → (Γ , A [ δ ]Ty) ⊢ weakenMor+ δ == weakenMor+ δ' ∷> (Δ , A)
WeakMor+Eq' dΓ dΔ dA dδ= = WeakMor+Eq dA (MorEqMor1 dΓ dΔ dδ=) dδ=


-- This has become absolete
-- _,,_ : {Γ Γ' : Ctx n} {A A' : TyExpr n} → ⊢ Γ == Γ' → Derivable (Γ ⊢ A == A') → ⊢ (Γ , A) == (Γ' , A')
-- dΓ= ,, dA= = dΓ= , dA= -- ConvTyEq' dA= dΓ= (CtxEqCtx2 dΓ=)

TmTran' : {Γ : Ctx n} {u v w : TmExpr n} {A : TyExpr n} → ⊢ Γ
        → Derivable (Γ ⊢ u == v :> A) → Derivable (Γ ⊢ v == w :> A) → Derivable (Γ ⊢ u == w :> A)
TmTran' dΓ du= dv= = TmTran (TmEqTm1 dΓ dv=) du= dv=

TyTran' : {Γ : Ctx n} {A B C : TyExpr n} → ⊢ Γ
        → Derivable (Γ ⊢ A == B) → Derivable (Γ ⊢ B == C) → Derivable (Γ ⊢ A == C)
TyTran' dΓ dA= dB= = TyTran (TyEqTy1 dΓ dB=) dA= dB=

DerTmTy : {Γ : Ctx n} {u : TmExpr n} {A : TyExpr n} → (⊢ Γ) → Derivable (Γ ⊢ u :> A) → Derivable (Γ ⊢ A)
DerTmTy dΓ (Var k dA) = getTyDer k dΓ
DerTmTy dΓ (Conv dA du dA=) = TyEqTy2 dΓ dA=
DerTmTy dΓ UUUU = UU
DerTmTy dΓ (SumUU da db) = UU
DerTmTy dΓ (Inl dA dB da) = Sum dA dB
DerTmTy dΓ (Inr dA dB db) = Sum dA dB
DerTmTy dΓ (Match dA dB dC dda ddb du) = SubstTy dC (idMorDerivable dΓ , congTmTy! ([idMor]Ty _) du)
DerTmTy dΓ (PiUU da db) = UU
DerTmTy dΓ (Lam dA dB du) = Pi dA dB
DerTmTy dΓ (App dA dB df da) = SubstTy dB ((idMorDerivable dΓ) , congTm (! ([idMor]Ty _)) refl da)
DerTmTy dΓ (SigUU da db) = UU
DerTmTy dΓ (Pair dA dB da db) = Sig dA dB
DerTmTy dΓ (Pr1 dA dB du) = dA
DerTmTy dΓ (Pr2 dA dB du) = SubstTy dB (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl (Pr1 dA dB du))
DerTmTy dΓ EmptyUU = UU
DerTmTy dΓ (Emptyelim dA du) = SubstTy dA (idMorDerivable dΓ , du)
DerTmTy dΓ UnitUU = UU
DerTmTy dΓ TT = Unit
DerTmTy dΓ (Unitelim dA dtt du) = SubstTy dA (idMorDerivable dΓ , du)
DerTmTy dΓ NatUU = UU
DerTmTy dΓ Zero = Nat
DerTmTy dΓ (Suc du) = Nat
DerTmTy dΓ (Natelim dP dO dS du) = SubstTy dP (idMorDerivable dΓ , du)
DerTmTy dΓ (IdUU da du dv) = UU
DerTmTy dΓ (Refl dA da) = Id dA da da
DerTmTy dΓ (JJ dA dP dd da db dp) = Subst3Ty dΓ dP da (congTmTy (! (weakenSubstTy _ _ )) db) (congTmTy (ap-id-Ty (! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _ ∙ [idMor]Ty _)) refl refl) dp)
