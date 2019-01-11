{-# OPTIONS --rewriting --prop --without-K --sized-types #-}

open import common

-- Somehow it doesn’t work to put that in common…
variable
  {s} : Size

{- Syntax of term- and type-expressions, using de Bruijn indices -}

data TyExpr : {s : Size} → ℕ → Set
data TmExpr : {s : Size} → ℕ → Set

data TyExpr where
  uu : (i : ℕ) → TyExpr {s} n
  el : (i : ℕ) (v : TmExpr {s} n) → TyExpr {↑ s} n
  pi : (A : TyExpr {s} n) (B : TyExpr {s} (suc n)) → TyExpr {↑ s} n
  sig : (A : TyExpr {s} n) (B : TyExpr {s} (suc n)) → TyExpr {↑ s} n
  nat : TyExpr {s} n
  id : (A : TyExpr {s} n) (u v : TmExpr {s} n) → TyExpr {↑ s} n

data TmExpr where
  var : (x : Fin n) → TmExpr {s} n

  uu : (i : ℕ) → TmExpr {s} n

  pi : (i : ℕ) (a : TmExpr {s} n) (b : TmExpr {s} (suc n)) → TmExpr {↑ s} n
  lam : (A : TyExpr {s} n) (B : TyExpr {s} (suc n)) (u : TmExpr {s} (suc n)) → TmExpr {↑ s} n
  app : (A : TyExpr {s} n) (B : TyExpr {s} (suc n)) (f : TmExpr {s} n) (a : TmExpr {s} n) → TmExpr {↑ s} n

  sig : (i : ℕ) (a : TmExpr {s} n) (b : TmExpr {s} (suc n)) → TmExpr {↑ s} n
  pair : (A : TyExpr {s} n) (B : TyExpr {s} (suc n)) (a : TmExpr {s} n) (b : TmExpr {s} n) → TmExpr {↑ s} n
  pr1 : (A : TyExpr {s} n) (B : TyExpr {s} (suc n)) (u : TmExpr {s} n) → TmExpr {↑ s} n
  pr2 : (A : TyExpr {s} n) (B : TyExpr {s} (suc n)) (u : TmExpr {s} n) → TmExpr {↑ s} n

  nat : (i : ℕ) → TmExpr {↑ s} n
  zero : TmExpr {s} n
  suc : (u : TmExpr {s} n) → TmExpr {↑ s} n
  -- nat-elim : (P : TyExpr {s} (suc n)) (d0 : TmExpr {s} n) (dS : TmExpr {s} (suc (suc n))) (u : TmExpr {s} n) → TmExpr {↑ s} n

  id : (i : ℕ) (a u v : TmExpr {s} n) → TmExpr {↑ s} n
  refl : (A : TyExpr {s} n) (u : TmExpr {s} n) → TmExpr {↑ s} n
  -- jj : (A : TyExpr {s} n) (P : TyExpr {s} (suc (suc (suc n)))) (d : TmExpr {s} (suc n)) (a b p : TmExpr {s} n) → TmExpr {↑ s} n
