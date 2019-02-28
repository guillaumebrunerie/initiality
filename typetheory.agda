{-# OPTIONS --rewriting --prop --without-K --no-auto-inline #-}

open import common

{- Syntax of term- and type-expressions, using de Bruijn indices -}

data TyExpr : ℕ → Set
data TmExpr : ℕ → Set

data TyExpr where
  uu : (i : ℕ) → TyExpr n
  el : (i : ℕ) (v : TmExpr n) → TyExpr n
  pi : (A : TyExpr n) (B : TyExpr (suc n)) → TyExpr n
  sig : (A : TyExpr n) (B : TyExpr (suc n)) → TyExpr n
  nat : TyExpr n
  id : (A : TyExpr n) (u v : TmExpr n) → TyExpr n

data TmExpr where
  var : (x : Fin n) → TmExpr n

  uu : (i : ℕ) → TmExpr n

  pi : (i : ℕ) (a : TmExpr n) (b : TmExpr (suc n)) → TmExpr n
  lam : (A : TyExpr n) (B : TyExpr (suc n)) (u : TmExpr (suc n)) → TmExpr n
  app : (A : TyExpr n) (B : TyExpr (suc n)) (f : TmExpr n) (a : TmExpr n) → TmExpr n

  sig : (i : ℕ) (a : TmExpr n) (b : TmExpr (suc n)) → TmExpr n
  pair : (A : TyExpr n) (B : TyExpr (suc n)) (a : TmExpr n) (b : TmExpr n) → TmExpr n
  pr1 : (A : TyExpr n) (B : TyExpr (suc n)) (u : TmExpr n) → TmExpr n
  pr2 : (A : TyExpr n) (B : TyExpr (suc n)) (u : TmExpr n) → TmExpr n

  nat : (i : ℕ) → TmExpr n
  zero : TmExpr n
  suc : (u : TmExpr n) → TmExpr n
  natelim : (P : TyExpr (suc n)) (d0 : TmExpr n) (dS : TmExpr (suc (suc n))) (u : TmExpr n) → TmExpr n

  id : (i : ℕ) (a u v : TmExpr n) → TmExpr n
  refl : (A : TyExpr n) (u : TmExpr n) → TmExpr n
  jj : (A : TyExpr n) (P : TyExpr (suc (suc (suc n)))) (d : TmExpr (suc n)) (a b p : TmExpr n) → TmExpr n
