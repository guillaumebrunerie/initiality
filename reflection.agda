{-# OPTIONS --rewriting --prop --without-K -v tc.unquote:10 #-}

open import common
open import Agda.Builtin.Reflection public
open import Agda.Builtin.Unit public
open import Agda.Builtin.String public renaming (primStringAppend to _++ₛ_)
open import Agda.Builtin.Sigma public renaming (Σ to ΣR)

_×R_ : (A B : Set) → Set
A ×R B = ΣR A (λ _ → B)

instance
  TCMonad : Monad {ℓ = lzero} TC
  return {{TCMonad}} = returnTC
  _>>=_ {{TCMonad}} = bindTC


{- Operations on lists -}

map : {A B : Set} → (f : A → B) → List A → List B
map f [] = []
map f (a ∷ as) = (f a ∷ map f as)

_++_ : {A : Set} → List A → List A → List A
[] ++ l = l
(a ∷ as) ++ l = a ∷ (as ++ l)

concat : {A : Set} → List (List A) → List A
concat [] = []
concat (l ∷ ls) = l ++ concat ls

mapTC : {A B : Set} → (f : A → TC B) → List A → TC (List B)
mapTC f [] = return []
mapTC f (a ∷ as) = do
  fa ← f a
  fas ← mapTC f as
  return (fa ∷ fas)

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ l) = reverse l ++ (x ∷ [])


{- Operations on arginfo -}

earg : {A : Set} → A → Arg A
earg x = arg (arg-info visible relevant) x

iarg : {A : Set} → A → Arg A
iarg x = arg (arg-info hidden relevant) x


{- Shifting de Bruijn indices -}

{-# TERMINATING #-}
shift : ℕ → Term → Term
shiftArg : ℕ → Arg Term → Arg Term
shiftAbs : ℕ → Abs Term → Abs Term
shiftSort : ℕ → Sort → Sort
shiftClause : ℕ → Clause → Clause

shift n (var x args) = var (n + x) (map (shiftArg n) args)
shift n (con c args) = con c (map (shiftArg n) args)
shift n (def f args) = def f (map (shiftArg n) args)
shift n (lam v t) = lam v (shiftAbs n t)
shift n (pat-lam cs args) = pat-lam (map (shiftClause n) cs) (map (shiftArg n) args)
shift n (pi a b) = pi (shiftArg n a) (shiftAbs n b)
shift n (agda-sort s) = agda-sort (shiftSort n s)
shift n (lit l) = lit l
shift n (meta x args) = meta x (map (shiftArg n) args)
shift n unknown = unknown

shiftArg n (arg i x) = arg i (shift n x)

shiftAbs n (abs s x) = abs s (shift n x)

shiftSort n (set u) = set (shift n u)
shiftSort n (lit k) = lit k
shiftSort n unknown = unknown

shiftClause n (clause ps t) = clause ps (shift n t)
shiftClause n (absurd-clause ps) = absurd-clause ps


if_then_else_ : {A : Set} → Bool → A → A → A
if true then t else f = t
if false then t else f = f

lookup : List (Name ×R Name) → Name → Name
lookup [] _ = quote lookup
lookup ((a , b) ∷ l) a' = if primQNameEquality a a' then b else lookup l a'

getNumberOfPi : Type → ℕ
getNumberOfPi (pi _ (abs _ B)) = suc (getNumberOfPi B)
getNumberOfPi _ = 0

abstract
  ERROR : Set
  ERROR = ⊤
