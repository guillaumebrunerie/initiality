{-# OPTIONS --rewriting --prop --without-K -v tc.unquote:10 #-}

open import Agda.Builtin.Reflection public
open import Agda.Builtin.Unit public
open import Agda.Builtin.String public renaming (primStringAppend to _++ₛ_)

open import common
open import typetheory

_×R_ : (A B : Set) → Set
A ×R B = ΣSS A (λ _ → B)

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

{- Meta-macros -}

getConsTyTm : TC (List Name ×R List Name)
getConsTyTm = do
  data-type _ consTy ← getDefinition (quote TyExpr)
    where _ → typeError (strErr "TyExpr is not a datatype." ∷ [])
  data-type _ consTm ← getDefinition (quote TmExpr)
    where _ → typeError (strErr "TmExpr is not a datatype." ∷ [])
  return (consTy , consTm)

applyToFresh : (Name → Name → TC ⊤) → String → Name → TC (Name ×R Name)
applyToFresh f hint s = do
  sNew ← freshName (hint ++ₛ primShowQName s)
  f s sNew
  return (s , sNew)

listify : List (Name ×R Name) → Term
listify [] = con (quote []) []
listify ((s , t) ∷ l) = con (quote _∷_) (earg (con (quote ΣSS._,_) (earg (lit (name s)) ∷ earg (lit (name t)) ∷ [])) ∷ earg (listify l) ∷ [])

iterateExpr : Name → (Name → Name → TC ⊤) → TC ⊤
iterateExpr s f = do
  (consTy , consTm) ← getConsTyTm
  list ← mapTC (applyToFresh f "ap-") (consTy ++ consTm)
  defineFun s (clause [] (listify list) ∷ [])

Ty?Tm : Name → Name → Name → Name
Ty?Tm (quote TyExpr) TyFun TmFun = TyFun
Ty?Tm (quote TmExpr) TyFun TmFun = TmFun 
Ty?Tm _ _ _ = quote ERROR

generateClausewise : Name → Name → List (Arg Pattern) → List (Arg Pattern) → (ℕ → Term) → (ℕ → Name → Term → Term) → TC ⊤
generateClausewise funTy funTm preArgs postArgs varCase TmTyCase = (do
  (consTy , consTm) ← getConsTyTm
  clausesTy ← mapTC constructClause consTy
  defineFun funTy clausesTy
  clausesTm ← mapTC constructClause consTm
  defineFun funTm clausesTm)  where

    constructPattern : Type → List (Arg Pattern)
    constructPattern (pi (arg i _) (abs s B)) =
      arg i (var s) ∷ constructPattern B
    constructPattern A = []

    constructClause : Name → TC Clause
    constructClause c = do
      pi _ (abs _ tyC) ← getType c
        where _ → typeError (strErr "The constructor should have [n] as a first implicit argument" ∷ [])
      let l = getNumberOfPi tyC
      let result = if primQNameEquality c (quote TmExpr.var) then
                     varCase l
                   else
                     TmTyCase l c tyC
      return (clause (preArgs ++ (earg (con c (constructPattern tyC)) ∷ postArgs)) result)

-- var+extra : Name → (ℕ → Term)
-- var+extra varCase l = def varCase (earg (var 0 []) ∷ [])

depth : Arg Term → ℕ
depth (arg _ (con _ (n ∷ _))) =  suc (depth n)
depth _ = zero

makeArgs : (Name → ℕ → ℕ → Arg Term) → (ℕ → Type → List (Arg Term))
makeArgs body n (pi (arg i (def T (k ∷ _))) (abs s B)) =
  body T n (depth k) ∷ makeArgs body (n - 1) B
makeArgs body n (pi (arg (arg-info visible _) _) (abs s B)) =
  earg (con (quote _≡_.refl) []) ∷ makeArgs body (n - 1) B
makeArgs body n (pi _ (abs s B)) = makeArgs body (n - 1) B
makeArgs body n _ = []

makeArgs' : ℕ → (Name → ℕ → ℕ → Arg Term) → (ℕ → Type → List (Arg Term))
makeArgs' shift body n (pi (arg i (def T (k ∷ _))) (abs s B)) =
  body T n (depth k) ∷ makeArgs' shift body (n - 1) B
makeArgs' shift body n (pi (arg (arg-info visible _) _) (abs s B)) =
  earg (var (n + shift) []) ∷ makeArgs' shift body (n - 1) B
makeArgs' shift body n (pi _ (abs s B)) = makeArgs' shift body (n - 1) B
makeArgs' shift body n _ = []

{- Generate the ap lemmas for every type/term constructor -}

half : ℕ → ℕ
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

-- Takes a name [s] and a type [A₀ → … → Aₙ → B] and generates [{x₀ y₀ : A₀} (p₀ : x₀ ≡ y₀) … {xₙ yₙ : Aₙ} (pₙ : xₙ ≡ yₙ) → s x₀ … xₙ ≡ s y₀ … yₙ]
generate-type : ℕ → Name → Type → Type
generate-type n s (pi (arg ai A) (abs x B)) =
  pi (iarg (shift n A)) (abs x
  (pi (iarg (shift (suc n) A)) (abs (x ++ₛ "'")
  (pi (earg (def (quote _≡_) (earg (var 1 []) ∷ earg (var 0 []) ∷ []))) (abs (x ++ₛ "⁼")
  (generate-type (2 + n) s B))))))
generate-type n s _ =
  def (quote _≡_) (earg (con s (iarg (var (half n * 3) []) ∷ make-args 2 n))
                 ∷ earg (con s (iarg (var (half n * 3) []) ∷ make-args 1 n)) ∷ [])  where

    make-args : ℕ → ℕ → List (Arg Term)
    make-args k zero = []
    make-args k (suc zero) = []
    make-args k (suc (suc n)) = earg (var (half n * 3 + k) []) ∷ make-args k n

generate-pattern : Type → List (Arg Pattern)
generate-pattern (pi _ (abs _ B)) = earg (con (quote _≡_.refl) []) ∷ generate-pattern B
generate-pattern _ = []

generate-ap : Name → Name → TC ⊤
generate-ap s res = do
  pi A (abs y ts) ← getType s
      where _ → typeError (strErr "not a Pi" ∷ [])
  _ ← declareDef (earg res) (pi A (abs y (generate-type 0 s ts)))
  _ ← defineFun res (clause (generate-pattern ts) (con (quote _≡_.refl) []) ∷ [])
  return _
 
corresponding-ap : List (Name ×R Name)
unquoteDef corresponding-ap = iterateExpr corresponding-ap generate-ap

apify : (Name → ℕ → ℕ → Arg Term) → (ℕ → Name → Term → Term)
apify body l c tyC = def (lookup corresponding-ap c) (makeArgs body (l - 1) tyC)


unquoteDecl ap-uu-Tm = generate-ap (quote TmExpr.uu) ap-uu-Tm
unquoteDecl ap-var-Tm = generate-ap (quote TmExpr.var) ap-var-Tm
unquoteDecl ap-pi-Ty = generate-ap (quote TyExpr.pi) ap-pi-Ty
unquoteDecl ap-sig-Ty = generate-ap (quote TyExpr.sig) ap-sig-Ty
unquoteDecl ap-pi-Tm = generate-ap (quote TmExpr.pi) ap-pi-Tm
unquoteDecl ap-lam-Tm = generate-ap (quote TmExpr.lam) ap-lam-Tm
unquoteDecl ap-app-Tm = generate-ap (quote TmExpr.app) ap-app-Tm
unquoteDecl ap-sig-Tm = generate-ap (quote TmExpr.sig) ap-sig-Tm
unquoteDecl ap-pair-Tm = generate-ap (quote TmExpr.pair) ap-pair-Tm
unquoteDecl ap-pr1-Tm = generate-ap (quote TmExpr.pr1) ap-pr1-Tm
unquoteDecl ap-pr2-Tm = generate-ap (quote TmExpr.pr2) ap-pr2-Tm
unquoteDecl ap-nat-elim-Tm = generate-ap (quote TmExpr.natelim) ap-nat-elim-Tm
unquoteDecl ap-jj-Tm = generate-ap (quote TmExpr.jj) ap-jj-Tm 
unquoteDecl ap-el-Ty = generate-ap (quote TyExpr.el) ap-el-Ty 
unquoteDecl ap-id-Ty = generate-ap (quote TyExpr.id) ap-id-Ty
unquoteDecl ap-id-Tm = generate-ap (quote TmExpr.id) ap-id-Tm
unquoteDecl ap-suc-Tm = generate-ap (quote TmExpr.suc) ap-suc-Tm
unquoteDecl ap-refl-Tm = generate-ap (quote TmExpr.refl) ap-refl-Tm

iterate : ℕ → (List (Arg Term) → Term) → Term → Term
iterate 0 f t = t
iterate (suc n) f t = f (earg (iterate n f t) ∷ [])

-- ≡R

generate-typeR : ℕ → Name → Type → Type
generate-typeR n s (pi (arg ai A) (abs x B)) =
  pi (iarg (shift n A)) (abs x
  (pi (iarg (shift (suc n) A)) (abs (x ++ₛ "'")
  (pi (earg (def (quote _≡R_) (earg (var 1 []) ∷ earg (var 0 []) ∷ []))) (abs (x ++ₛ "⁼")
  (generate-typeR (2 + n) s B))))))
generate-typeR n s _ =
  def (quote _≡R_) (earg (con s (iarg (var (half n * 3) []) ∷ make-args 2 n))
                 ∷ earg (con s (iarg (var (half n * 3) []) ∷ make-args 1 n)) ∷ [])  where

    make-args : ℕ → ℕ → List (Arg Term)
    make-args k zero = []
    make-args k (suc zero) = []
    make-args k (suc (suc n)) = earg (var (half n * 3 + k) []) ∷ make-args k n



generate-patternR : Type → List (Arg Pattern)
generate-patternR (pi _ (abs _ B)) = earg (con (quote _≡R_.reflR) []) ∷ generate-patternR B
generate-patternR _ = []

generate-apR : Name → Name → TC ⊤
generate-apR s res = do
  pi A (abs y ts) ← getType s
    where _ → typeError (strErr "not a Pi" ∷ [])
  _ ← declareDef (earg res) (pi A (abs y (generate-typeR 0 s ts)))
  _ ← defineFun res (clause (generate-patternR ts) (con (quote _≡R_.reflR) []) ∷ [])
  return _


unquoteDecl apR-var-Tm = generate-apR (quote TmExpr.var) apR-var-Tm
unquoteDecl apR-pi-Ty = generate-apR (quote TyExpr.pi) apR-pi-Ty 
unquoteDecl apR-sig-Ty = generate-apR (quote TyExpr.sig) apR-sig-Ty
unquoteDecl apR-pi-Tm = generate-apR (quote TmExpr.pi) apR-pi-Tm
unquoteDecl apR-lam-Tm = generate-apR (quote TmExpr.lam) apR-lam-Tm
unquoteDecl apR-app-Tm = generate-apR (quote TmExpr.app) apR-app-Tm
unquoteDecl apR-sig-Tm = generate-apR (quote TmExpr.sig) apR-sig-Tm
unquoteDecl apR-pair-Tm = generate-apR (quote TmExpr.pair) apR-pair-Tm
unquoteDecl apR-pr1-Tm = generate-apR (quote TmExpr.pr1) apR-pr1-Tm
unquoteDecl apR-pr2-Tm = generate-apR (quote TmExpr.pr2) apR-pr2-Tm
unquoteDecl apR-natelim-Tm = generate-apR (quote TmExpr.natelim) apR-natelim-Tm
unquoteDecl apR-jj-Tm = generate-apR (quote TmExpr.jj) apR-jj-Tm
unquoteDecl apR-el-Ty = generate-apR (quote TyExpr.el) apR-el-Ty
unquoteDecl apR-id-Ty = generate-apR (quote TyExpr.id) apR-id-Ty
unquoteDecl apR-id-Tm = generate-apR (quote TmExpr.id) apR-id-Tm
unquoteDecl apR-suc-Tm = generate-apR (quote TmExpr.suc) apR-suc-Tm
unquoteDecl apR-refl-Tm = generate-apR (quote TmExpr.refl) apR-refl-Tm
