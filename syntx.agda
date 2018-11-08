{-# OPTIONS --rewriting --allow-unsolved-metas --prop --no-termination-check #-}
-- The flag --no-termination-check is enabled because of issue #3332
 
open import common
open import Agda.Builtin.Size

{- Syntax of term- and type-expressions, using de Bruijn indices -}
variable
  {i} : Size

data TyExpr : {i : Size} → ℕ → Set
data TmExpr : {i : Size} → ℕ → Set

data TyExpr where
  pi : (A : TyExpr {i} n) (B : TyExpr {i} (suc n)) → TyExpr {↑ i} n
  uu : TyExpr {i} n
  el : (v : TmExpr {i} n) → TyExpr {↑ i} n

data TmExpr where
  var : (x : Fin n) → TmExpr {i} n
  lam : (A : TyExpr {i} n) (B : TyExpr {i} (suc n)) (u : TmExpr {i} (suc n)) → TmExpr {↑ i} n
  app : (A : TyExpr {i} n) (B : TyExpr {i} (suc n)) (f : TmExpr {i} n) (a : TmExpr {i} n) → TmExpr {↑ i} n

{- Contexts and context morphisms -}

data Ctx : ℕ → Set where
  ◇ : Ctx 0
  _,_ : {n : ℕ} (Γ : Ctx n) (A : TyExpr n) → Ctx (suc n)

data Mor (n : ℕ) : ℕ → Set where
  ◇ : Mor n 0
  _,_ : {m : ℕ} (δ : Mor n m) (u : TmExpr n) → Mor n (suc m)

{- Weakening -}

-- position : Fin n -> ℕ
-- position {n = n} last = n
-- position {n = suc n} (prev x) = position {n = n} x

weakenTy' : (k : Fin (suc n)) → TyExpr n → TyExpr (suc n)
weakenTm' : (k : Fin (suc n)) → TmExpr n → TmExpr (suc n)
weakenVar' : (k : Fin (suc n)) → Fin n → Fin (suc n)

weakenTy' k (pi A B) = pi (weakenTy' k A) (weakenTy' (prev k) B)
weakenTy' k uu = uu
weakenTy' k (el v) = el (weakenTm' k v)

weakenTm' k (var x) = var (weakenVar' k x)
weakenTm' k (lam A B u) = lam (weakenTy' k A) (weakenTy' (prev k) B) (weakenTm' (prev k) u)
weakenTm' k (app A B f a) = app (weakenTy' k A) (weakenTy' (prev k) B) (weakenTm' k f) (weakenTm' k a)

weakenVar' last = prev
weakenVar' (prev k) last = last
weakenVar' (prev k) (prev x) = prev (weakenVar' k x)

weakenTy : TyExpr n → TyExpr (suc n)
weakenTy = weakenTy' last

weakenTm : TmExpr n → TmExpr (suc n)
weakenTm = weakenTm' last


weakenMor' : (k : Fin (suc n)) → Mor n m → Mor (suc n) m
weakenMor' k ◇ = ◇
weakenMor' k (δ , u) = (weakenMor' k δ , weakenTm' k u)

weakenMor : Mor n m → Mor (suc n) m
weakenMor = weakenMor' last

-- {- Substitution -}


substTy : TyExpr (m + suc n) → TmExpr n → TyExpr (m + n)
substTm : TmExpr (m + suc n) → TmExpr n → TmExpr (m + n)
substVar : Fin (m + suc n) → TmExpr n → TmExpr (m + n)

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

{- Total substitutions -}

infix 42 _[_]Ty
infix 42 _[_]Tm

n+0 : n + zero ≡ n
n+0 {zero} = refl
n+0 {suc n} = ap suc n+0

n+suc : n + (suc m) ≡ (suc n) + m
n+suc {n = zero} = refl
n+suc {n = suc n} = ap suc n+suc

transport : {A : Set} (P : A -> Set) {a b : A} (p : a ≡ b) -> P a -> P b
transport _ refl x = x
 
trFin : (n ≡ m) → Fin n → Fin m
trFin refl x = x

prev^ : (m : ℕ) → Fin (suc n) → Fin (suc (n + m))
prev^ {n = n} zero k = trFin (ap suc (! n+0)) k
prev^ {n = n} (suc m) k = trFin (ap suc (! n+suc)) (prev (prev^ m k))

-- first : Fin (suc n)
-- first {zero} = last
-- first {suc n} = prev first

-- n+1 : n + 1 ≡  suc n
-- n+1 {zero} = refl
-- n+1 {suc n} = ap suc n+1

-- shiftTy' : (k : Fin (suc n)) ->  TyExpr n -> TyExpr (n + 1)
-- shiftTm' : (k : Fin (suc n)) -> TmExpr n -> TmExpr (n + 1)
-- shiftVar : (k : Fin (suc n)) -> Fin n -> Fin (n + 1) 

-- shiftTy' k (pi A B) = pi (shiftTy' k A) (shiftTy' (prev k) B)
-- shiftTy' k uu = uu
-- shiftTy' k (el v) = el (shiftTm' k v)

-- shiftTm' k (var x) = var (shiftVar k x)
-- shiftTm' k (lam A B u) = lam (shiftTy' k A) (shiftTy' (prev k) B) (shiftTm' (prev k) u)
-- shiftTm' k (app A B f a) = app (shiftTy' k A) (shiftTy' (prev k) B) (shiftTm' k f) (shiftTm' k a) 

-- shiftVar last x = transport Fin (! n+1) (prev x)
-- shiftVar (prev k) last = last
-- shiftVar (prev k) (prev x) = prev (shiftVar k x)


-- shiftTy : TyExpr n -> TyExpr (n + 1)
-- shiftTy = shiftTy' first

-- shiftTm : TmExpr n -> TmExpr (n + 1)
-- shiftTm = shiftTm' first

shiftTy^ : TyExpr n -> TyExpr (n + m)
shiftTy^ {m = zero} A = transport TyExpr (! n+0) A
shiftTy^ {m = suc m} A = transport TyExpr (! n+suc) ((weakenTy' (prev^ m last) (shiftTy^ {m = m} A)))

shiftTm^ : TmExpr n -> TmExpr (n + m)
shiftTm^ {m = zero} t = transport TmExpr (! n+0) t
shiftTm^ {m = suc m} t = transport TmExpr (! n+suc) ((weakenTm' (prev^ m last) (shiftTm^ {m = m} t)))

-- shiftTy : TyExpr n -> TyExpr (suc n)
-- shiftTm : TmExpr n -> TmExpr (suc n)

-- shiftTy = weakenTy' first
-- shiftTm = weakenTm' first

-- shiftTy^ : {m : ℕ} -> TyExpr n -> TyExpr (n + m)
-- shiftTy^ {m = zero} A = transport TyExpr (! n+0) A
-- shiftTy^ {m = suc m} A = transport TyExpr (! n+suc) (shiftTy^ (shiftTy A))

-- shiftTm^ : {m : ℕ} -> TmExpr n -> TmExpr (n + m)
-- shiftTm^ {m = zero} t = transport TmExpr (! n+0) t
-- shiftTm^ {m = suc m} t = transport TmExpr (! n+suc) (shiftTm^ (shiftTm t))


_[_]Ty' : {m n k : ℕ} -> TyExpr (k + n) -> (δ : Mor m n) -> TyExpr (k + m)
_[_]Tm' : {m n k : ℕ} -> TmExpr (k + n) -> (δ : Mor m n) -> TmExpr (k + m)

A [ ◇ ]Ty' = shiftTy^ (transport TyExpr n+0 A)
A [ δ , u ]Ty' = substTy (transport TyExpr (! n+suc) ((transport TyExpr n+suc A) [ δ ]Ty')) u

t [ ◇ ]Tm' = shiftTm^ (transport TmExpr n+0 t)
t [ δ , u ]Tm' = substTm (transport TmExpr (! n+suc) (((transport TmExpr n+suc t) [ δ ]Tm'))) u 

_[_]Ty : {n m : ℕ} → TyExpr n → (δ : Mor m n) → TyExpr m
_[_]Tm : {n m : ℕ} → TmExpr n → (δ : Mor m n) → TmExpr m

-- A [ δ ]Ty = A [ δ ]Ty'
-- t [ δ ]Tm = t [ δ ]Tm'


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

{- Weakening commutes with weakening -}

n+0 : (n : ℕ) → (n + 0) ≡R n
n+0 0 = reflR
n+0 (suc n) = apR suc (n+0 n)

n+suc : (n m : ℕ) → (n + suc m) ≡R suc (n + m)
n+suc 0 m = reflR
n+suc (suc n) m = apR suc (n+suc n m)

trFin : (n ≡R m) → Fin n → Fin m
trFin reflR x = x

prev^ : (m : ℕ) → Fin (suc n) → Fin (suc (n + m))
prev^ {n = n} zero k = trFin (apR suc (!R (n+0 n))) k
prev^ {n = n} (suc m) k = trFin (apR suc (!R (n+suc n m))) (prev (prev^ m k))

trTyExpr : (n ≡R m) → TyExpr {i} n → TyExpr {i} m
trTyExpr reflR x = x

FTy : (n : ℕ) (m : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TyExpr {i} (suc (n + m))) (p : u ≡R suc (n + m)) → Prop
FTy n m u k A p =
  weakenTy' (trFin (apR suc (!R (apR suc p))) (prev (prev^ m last))) (weakenTy' (trFin (apR suc (!R p)) (prev (prev^ m k))) (trTyExpr (!R p) A)) ≡
  weakenTy' (trFin (apR suc (!R (apR suc p))) (prev (prev^ m (prev k)))) (weakenTy' (trFin (apR suc (!R p)) (prev (prev^ m last))) (trTyExpr ((!R p)) A))

trFTy : {i : Size} (n : ℕ) (m : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TyExpr (suc (n + m))) (p : u ≡R suc (n + m)) → FTy {i} n m u k A p → FTy {i} n m (suc (n + m)) k A reflR
trFTy n m u k A reflR x = x

trTmExpr : (n ≡R m) → TmExpr {i} n → TmExpr {i} m
trTmExpr reflR x = x

FTm : (n : ℕ) (m : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TmExpr {i} (suc (n + m))) (p : u ≡R suc (n + m)) → Prop
FTm n m u k A p =
  weakenTm' (trFin (apR suc (!R (apR suc p))) (prev (prev^ m last))) (weakenTm' (trFin (apR suc (!R p)) (prev (prev^ m k))) (trTmExpr (!R p) A)) ≡
  weakenTm' (trFin (apR suc (!R (apR suc p))) (prev (prev^ m (prev k)))) (weakenTm' (trFin (apR suc (!R p)) (prev (prev^ m last))) (trTmExpr ((!R p)) A))

trFTm : {i : Size} (n : ℕ) (m : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TmExpr (suc (n + m))) (p : u ≡R suc (n + m)) → FTm {i} n m u k A p → FTm {i} n m (suc (n + m)) k A reflR
trFTm n m u k A reflR x = x

FVar : (n : ℕ) (m : ℕ) (u : ℕ) (k : Fin (suc n)) (A : Fin (suc (n + m))) (p : u ≡R suc (n + m)) → Prop
FVar n m u k A p =
  weakenVar' (trFin (apR suc (!R (apR suc p))) (prev (prev^ m last))) (weakenVar' (trFin (apR suc (!R p)) (prev (prev^ m k))) (trFin (!R p) A)) ≡
  weakenVar' (trFin (apR suc (!R (apR suc p))) (prev (prev^ m (prev k)))) (weakenVar' (trFin (apR suc (!R p)) (prev (prev^ m last))) (trFin ((!R p)) A))

trFVar : {i : Size} (n : ℕ) (m : ℕ) (u : ℕ) (k : Fin (suc n)) (A : Fin (suc (n + m))) (p : u ≡R suc (n + m)) → FVar n m u k A p → FVar n m (suc (n + m)) k A reflR
trFVar n m u k A reflR x = x

weakenCommutesTy'' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TyExpr {i} (suc (n + m))) → FTy n m (suc (n + m)) k A reflR
weakenCommutesTy' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TyExpr {i} (n + m)) → weakenTy' (prev^ m last) (weakenTy' (prev^ m k) A) ≡ weakenTy' (prev^ m (prev k)) (weakenTy' (prev^ m last) A)

weakenCommutesTm'' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TmExpr {i} (suc (n + m))) → FTm n m (suc (n + m)) k A reflR
weakenCommutesTm' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TmExpr {i} (n + m)) → weakenTm' (prev^ m last) (weakenTm' (prev^ m k) A) ≡ weakenTm' (prev^ m (prev k)) (weakenTm' (prev^ m last) A)

weakenCommutesVar' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : Fin (n + m)) → weakenVar' (prev^ m last) (weakenVar' (prev^ m k) A) ≡ weakenVar' (prev^ m (prev k)) (weakenVar' (prev^ m last) A)

weakenCommutesTy'' {n = n} m k A = trFTy n m (n + suc m) k A (n+suc n m) (weakenCommutesTy' (suc m) k (trTyExpr (!R (n+suc n m)) A))

weakenCommutesTy' {n = n} m k (pi A B) rewrite weakenCommutesTy' m k A | weakenCommutesTy'' {n = n} m k B = refl
weakenCommutesTy' {n = n} m k uu = refl
weakenCommutesTy' {n = n} m k (el v) rewrite weakenCommutesTm' m k v = refl

weakenCommutesTm'' {n = n} m k A = trFTm n m (n + suc m) k A (n+suc n m) (weakenCommutesTm' (suc m) k (trTmExpr (!R (n+suc n m)) A))

weakenCommutesTm' m k (var x) = ap var (weakenCommutesVar' m k x)
weakenCommutesTm' m k (lam A B u) rewrite weakenCommutesTy' m k A | weakenCommutesTy'' m k B | weakenCommutesTm'' m k u = refl
weakenCommutesTm' m k (app A B f a) rewrite weakenCommutesTy' m k A | weakenCommutesTy'' m k B | weakenCommutesTm' m k f | weakenCommutesTm' m k a = refl

weakenCommutesVar' {n = n} zero k x with n + 0 | n+0 n
... | _ | reflR = refl
weakenCommutesVar' {n = n} (suc m) k x with n + suc m | n+suc n m
... | _ | reflR with x
...   | last = refl
...   | prev x' = ap prev (weakenCommutesVar' m k x')

GTy : (n : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TyExpr {i} n) (p : u ≡R n) → Prop
GTy n u k A p =
  weakenTy' (trFin (apR suc (!R (apR suc p))) last) (weakenTy' (trFin (apR suc (!R p)) k) (trTyExpr (!R p) A)) ≡
  weakenTy' (trFin (apR suc (!R (apR suc p))) (prev k)) (weakenTy' (trFin (apR suc (!R p)) last) (trTyExpr ((!R p)) A))

trGTy : {i : Size} (n : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TyExpr n) (p : u ≡R n) → GTy {i} n u k A p → GTy {i} n n k A reflR
trGTy n u k A reflR x = x

weakenTyCommutes : {n : ℕ} (k : Fin (suc n)) (A : TyExpr n) → weakenTy' last (weakenTy' k A) ≡ weakenTy' (prev k) (weakenTy' last A)
weakenTyCommutes {n = n} k A = trGTy n (n + 0) k A (n+0 n) (weakenCommutesTy' 0 k (trTyExpr (!R (n+0 n)) A))

GTm : (n : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TmExpr {i} n) (p : u ≡R n) → Prop
GTm n u k A p =
  weakenTm' (trFin (apR suc (!R (apR suc p))) last) (weakenTm' (trFin (apR suc (!R p)) k) (trTmExpr (!R p) A)) ≡
  weakenTm' (trFin (apR suc (!R (apR suc p))) (prev k)) (weakenTm' (trFin (apR suc (!R p)) last) (trTmExpr ((!R p)) A))

trGTm : {i : Size} (n : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TmExpr n) (p : u ≡R n) → GTm {i} n u k A p → GTm {i} n n k A reflR
trGTm n u k A reflR x = x

weakenTmCommutes : {n : ℕ} (k : Fin (suc n)) (A : TmExpr n) → weakenTm' last (weakenTm' k A) ≡ weakenTm' (prev k) (weakenTm' last A)
weakenTmCommutes {n = n} k A = trGTm n (n + 0) k A (n+0 n) (weakenCommutesTm' 0 k (trTmExpr (!R (n+0 n)) A))

weakenMorCommutes : (k : Fin (suc n)) (δ : Mor n m) → weakenMor' last (weakenMor' k δ) ≡ weakenMor' (prev k) (weakenMor' last δ)
weakenMorCommutes {m = zero} k ◇ = refl
weakenMorCommutes {m = suc m} k (δ , u) rewrite weakenMorCommutes k δ | weakenTmCommutes k u = refl

-- weakenMor^ : (k : ℕ) (δ : Mor n m) → Mor (k + n) m
-- weakenMor^ k ◇ = ◇
-- weakenMor^ k (δ , u) = (weakenMor^ k δ , {!!})
-- weakenMor^ 0 δ = δ
-- weakenMor^ (suc k) δ = weakenMor (weakenMor^ k δ)

-- trimMor : (k : ℕ) (δ : Mor n (k + m)) → Mor n m
-- trimMor 0 δ = δ
-- trimMor (suc k) (δ , u) = trimMor k δ

-- idMor[]Mor : (k : ℕ) {n m : ℕ} (δ : Mor n (k + m)) → weakenMor^ k (idMor m) [ δ ]Mor ≡ trimMor k δ
-- idMor[]Mor k {m = zero} δ = {!refl!}
-- idMor[]Mor k {m = suc m} δ = {!!}

{- Properties of substitution and weakening -}

weaken[]Ty : (A : TyExpr n) (δ : Mor m n) (k : Fin (suc m)) → weakenTy' k (A [ δ ]Ty) ≡ A [ weakenMor' k δ ]Ty
weaken[]Tm : (u : TmExpr n) (δ : Mor m n) (k : Fin (suc m)) → weakenTm' k (u [ δ ]Tm) ≡ u [ weakenMor' k δ ]Tm

weaken[]Ty (el v) δ k rewrite weaken[]Tm v δ k = refl
weaken[]Ty (pi A B) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor δ , var last) (prev k) | weakenMorCommutes k δ = refl
weaken[]Ty uu δ k = refl

weaken[]Tm (var last) (δ , u) k = refl
weaken[]Tm (var (prev x)) (δ , u) k = weaken[]Tm (var x) δ k
weaken[]Tm (lam A B u) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor δ , var last) (prev k) | weakenMorCommutes k δ | weaken[]Tm u (weakenMor δ , var last) (prev k) = refl
weaken[]Tm (app A B f a) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor δ , var last) (prev k) | weakenMorCommutes k δ | weaken[]Tm f δ k | weaken[]Tm a δ k = refl

idMor : (n : ℕ) → Mor n n
idMor zero = ◇
idMor (suc n) = weakenMor (idMor n) , var last

[idMor]Ty : {n : ℕ} (A : TyExpr n) → A [ idMor n ]Ty ≡ A
[idMor]Tm : {n : ℕ} (u : TmExpr n) → u [ idMor n ]Tm ≡ u

[idMor]Ty uu = refl
[idMor]Ty (pi A B) rewrite [idMor]Ty A | [idMor]Ty B = refl
[idMor]Ty (el v) rewrite [idMor]Tm v = refl

[idMor]Tm {n = zero} (var ())
[idMor]Tm {n = suc n} (var last) = refl
[idMor]Tm {n = suc n} (var (prev x)) = ! (weaken[]Tm (var x) (idMor n) last) ∙ ap weakenTm ([idMor]Tm (var x))
[idMor]Tm (lam A B u) rewrite [idMor]Ty A | [idMor]Ty B | [idMor]Tm u = refl
[idMor]Tm (app A B f a) rewrite [idMor]Ty A | [idMor]Ty B | [idMor]Tm f | [idMor]Tm a = refl

[idMor]Mor : {n m : ℕ} (δ : Mor n m) → δ [ idMor n ]Mor ≡ δ
[idMor]Mor ◇ = refl
[idMor]Mor (δ , u) rewrite [idMor]Mor δ | [idMor]Tm u = refl

postulate
  weakenidMor[]Mor : (δ : Mor m n) (u : TmExpr m) → weakenMor (idMor n) [ δ , u ]Mor ≡ δ
-- weakenidMor[]Mor {zero} ◇ u = refl
-- weakenidMor[]Mor {suc n} (δ , v) u = {!!}

idMor[]Mor : (δ : Mor n m) → idMor m [ δ ]Mor ≡ δ
idMor[]Mor {m = zero} ◇ = refl
idMor[]Mor {m = suc m} (δ , u) rewrite weakenidMor[]Mor δ u = refl

postulate
  lemma   : (δ : Mor n m) (θ : Mor m l) → (weakenMor θ [ weakenMor δ , var last ]Mor) ≡ weakenMor (θ [ δ ]Mor)
  lemmaTy : (δ : Mor n m) (C : TyExpr m) → (weakenTy C [ weakenMor δ , var last ]Ty) ≡ weakenTy (C [ δ ]Ty)
  lemmaTm : (δ : Mor n m) (w : TmExpr m) → (weakenTm w [ weakenMor δ , var last ]Tm) ≡ weakenTm (w [ δ ]Tm)

-- lemma {l = zero} δ ◇ = refl
-- lemma {l = suc l} δ (θ , w) rewrite lemma δ θ | lemmaTm δ w = refl

-- lemmaTy δ (pi A B) rewrite lemmaTy δ A = {! !}
-- lemmaTy δ uu = refl
-- lemmaTy δ (el v) = {!!}

-- lemmaTm δ (var x) = {!!}
-- lemmaTm δ (lam A B u) = {!!}
-- lemmaTm δ (app A B f a) = {!!}

[]Ty-assoc : (δ : Mor n m) (θ : Mor m k) (A : TyExpr k) → A [ θ ]Ty [ δ ]Ty ≡ A [ θ [ δ ]Mor ]Ty
[]Tm-assoc : (δ : Mor n m) (θ : Mor m k) (u : TmExpr k) → u [ θ ]Tm [ δ ]Tm ≡ u [ θ [ δ ]Mor ]Tm

[]Ty-assoc δ θ (pi A B) rewrite []Ty-assoc δ θ A | []Ty-assoc (weakenMor δ , var last) (weakenMor θ , var last) B | lemma δ θ = refl
[]Ty-assoc δ θ uu = refl
[]Ty-assoc δ θ (el v) rewrite []Tm-assoc δ θ v = refl

[]Tm-assoc δ (θ , v) (var last) = refl
[]Tm-assoc δ (θ , v) (var (prev x)) = []Tm-assoc δ θ (var x)
[]Tm-assoc δ θ (lam A B u) rewrite []Ty-assoc δ θ A | []Ty-assoc (weakenMor δ , var last) (weakenMor θ , var last) B | []Tm-assoc (weakenMor δ , var last) (weakenMor θ , var last) u | lemma δ θ = refl
[]Tm-assoc δ θ (app A B f a) rewrite []Ty-assoc δ θ A | []Ty-assoc (weakenMor δ , var last) (weakenMor θ , var last) B | lemma δ θ | []Tm-assoc δ θ f | []Tm-assoc δ θ a = refl

[]Mor-assoc : (δ : Mor n m) (θ : Mor m k) (φ : Mor k l) → φ [ θ ]Mor [ δ ]Mor ≡ φ [ θ [ δ ]Mor ]Mor
[]Mor-assoc δ θ ◇ = refl
[]Mor-assoc δ θ (φ , w) rewrite []Mor-assoc δ θ φ | []Tm-assoc δ θ w = refl
