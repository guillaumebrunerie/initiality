{-# OPTIONS --irrelevant-projections --type-in-type --rewriting --allow-unsolved-metas #-}

open import common

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

{- Contexts and context morphisms -}

data Ctx : ℕ → Set where
  ◇ : Ctx 0
  _,_ : {n : ℕ} (Γ : Ctx n) → TyExpr n → Ctx (suc n)

data Mor (n : ℕ) : ℕ → Set where
  ◇ : Mor n 0
  _,_ : {m : ℕ} → Mor n m → TmExpr n → Mor n (suc m)

{- Weakening -}

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
weakenMor' k (δ , u) = (weakenMor' k δ , weakenTm' k u) -- renameMor (injF k)

weakenMor : Mor n m → Mor (suc n) m
weakenMor = weakenMor' last

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

{- Properties of substitution and weakening -}

weaken[]Ty : (A : TyExpr n) (δ : Mor m n) (k : Fin (suc m)) → weakenTy' k (A [ δ ]Ty) ≡ A [ weakenMor' k δ ]Ty
weaken[]Tm : (u : TmExpr n) (δ : Mor m n) (k : Fin (suc m)) → weakenTm' k (u [ δ ]Tm) ≡ u [ weakenMor' k δ ]Tm

weaken[]Ty (pi A B) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor δ , var last) (prev k) = {!refl!}
weaken[]Ty uu δ = λ k₁ → refl
weaken[]Ty (el v) δ = {!!}

weaken[]Tm = {!!}

idMor : (n : ℕ) → Mor n n
idMor zero = ◇
idMor (suc n) = weakenMor (idMor n) , var last

[idMor]Ty : {n : ℕ} (A : TyExpr n) → A [ idMor n ]Ty ≡ A
[idMor]Tm : {n : ℕ} (u : TmExpr n) → u [ idMor n ]Tm ≡ u

[idMor]Ty (pi A B) rewrite [idMor]Ty A | [idMor]Ty B = refl
[idMor]Ty uu = refl
[idMor]Ty (el v) rewrite [idMor]Tm v = refl

[idMor]Tm {zero} (var ())
[idMor]Tm {suc n} (var last) = refl
[idMor]Tm {suc n} (var (prev x)) = ! (weaken[]Tm (var x) (idMor n) last) ∙ ap weakenTm ([idMor]Tm (var x))
[idMor]Tm (lam A B u) rewrite [idMor]Ty A | [idMor]Ty B | [idMor]Tm u = refl
[idMor]Tm (app A B f a) rewrite [idMor]Ty A | [idMor]Ty B | [idMor]Tm f | [idMor]Tm a = refl

[idMor]Mor : {n m : ℕ} (δ : Mor n m) → δ [ idMor n ]Mor ≡ δ
[idMor]Mor ◇ = refl
[idMor]Mor (δ , u) rewrite [idMor]Mor δ | [idMor]Tm u = refl

.weakenidMor[]Mor : (δ : Mor m n) (u : TmExpr m) → weakenMor (idMor n) [ δ , u ]Mor ≡ δ
weakenidMor[]Mor δ u = {!!}

n+0 : (n : ℕ) → n + 0 ≡ n
n+0 0 = refl
n+0 (suc n) rewrite n+0 n = refl

n+suc : (n m : ℕ) → n + suc m ≡ suc (n + m)
n+suc 0 m = refl
n+suc (suc n) m rewrite n+suc n m = refl

prev^ : (m : ℕ) → Fin (suc n) → Fin (suc (n + m))
prev^ {n = n} zero k rewrite n+0 n = k
prev^ {n = n} (suc m) k rewrite n+suc n m = prev (prev^ m k)

trFin : (n ≡ m) → TyExpr n → TyExpr m
trFin refl x = x

weakenCommutes'' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TyExpr (suc (n + m))) → weakenTy' (prev (prev^ {n = suc n} m last)) (weakenTy' (prev (prev^ m k)) A) ≡ weakenTy' (prev (prev^ m (prev k))) (weakenTy' (prev (prev^ m last)) A)
weakenCommutes' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TyExpr (n + m)) → weakenTy' (prev^ {n = suc n} m last) (weakenTy' (prev^ m k) A) ≡ weakenTy' (prev^ m (prev k)) (weakenTy' (prev^ m last) A)

A' : (n m : ℕ) → (A : TyExpr (suc (n + m))) → TyExpr (n + (suc m))
A' n m A rewrite n+suc n m = A

weakenCommutes'' {n = n} m k A rewrite n+suc n m | n+suc (suc n) m = {!weakenCommutes' (suc m) k (A' n m A)!}

weakenCommutes' {n = n} m k (pi A B) rewrite weakenCommutes' m k A | weakenCommutes'' {n = n} m k B = refl
weakenCommutes' m k uu = refl
weakenCommutes' m k (el v) = {!!}

weakenCommutes : {n : ℕ} (k : Fin (suc n)) (A : TyExpr n) → weakenTy' last (weakenTy' k A) ≡ weakenTy' (prev k) (weakenTy' last A)
weakenCommutes k (pi A B) = {!!}
weakenCommutes k uu = refl
weakenCommutes k (el v) = {!!}

-- weakenMor^ : (k : ℕ) (δ : Mor n m) → Mor (k + n) m
-- weakenMor^ k ◇ = ◇
-- weakenMor^ k (δ , u) = (weakenMor^ k δ , {!!})
-- -- weakenMor^ 0 δ = δ
-- -- weakenMor^ (suc k) δ = weakenMor (weakenMor^ k δ)

-- trimMor : (k : ℕ) (δ : Mor n (k + m)) → Mor n m
-- trimMor 0 δ = δ
-- trimMor (suc k) (δ , u) = trimMor k δ

-- idMor[]Mor : (k : ℕ) {n m : ℕ} (δ : Mor n (k + m)) → weakenMor^ k (idMor m) [ δ ]Mor ≡ trimMor k δ
-- idMor[]Mor k {m = zero} δ = {!refl!}
-- idMor[]Mor k {m = suc m} δ = {!!}

idMor[]Mor : (δ : Mor n m) → idMor m [ δ ]Mor ≡ δ
idMor[]Mor δ = {!!}

[]Ty-assoc : (δ : Mor n m) (θ : Mor m k) (A : TyExpr k) → A [ θ ]Ty [ δ ]Ty ≡ A [ θ [ δ ]Mor ]Ty
[]Tm-assoc : (δ : Mor n m) (θ : Mor m k) (u : TmExpr k) → u [ θ ]Tm [ δ ]Tm ≡ u [ θ [ δ ]Mor ]Tm

[]Ty-assoc δ θ A = {!!}

[]Tm-assoc δ (θ , v) (var last) = refl
[]Tm-assoc δ (θ , v) (var (prev x)) = []Tm-assoc δ θ (var x)
[]Tm-assoc δ θ (lam A B u) rewrite []Ty-assoc δ θ A | []Ty-assoc (weakenMor δ , var last) (weakenMor θ , var last) B = {!!}
[]Tm-assoc δ θ (app A B f a) = {!!}

[]Mor-assoc : (δ : Mor n m) (θ : Mor m k) (φ : Mor k l) → φ [ θ ]Mor [ δ ]Mor ≡ φ [ θ [ δ ]Mor ]Mor
[]Mor-assoc δ θ ◇ = refl
[]Mor-assoc δ θ (φ , w) rewrite []Mor-assoc δ θ φ | []Tm-assoc δ θ w = refl
