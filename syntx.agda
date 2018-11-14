{-# OPTIONS --rewriting --allow-unsolved-metas --prop #-}
 
open import common

-- Somehow it doesn’t work to put that in common…
variable
  {i} : Size

{- Syntax of term- and type-expressions, using de Bruijn indices -}

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

weakenCtx : (k : Fin (suc n)) (Γ : Ctx n) (T : TyExpr (n -F' k)) → Ctx (suc n)
weakenCtx last Γ T = Γ , T
weakenCtx {n = zero} (prev ()) ◇ T
weakenCtx (prev k) (Γ , A) T = weakenCtx k Γ T , weakenTy' k A 

idMor : (n : ℕ) → Mor n n
idMor zero = ◇
idMor (suc n) = weakenMor (idMor n) , var last

insertMor : (k : Fin (suc m)) → TmExpr n  → Mor n m → Mor n (suc m)
insertMor last u δ = δ , u
insertMor (prev ()) u ◇ 
insertMor (prev k) u (δ , u') = insertMor k u δ  , u'

weakenCommutesInsert : (k : Fin (suc m)) (l : Fin (suc n)) (u : TmExpr n) (δ : Mor n m) → insertMor k (weakenTm' l u) (weakenMor' l δ) ≡ weakenMor' l (insertMor k u δ)
weakenCommutesInsert last l u ◇ = refl
weakenCommutesInsert (prev ()) l u ◇ 
weakenCommutesInsert last l u (δ , u') = refl
weakenCommutesInsert (prev k) l u (δ , u') rewrite weakenCommutesInsert k l u δ = refl


{- Total substitutions -}

infix 42 _[_]Ty
infix 42 _[_]Tm

_[_]Ty : {n m : ℕ} → TyExpr m → (δ : Mor n m) → TyExpr n
_[_]Tm : {n m : ℕ} → TmExpr m → (δ : Mor n m) → TmExpr n

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

{- Partial substitutions as a special case of total substitutions -}

substTy : TyExpr (suc n) → TmExpr n → TyExpr n
substTm : TmExpr (suc n) → TmExpr n → TmExpr n

substTy A t = A [ idMor _ , t ]Ty
substTm u t = u [ idMor _ , t ]Tm


{- Weakening commutes with weakening -}

-- This is rather technical because the induction hypothesis doesn’t typecheck without a lot of
-- transports everywhere. Additionally, we are using relevant equality here as we need to transport
-- into sets.

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


{- Weakening commutes with total substitution -}

weaken[]Ty : (A : TyExpr n) (δ : Mor m n) (k : Fin (suc m)) → weakenTy' k (A [ δ ]Ty) ≡ A [ weakenMor' k δ ]Ty
weaken[]Tm : (u : TmExpr n) (δ : Mor m n) (k : Fin (suc m)) → weakenTm' k (u [ δ ]Tm) ≡ u [ weakenMor' k δ ]Tm

weaken[]Ty (el v) δ k rewrite weaken[]Tm v δ k = refl
weaken[]Ty (pi A B) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor δ , var last) (prev k) | weakenMorCommutes k δ = refl
weaken[]Ty uu δ k = refl

weaken[]Tm (var last) (δ , u) k = refl
weaken[]Tm (var (prev x)) (δ , u) k = weaken[]Tm (var x) δ k
weaken[]Tm (lam A B u) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor δ , var last) (prev k) | weakenMorCommutes k δ | weaken[]Tm u (weakenMor δ , var last) (prev k) = refl
weaken[]Tm (app A B f a) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor δ , var last) (prev k) | weakenMorCommutes k δ | weaken[]Tm f δ k | weaken[]Tm a δ k = refl

weaken[]Mor : (θ : Mor n k) (δ : Mor m n) (k : Fin (suc m)) → weakenMor' k (θ [ δ ]Mor) ≡ (θ [ weakenMor' k δ ]Mor)

weaken[]Mor ◇ _ k = refl
weaken[]Mor (θ , u) δ k rewrite weaken[]Mor θ δ k | weaken[]Tm u δ k = refl


{- Substituting a morphism where a term is inserted into a type/term/morphism that is weakened at that point does nothing -}

weakenTyInsert' : (k : Fin (suc m)) (A : TyExpr m) (δ : Mor n m) (t : TmExpr n) -> weakenTy' k A [ insertMor k t δ ]Ty ≡ A [ δ ]Ty
weakenTmInsert' : (k : Fin (suc m)) (u : TmExpr m) (δ : Mor n m) (t : TmExpr n) -> weakenTm' k u [ insertMor k t δ ]Tm ≡ u [ δ ]Tm

weakenTyInsert' k (pi A B) δ t rewrite ! (weakenCommutesInsert k last t δ) | weakenTyInsert' (prev k) B (weakenMor' last δ , var last) (weakenTm' last t) | weakenTyInsert' k A δ t = refl
weakenTyInsert' k uu δ t = refl
weakenTyInsert' k (el v) δ t rewrite weakenTmInsert' k v δ t = refl 

weakenTmInsert' last (var x) δ t = refl
weakenTmInsert' (prev k) (var last) (δ , u) t = refl
weakenTmInsert' (prev k) (var (prev x)) (δ , u) t = weakenTmInsert' k (var x) δ t
weakenTmInsert' k (lam A B u) δ t rewrite weakenTyInsert' k A δ t | ! (weakenCommutesInsert k last t δ) | weakenTyInsert' (prev k) B (weakenMor' last δ , var last) (weakenTm' last t) | weakenTmInsert' (prev k) u (weakenMor' last δ , var last) (weakenTm' last t) = refl 
weakenTmInsert' k (app A B f a) δ t rewrite weakenTyInsert' k A δ t | ! (weakenCommutesInsert k last t δ) | weakenTyInsert' (prev k) B (weakenMor' last δ , var last) (weakenTm' last t) | weakenTmInsert' k f δ t | weakenTmInsert' k a δ t = refl 


weakenTyInsert : (A : TyExpr m) (δ : Mor n m) (t : TmExpr n) -> weakenTy A [ δ , t ]Ty ≡ A [ δ ]Ty
weakenTmInsert : (u : TmExpr m) (δ : Mor n m) (t : TmExpr n) -> weakenTm u [ δ , t ]Tm ≡ u [ δ ]Tm

weakenTyInsert A δ t = weakenTyInsert' last A δ t
weakenTmInsert u δ t = weakenTmInsert' last u δ t


weakenMorInsert : (θ : Mor n m) (δ : Mor k n) (t : TmExpr k) ->  weakenMor θ [ δ ,  t ]Mor ≡ θ [ δ ]Mor

weakenMorInsert ◇ _ _ = refl
weakenMorInsert (θ , u) δ t rewrite weakenMorInsert θ δ t | weakenTmInsert u δ t = refl


[weakenMor]Mor : (δ : Mor n m) (θ : Mor m l) → (weakenMor θ [ weakenMor δ , var last ]Mor) ≡ weakenMor (θ [ δ ]Mor)
[weakenMor]Ty  : (δ : Mor n m) (C : TyExpr m) → (weakenTy C [ weakenMor δ , var last ]Ty) ≡ weakenTy (C [ δ ]Ty)
[weakenMor]Tm  : (δ : Mor n m) (w : TmExpr m) → (weakenTm w [ weakenMor δ , var last ]Tm) ≡ weakenTm (w [ δ ]Tm)

[weakenMor]Mor δ θ = weakenMorInsert θ (weakenMor δ) (var last) ∙ ! (weaken[]Mor θ δ last)
[weakenMor]Ty δ C = weakenTyInsert C (weakenMor δ) (var last) ∙ ! (weaken[]Ty C δ last)
[weakenMor]Tm δ w = weakenTmInsert w (weakenMor δ) (var last) ∙ ! (weaken[]Tm w δ last)


{- Substitution by the identity morphism does nothing -}

[idMor]Ty : (A : TyExpr n) → A [ idMor n ]Ty ≡ A
[idMor]Tm : (u : TmExpr n) → u [ idMor n ]Tm ≡ u

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

idMor[]Mor : (δ : Mor n m) → idMor m [ δ ]Mor ≡ δ

idMor[]Mor {m = zero} ◇ = refl
idMor[]Mor {m = suc m} (δ , u) rewrite weakenMorInsert (idMor m) δ u | idMor[]Mor δ  = refl


{- Substitution is associative -}

[]Ty-assoc : (δ : Mor n m) (θ : Mor m k) (A : TyExpr k) → A [ θ ]Ty [ δ ]Ty ≡ A [ θ [ δ ]Mor ]Ty
[]Tm-assoc : (δ : Mor n m) (θ : Mor m k) (u : TmExpr k) → u [ θ ]Tm [ δ ]Tm ≡ u [ θ [ δ ]Mor ]Tm

[]Ty-assoc δ θ (pi A B) rewrite []Ty-assoc δ θ A | []Ty-assoc (weakenMor δ , var last) (weakenMor θ , var last) B | [weakenMor]Mor δ θ = refl
[]Ty-assoc δ θ uu = refl
[]Ty-assoc δ θ (el v) rewrite []Tm-assoc δ θ v = refl

[]Tm-assoc δ (θ , v) (var last) = refl
[]Tm-assoc δ (θ , v) (var (prev x)) = []Tm-assoc δ θ (var x)
[]Tm-assoc δ θ (lam A B u) rewrite []Ty-assoc δ θ A | []Ty-assoc (weakenMor δ , var last) (weakenMor θ , var last) B | []Tm-assoc (weakenMor δ , var last) (weakenMor θ , var last) u | [weakenMor]Mor δ θ = refl
[]Tm-assoc δ θ (app A B f a) rewrite []Ty-assoc δ θ A | []Ty-assoc (weakenMor δ , var last) (weakenMor θ , var last) B | [weakenMor]Mor δ θ | []Tm-assoc δ θ f | []Tm-assoc δ θ a = refl

[]Mor-assoc : (δ : Mor n m) (θ : Mor m k) (φ : Mor k l) → φ [ θ ]Mor [ δ ]Mor ≡ φ [ θ [ δ ]Mor ]Mor
[]Mor-assoc δ θ ◇ = refl
[]Mor-assoc δ θ (φ , w) rewrite []Mor-assoc δ θ φ | []Tm-assoc δ θ w = refl


{- Substituting a weakened term in a weaken type/term is the same as weakening the substitution -}

-- TODO: rewrite with rewrite?
weakenCommutesSubstTy : (k : Fin (suc n)) (B : TyExpr (suc n)) (a : TmExpr n) -> substTy (weakenTy' (prev k) B) (weakenTm' k a) ≡ weakenTy' k (substTy B a)
weakenCommutesSubstTm : (k : Fin (suc n)) (u : TmExpr (suc n)) (a : TmExpr n) -> substTm (weakenTm' (prev k) u) (weakenTm' k a) ≡ weakenTm' k (substTm u a)

weakenCommutesSubstTy k B a = ap (λ z → substTy (weakenTy' (prev k) z) _) (! ([idMor]Ty B)) ∙
                              ap (λ z → substTy z _) (weaken[]Ty B (idMor _) _) ∙
                              []Ty-assoc _ _ B ∙
                              ap (λ z → B [ z [ (weakenMor' last (idMor _) , var last) , weakenTm' _ _ ]Mor , weakenTm' k a ]Ty) (! (weakenMorCommutes _ (idMor _))) ∙
                              ap (λ z → B [ z , weakenTm' _ _ ]Ty) (weakenMorInsert _ _ _ ∙ [idMor]Mor (weakenMor' _ (idMor _))) ∙
                              ! (weaken[]Ty B (idMor _ , _) _)
 
-- TODO: rewrite with rewrite?
weakenCommutesSubstTm k u a = ap (λ z → substTm (weakenTm' (prev k) z) _) (! ([idMor]Tm u)) ∙
                              ap (λ z → substTm z _ ) (weaken[]Tm u (idMor _) _) ∙ 
                              []Tm-assoc ((weakenMor' last (idMor _) , var last) , weakenTm' _ _) (weakenMor' (prev k) (weakenMor' last (idMor _)) , var last) u ∙
                              ap (λ z → u [ z [ (weakenMor' last (idMor _) , var last) , weakenTm' _ _ ]Mor , weakenTm' k a ]Tm) (! (weakenMorCommutes _ (idMor _))) ∙ 
                              ap (λ z → u [ z , weakenTm' _ _ ]Tm) (weakenMorInsert _ _ _ ∙ [idMor]Mor (weakenMor' _ (idMor _))) ∙
                              ! (weaken[]Tm u (idMor _ , _) _)

weakenSubstTy : (A : TyExpr n) (t : TmExpr n) -> substTy (weakenTy A) t ≡ A
weakenSubstTm : (u : TmExpr n) (t : TmExpr n) -> substTm (weakenTm u) t ≡ u

weakenSubstTy A u = weakenTyInsert A (idMor _) u ∙ ([idMor]Ty _)
weakenSubstTm u t = weakenTmInsert u (idMor _) t ∙ ([idMor]Tm _)

{- Total substitution commutes with partial substitution -}

-- TODO: rewrite with rewrite?
substCommutes[]Ty : (B : TyExpr (suc m)) (a : TmExpr m) (δ : Mor n m) → substTy (B [ weakenMor δ , var last ]Ty) (a [ δ ]Tm) ≡ (substTy B a) [ δ ]Ty
substCommutes[]Ty B a δ = []Ty-assoc (idMor _ , (a [ δ ]Tm)) (weakenMor' last δ , var last) B ∙
                          ap (λ z → B [ z , (a [ δ ]Tm) ]Ty) (weakenMorInsert δ (idMor _) (a [ δ ]Tm)) ∙
                          ap (λ z → B [ z , (a [ δ ]Tm) ]Ty) ([idMor]Mor δ) ∙
                          ! ([]Ty-assoc δ (idMor _ , a) B ∙
                            ap (λ z → B [ z , (a [ δ ]Tm) ]Ty) (idMor[]Mor δ))

-- TODO: rewrite with rewrite?
substCommutes[]Tm : (u : TmExpr (suc m)) (a : TmExpr m) (δ : Mor n m) → substTm (u [ weakenMor δ , var last ]Tm) (a [ δ ]Tm) ≡ (substTm u a) [ δ ]Tm
substCommutes[]Tm B a δ = []Tm-assoc (idMor _ , (a [ δ ]Tm)) (weakenMor' last δ , var last) B ∙
                          ap (λ z → B [ z , (a [ δ ]Tm) ]Tm) (weakenMorInsert δ (idMor _) (a [ δ ]Tm)) ∙
                          ap (λ z → B [ z , (a [ δ ]Tm) ]Tm) ([idMor]Mor δ) ∙
                          ! ([]Tm-assoc δ (idMor _ , a) B ∙
                            ap (λ z → B [ z , (a [ δ ]Tm) ]Tm) (idMor[]Mor δ))


