{-# OPTIONS --rewriting --prop --without-K -v tc.unquote:10 #-}
 
open import common
open import reflection

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
  nat-elim : (P : TyExpr {s} (suc n)) (d0 : TmExpr {s} n) (dS : TmExpr {s} (suc n)) (u : TmExpr {s} n) → TmExpr {↑ s} n

  id : (i : ℕ) (a u v : TmExpr {s} n) → TmExpr {↑ s} n
  refl : (A : TyExpr {s} n) (u : TmExpr {s} n) → TmExpr {↑ s} n
--  jj : (A : TyExpr {s} n) (P : TyExpr {s} (suc (suc (suc n)))) (d : TmExpr {s} (suc n)) (a b p : TmExpr {s} n) → TmExpr {↑ s} n

Ty?Tm : Name → Name → Name → Name
Ty?Tm (quote TyExpr) TyFun TmFun = TyFun
Ty?Tm (quote TmExpr) TyFun TmFun = TmFun
Ty?Tm _ _ _ = quote ERROR

{- Contexts and context morphisms -}

data Ctx : ℕ → Set where
  ◇ : Ctx 0
  _,_ : {n : ℕ} (Γ : Ctx n) (A : TyExpr n) → Ctx (suc n)

data Mor (n : ℕ) : ℕ → Set where
  ◇ : Mor n 0
  _,_ : {m : ℕ} (δ : Mor n m) (u : TmExpr n) → Mor n (suc m)


{- Weakening -}

weakenVar' : (k : Fin (suc n)) → Fin n → Fin (suc n)
weakenVar' last = prev
weakenVar' (prev k) last = last
weakenVar' (prev k) (prev x) = prev (weakenVar' k x)


weakenTm' : (k : Fin (suc n)) → TmExpr n → TmExpr (suc n)
weakenTy' : (k : Fin (suc n)) → TyExpr n → TyExpr (suc n)

weakenTy' k (uu i) = uu i
weakenTy' k (el i v) = el i (weakenTm' k v)
weakenTy' k (pi A B) = pi (weakenTy' k A) (weakenTy' (prev k) B)
weakenTy' k (sig A B) = sig (weakenTy' k A) (weakenTy' (prev k) B)
weakenTy' k nat = nat
weakenTy' k (id A u v) = id (weakenTy' k A) (weakenTm' k u) (weakenTm' k v)

weakenTm' k (var x) = var (weakenVar' k x)
weakenTm' k (uu i) = uu i
weakenTm' k (pi i a b) = pi i (weakenTm' k a) (weakenTm' (prev k) b)
weakenTm' k (lam A B u) = lam (weakenTy' k A) (weakenTy' (prev k) B) (weakenTm' (prev k) u)
weakenTm' k (app A B f a) = app (weakenTy' k A) (weakenTy' (prev k) B)
                                (weakenTm' k f) (weakenTm' k a)
weakenTm' k (sig i a b) = sig i (weakenTm' k a) (weakenTm' (prev k) b)
weakenTm' k (pair A B a b) = pair (weakenTy' k A) (weakenTy' (prev k) B)
                                  (weakenTm' k a) (weakenTm' k b)
weakenTm' k (pr1 A B u) = pr1 (weakenTy' k A) (weakenTy' (prev k) B) (weakenTm' k u)
weakenTm' k (pr2 A B u) = pr2 (weakenTy' k A) (weakenTy' (prev k) B) (weakenTm' k u)
weakenTm' k (nat i) = nat i
weakenTm' k zero = zero
weakenTm' k (suc u) = suc (weakenTm' k u)
weakenTm' k (nat-elim P d0 dS u) = nat-elim (weakenTy' (prev k) P) (weakenTm' k d0)
                                            (weakenTm' (prev k) dS) (weakenTm' k u)
weakenTm' k (id i a u v) = id i (weakenTm' k a) (weakenTm' k u) (weakenTm' k v)
weakenTm' k (refl A u) = refl (weakenTy' k A) (weakenTm' k u)
-- weakenTm' k (jj A P d a b p) = jj (weakenTy' k A) (weakenTy' (prev (prev (prev k))) P)
--                                   (weakenTm' (prev k) d) (weakenTm' k a) (weakenTm' k b)
--                                   (weakenTm' k p)

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

weakenMor+ : Mor n m → Mor (suc n) (suc m)
weakenMor+ δ = weakenMor δ , var last

infix 42 _[_]Ty
infix 42 _[_]Tm

_[_]Ty : {n m : ℕ} → TyExpr m → (δ : Mor n m) → TyExpr n
_[_]Tm : {n m : ℕ} → TmExpr m → (δ : Mor n m) → TmExpr n

uu i [ δ ]Ty = uu i
el i v [ δ ]Ty = el i (v [ δ ]Tm)
pi A B [ δ ]Ty = pi (A [ δ ]Ty) (B [ weakenMor+ δ ]Ty)
sig A B [ δ ]Ty = sig (A [ δ ]Ty) (B [ weakenMor+ δ ]Ty)
nat [ δ ]Ty = nat
id A u v [ δ ]Ty = id (A [ δ ]Ty) (u [ δ ]Tm) (v [ δ ]Tm)

var last [ (δ , u) ]Tm = u
var (prev x) [ (δ , u) ]Tm = var x [ δ ]Tm
uu i [ δ ]Tm = uu i
pi i a b [ δ ]Tm = pi i (a [ δ ]Tm) (b [ weakenMor+ δ ]Tm)
lam A B u [ δ ]Tm = lam (A [ δ ]Ty) (B [ weakenMor+ δ ]Ty) (u [ weakenMor+ δ ]Tm)
app A B f a [ δ ]Tm = app (A [ δ ]Ty) (B [ weakenMor+ δ ]Ty) (f [ δ ]Tm) (a [ δ ]Tm)
sig i a b [ δ ]Tm = sig i (a [ δ ]Tm) (b [ weakenMor+ δ ]Tm)
pair A B a b [ δ ]Tm = pair (A [ δ ]Ty) (B [ weakenMor+ δ ]Ty) (a [ δ ]Tm) (b [ δ ]Tm)
pr1 A B u [ δ ]Tm = pr1 (A [ δ ]Ty) (B [ weakenMor+ δ ]Ty) (u [ δ ]Tm)
pr2 A B u [ δ ]Tm = pr2 (A [ δ ]Ty) (B [ weakenMor+ δ ]Ty) (u [ δ ]Tm)
nat i [ δ ]Tm = nat i
zero [ δ ]Tm = zero
suc u [ δ ]Tm = suc (u [ δ ]Tm)
nat-elim P d0 dS u [ δ ]Tm = nat-elim (P [ weakenMor+ δ ]Ty) (d0 [ δ ]Tm) (dS [ weakenMor+ δ ]Tm)
                                      (u [ δ ]Tm)
id i a u v [ δ ]Tm = id i (a [ δ ]Tm) (u [ δ ]Tm) (v [ δ ]Tm)
refl A u [ δ ]Tm = refl (A [ δ ]Ty) (u [ δ ]Tm)
-- jj A P d a b p [ δ ]Tm = jj (A [ δ ]Ty) (P [ weakenMor+ (weakenMor+ (weakenMor+ δ)) ]Ty)
--                             (d [ weakenMor+ δ ]Tm) (a [ δ ]Tm) (b [ δ ]Tm) (p [ δ ]Tm)

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

trTyExpr : (n ≡R m) → TyExpr {s} n → TyExpr {s} m
trTyExpr reflR x = x

FTy : (n m u : ℕ) (k : Fin (suc n)) (A : TyExpr {s} (suc (n + m))) (p : u ≡R suc (n + m)) → Prop
FTy n m u k A p =
  weakenTy' (trFin (apR suc (!R (apR suc p))) (prev (prev^ m last)))
            (weakenTy' (trFin (apR suc (!R p)) (prev (prev^ m k))) (trTyExpr (!R p) A)) ≡
  weakenTy' (trFin (apR suc (!R (apR suc p))) (prev (prev^ m (prev k))))
            (weakenTy' (trFin (apR suc (!R p)) (prev (prev^ m last))) (trTyExpr ((!R p)) A))

trFTy : (n m u : ℕ) (k : Fin (suc n)) (A : TyExpr {s} (suc (n + m))) (p : u ≡R suc (n + m))
      → FTy {s} n m u k A p → FTy {s} n m (suc (n + m)) k A reflR
trFTy n m u k A reflR x = x

trTmExpr : (n ≡R m) → TmExpr {s} n → TmExpr {s} m
trTmExpr reflR x = x

FTm : (n m u : ℕ) (k : Fin (suc n)) (A : TmExpr {s} (suc (n + m))) (p : u ≡R suc (n + m)) → Prop
FTm n m u k A p =
  weakenTm' (trFin (apR suc (!R (apR suc p))) (prev (prev^ m last)))
            (weakenTm' (trFin (apR suc (!R p)) (prev (prev^ m k))) (trTmExpr (!R p) A)) ≡
  weakenTm' (trFin (apR suc (!R (apR suc p))) (prev (prev^ m (prev k))))
            (weakenTm' (trFin (apR suc (!R p)) (prev (prev^ m last))) (trTmExpr ((!R p)) A))

trFTm : (n m u : ℕ) (k : Fin (suc n)) (A : TmExpr {s} (suc (n + m))) (p : u ≡R suc (n + m))
      → FTm {s} n m u k A p → FTm {s} n m (suc (n + m)) k A reflR
trFTm n m u k A reflR x = x

FVar : (n m u : ℕ) (k : Fin (suc n)) (A : Fin (suc (n + m))) (p : u ≡R suc (n + m)) → Prop
FVar n m u k A p =
  weakenVar' (trFin (apR suc (!R (apR suc p))) (prev (prev^ m last)))
             (weakenVar' (trFin (apR suc (!R p)) (prev (prev^ m k))) (trFin (!R p) A)) ≡
  weakenVar' (trFin (apR suc (!R (apR suc p))) (prev (prev^ m (prev k))))
             (weakenVar' (trFin (apR suc (!R p)) (prev (prev^ m last))) (trFin ((!R p)) A))

trFVar : (n m u : ℕ) (k : Fin (suc n)) (A : Fin (suc (n + m))) (p : u ≡R suc (n + m))
       → FVar n m u k A p → FVar n m (suc (n + m)) k A reflR
trFVar n m u k A reflR x = x


weakenCommutesTy' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TyExpr {s} (n + m))
                  → weakenTy' (prev^ m last) (weakenTy' (prev^ m k) A)
                  ≡ weakenTy' (prev^ m (prev k)) (weakenTy' (prev^ m last) A)
weakenCommutesTy+' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TyExpr {s} (suc (n + m)))
                   → FTy n m (suc (n + m)) k A reflR
-- weakenCommutesTy+++' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TyExpr {s} (suc (suc (suc (n + m)))))
--                    → FTy ? ? (suc (suc (suc (n + m)))) k A reflR

weakenCommutesTm+' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TmExpr {s} (suc (n + m)))
                   → FTm n m (suc (n + m)) k A reflR
weakenCommutesTm' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TmExpr {s} (n + m))
                  → weakenTm' (prev^ m last) (weakenTm' (prev^ m k) A)
                  ≡ weakenTm' (prev^ m (prev k)) (weakenTm' (prev^ m last) A)

weakenCommutesVar' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : Fin (n + m))
                   → weakenVar' (prev^ m last) (weakenVar' (prev^ m k) A)
                   ≡ weakenVar' (prev^ m (prev k)) (weakenVar' (prev^ m last) A)


-- weakenCommutesTy+++' {n = n} m k A =
--   trFTy n m (n + suc m) k A (n+suc n m) (weakenCommutesTy' (suc (suc (suc m))) k (trTyExpr (!R (n+suc n m)) A))

weakenCommutesTy+' {n = n} m k A =
  trFTy n m (n + suc m) k A (n+suc n m) (weakenCommutesTy' (suc m) k (trTyExpr (!R (n+suc n m)) A))

weakenCommutesTy' m k (uu i) = refl
weakenCommutesTy' m k (el i v) rewrite weakenCommutesTm' m k v = refl
weakenCommutesTy' m k (pi A B) rewrite weakenCommutesTy' m k A
                                     | weakenCommutesTy+' m k B = refl
weakenCommutesTy' m k (sig A B) rewrite weakenCommutesTy' m k A
                                      | weakenCommutesTy+' m k B = refl
weakenCommutesTy' m k nat = refl
weakenCommutesTy' m k (id A u v) rewrite weakenCommutesTy' m k A
                                       | weakenCommutesTm' m k u
                                       | weakenCommutesTm' m k v = refl

weakenCommutesTm+' {n = n} m k A =
  trFTm n m (n + suc m) k A (n+suc n m) (weakenCommutesTm' (suc m) k (trTmExpr (!R (n+suc n m)) A))

weakenCommutesTm' m k (var x) rewrite weakenCommutesVar' m k x = refl
weakenCommutesTm' m k (uu i) = refl
weakenCommutesTm' m k (pi i a b)
  rewrite weakenCommutesTm' m k a
        | weakenCommutesTm+' m k b
  = refl
weakenCommutesTm' m k (lam A B u)
  rewrite weakenCommutesTy' m k A
        | weakenCommutesTy+' m k B
        | weakenCommutesTm+' m k u
  = refl
weakenCommutesTm' m k (app A B f a)
  rewrite weakenCommutesTy' m k A
        | weakenCommutesTy+' m k B
        | weakenCommutesTm' m k f
        | weakenCommutesTm' m k a
  = refl
weakenCommutesTm' m k (sig i a b)
  rewrite weakenCommutesTm' m k a
        | weakenCommutesTm+' m k b
  = refl
weakenCommutesTm' m k (pair A B a b)
  rewrite weakenCommutesTy' m k A
        | weakenCommutesTy+' m k B
        | weakenCommutesTm' m k a
        | weakenCommutesTm' m k b
  = refl
weakenCommutesTm' m k (pr1 A B u)
  rewrite weakenCommutesTy' m k A
        | weakenCommutesTy+' m k B
        | weakenCommutesTm' m k u
  = refl
weakenCommutesTm' m k (pr2 A B u)
  rewrite weakenCommutesTy' m k A
        | weakenCommutesTy+' m k B
        | weakenCommutesTm' m k u
  = refl
weakenCommutesTm' m k (nat i) = refl
weakenCommutesTm' m k zero = refl
weakenCommutesTm' m k (suc u)
  rewrite weakenCommutesTm' m k u
  = refl
weakenCommutesTm' m k (nat-elim P d0 dS u)
  rewrite weakenCommutesTy+' m k P
        | weakenCommutesTm' m k d0
        | weakenCommutesTm+' m k dS
        | weakenCommutesTm' m k u
  = refl
weakenCommutesTm' m k (id i a u v)
  rewrite weakenCommutesTm' m k a
        | weakenCommutesTm' m k u
        | weakenCommutesTm' m k v
  = refl
weakenCommutesTm' m k (refl A u)
  rewrite weakenCommutesTy' m k A
        | weakenCommutesTm' m k u
  = refl
-- weakenCommutesTm' m k (jj A P d a b p)
--   rewrite weakenCommutesTy' m k A
-- --        | {!weakenCommutesTy+++' m k P!}
--         | weakenCommutesTm+' m k d
--         | weakenCommutesTm' m k a
--         | weakenCommutesTm' m k b
--         | weakenCommutesTm' m k p
--   = {!weakenCommutesTy' m (prev (prev (prev k))) P!}

weakenCommutesVar' {n = n} zero k x with n + 0 | n+0 n
... | _ | reflR = refl
weakenCommutesVar' {n = n} (suc m) k x with n + suc m | n+suc n m
... | _ | reflR with x
...   | last = refl
...   | prev x' = ap prev (weakenCommutesVar' m k x')


GTy : (n : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TyExpr {s} n) (p : u ≡R n) → Prop
GTy n u k A p =
  weakenTy' (trFin (apR suc (!R (apR suc p))) last) (weakenTy' (trFin (apR suc (!R p)) k) (trTyExpr (!R p) A)) ≡
  weakenTy' (trFin (apR suc (!R (apR suc p))) (prev k)) (weakenTy' (trFin (apR suc (!R p)) last) (trTyExpr ((!R p)) A))

trGTy : {s : Size} (n : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TyExpr n) (p : u ≡R n) → GTy {s} n u k A p → GTy {s} n n k A reflR
trGTy n u k A reflR x = x

weakenTyCommutes : {n : ℕ} (k : Fin (suc n)) (A : TyExpr n) → weakenTy' last (weakenTy' k A) ≡ weakenTy' (prev k) (weakenTy' last A)
weakenTyCommutes {n = n} k A = trGTy n (n + 0) k A (n+0 n) (weakenCommutesTy' 0 k (trTyExpr (!R (n+0 n)) A))

GTm : (n : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TmExpr {s} n) (p : u ≡R n) → Prop
GTm n u k A p =
  weakenTm' (trFin (apR suc (!R (apR suc p))) last) (weakenTm' (trFin (apR suc (!R p)) k) (trTmExpr (!R p) A)) ≡
  weakenTm' (trFin (apR suc (!R (apR suc p))) (prev k)) (weakenTm' (trFin (apR suc (!R p)) last) (trTmExpr ((!R p)) A))

trGTm : {s : Size} (n : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TmExpr n) (p : u ≡R n) → GTm {s} n u k A p → GTm {s} n n k A reflR
trGTm n u k A reflR x = x

weakenTmCommutes : {n : ℕ} (k : Fin (suc n)) (A : TmExpr n) → weakenTm' last (weakenTm' k A) ≡ weakenTm' (prev k) (weakenTm' last A)
weakenTmCommutes {n = n} k A = trGTm n (n + 0) k A (n+0 n) (weakenCommutesTm' 0 k (trTmExpr (!R (n+0 n)) A))

weakenMorCommutes : (k : Fin (suc n)) (δ : Mor n m) → weakenMor' last (weakenMor' k δ) ≡ weakenMor' (prev k) (weakenMor' last δ)
weakenMorCommutes {m = zero} k ◇ = refl
weakenMorCommutes {m = suc m} k (δ , u) rewrite weakenMorCommutes k δ | weakenTmCommutes k u = refl


{- Weakening commutes with total substitution -}

weaken[]Ty : (A : TyExpr n) (δ : Mor m n) (k : Fin (suc m)) → weakenTy' k (A [ δ ]Ty) ≡ A [ weakenMor' k δ ]Ty
weaken[]Tm : (u : TmExpr n) (δ : Mor m n) (k : Fin (suc m)) → weakenTm' k (u [ δ ]Tm) ≡ u [ weakenMor' k δ ]Tm

weaken[]Ty (uu i) δ k = refl
weaken[]Ty (el i v) δ k rewrite weaken[]Tm v δ k = refl
weaken[]Ty (pi A B) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor+ δ) (prev k) | weakenMorCommutes k δ = refl
weaken[]Ty (sig A B) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor+ δ) (prev k) | weakenMorCommutes k δ = refl
weaken[]Ty nat δ k = refl
weaken[]Ty (id A u v) δ k rewrite weaken[]Ty A δ k | weaken[]Tm u δ k | weaken[]Tm v δ k = refl -- weakenMorCommutes k δ = refl

weaken[]Tm (var last) (δ , u) k = refl
weaken[]Tm (var (prev x)) (δ , u) k = weaken[]Tm (var x) δ k
weaken[]Tm (uu i) δ k = refl
weaken[]Tm (pi i a b) δ k rewrite weaken[]Tm a δ k | weaken[]Tm b (weakenMor+ δ) (prev k) | weakenMorCommutes k δ = refl
weaken[]Tm (lam A B u) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor+ δ) (prev k) | weakenMorCommutes k δ | weaken[]Tm u (weakenMor+ δ) (prev k) = refl
weaken[]Tm (app A B f a) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor+ δ) (prev k) | weakenMorCommutes k δ | weaken[]Tm f δ k | weaken[]Tm a δ k = refl
weaken[]Tm (sig i a b) δ k rewrite weaken[]Tm a δ k | weaken[]Tm b (weakenMor+ δ) (prev k) | weakenMorCommutes k δ = refl
weaken[]Tm (pair A B a b) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor+ δ) (prev k) | weakenMorCommutes k δ | weaken[]Tm a δ k | weaken[]Tm b δ k = refl
weaken[]Tm (pr1 A B u) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor+ δ) (prev k) | weakenMorCommutes k δ | weaken[]Tm u δ k = refl
weaken[]Tm (pr2 A B u) δ k rewrite weaken[]Ty A δ k | weaken[]Ty B (weakenMor+ δ) (prev k) | weakenMorCommutes k δ | weaken[]Tm u δ k = refl
weaken[]Tm (nat i) δ k = refl
weaken[]Tm (zero) δ k = refl
weaken[]Tm (suc u) δ k rewrite weaken[]Tm u δ k = refl
weaken[]Tm (nat-elim P d0 dS u) δ k rewrite weaken[]Ty P (weakenMor+ δ) (prev k) | weaken[]Tm d0 δ k | weaken[]Tm dS (weakenMor+ δ) (prev k) | weaken[]Tm u δ k | weakenMorCommutes k δ = refl
weaken[]Tm (id i a u v) δ k rewrite weaken[]Tm a δ k | weaken[]Tm u δ k | weaken[]Tm v δ k = refl
weaken[]Tm (refl A u) δ k rewrite weaken[]Ty A δ k | weaken[]Tm u δ k = refl
--weaken[]Tm (jj A P d a b p) δ k rewrite weaken[]Ty A δ k | weaken[]

weaken[]Mor : (θ : Mor n k) (δ : Mor m n) (k : Fin (suc m)) → weakenMor' k (θ [ δ ]Mor) ≡ (θ [ weakenMor' k δ ]Mor)

weaken[]Mor ◇ _ k = refl
weaken[]Mor (θ , u) δ k rewrite weaken[]Mor θ δ k | weaken[]Tm u δ k = refl


{- Substituting a morphism where a term is inserted into a type/term/morphism that is weakened at that point does nothing -}

weakenTyInsert' : (k : Fin (suc m)) (A : TyExpr m) (δ : Mor n m) (t : TmExpr n) -> weakenTy' k A [ insertMor k t δ ]Ty ≡ A [ δ ]Ty
weakenTmInsert' : (k : Fin (suc m)) (u : TmExpr m) (δ : Mor n m) (t : TmExpr n) -> weakenTm' k u [ insertMor k t δ ]Tm ≡ u [ δ ]Tm

weakenTyInsert' k (uu i) δ t = refl
weakenTyInsert' k (el i v) δ t rewrite weakenTmInsert' k v δ t = refl 
weakenTyInsert' k (pi A B) δ t rewrite ! (weakenCommutesInsert k last t δ) | weakenTyInsert' (prev k) B (weakenMor+ δ) (weakenTm t) | weakenTyInsert' k A δ t = refl
weakenTyInsert' k (sig A B) δ t rewrite ! (weakenCommutesInsert k last t δ) | weakenTyInsert' (prev k) B (weakenMor+ δ) (weakenTm t) | weakenTyInsert' k A δ t = refl
weakenTyInsert' k nat δ t = refl
weakenTyInsert' k (id A u v) δ t rewrite weakenTyInsert' k A δ t | weakenTmInsert' k u δ t | weakenTmInsert' k v δ t = refl

weakenTmInsert' last (var x) δ t = refl
weakenTmInsert' (prev k) (var last) (δ , u) t = refl
weakenTmInsert' (prev k) (var (prev x)) (δ , u) t = weakenTmInsert' k (var x) δ t
weakenTmInsert' k (uu i) δ t = refl
weakenTmInsert' k (pi i a b) δ t rewrite ! (weakenCommutesInsert k last t δ) | weakenTmInsert' k a δ t | weakenTmInsert' (prev k) b (weakenMor+ δ) (weakenTm t) = refl
weakenTmInsert' k (lam A B u) δ t rewrite ! (weakenCommutesInsert k last t δ) | weakenTyInsert' k A δ t | weakenTyInsert' (prev k) B (weakenMor+ δ) (weakenTm t) | weakenTmInsert' (prev k) u (weakenMor+ δ) (weakenTm t) = refl
weakenTmInsert' k (app A B f a) δ t rewrite ! (weakenCommutesInsert k last t δ) | weakenTyInsert' k A δ t | weakenTyInsert' (prev k) B (weakenMor+ δ) (weakenTm t) | weakenTmInsert' k f δ t | weakenTmInsert' k a δ t = refl 
weakenTmInsert' k (sig i a b) δ t rewrite ! (weakenCommutesInsert k last t δ) | weakenTmInsert' k a δ t | weakenTmInsert' (prev k) b (weakenMor+ δ) (weakenTm t) = refl
weakenTmInsert' k (pair A B a b) δ t rewrite ! (weakenCommutesInsert k last t δ) | weakenTyInsert' k A δ t | weakenTyInsert' (prev k) B (weakenMor+ δ) (weakenTm t) | weakenTmInsert' k a δ t | weakenTmInsert' k b δ t = refl
weakenTmInsert' k (pr1 A B u) δ t rewrite ! (weakenCommutesInsert k last t δ) | weakenTyInsert' k A δ t | weakenTyInsert' (prev k) B (weakenMor+ δ) (weakenTm t) | weakenTmInsert' k u δ t = refl
weakenTmInsert' k (pr2 A B u) δ t rewrite ! (weakenCommutesInsert k last t δ) | weakenTyInsert' k A δ t | weakenTyInsert' (prev k) B (weakenMor+ δ) (weakenTm t) | weakenTmInsert' k u δ t = refl
weakenTmInsert' k (nat i) δ t = refl
weakenTmInsert' k zero δ t = refl
weakenTmInsert' k (suc u) δ t rewrite weakenTmInsert' k u δ t = refl
weakenTmInsert' k (nat-elim P d0 dS u) δ t rewrite ! (weakenCommutesInsert k last t δ) | weakenTyInsert' (prev k) P (weakenMor+ δ) (weakenTm t) | weakenTmInsert' k d0 δ t | weakenTmInsert' (prev k) dS (weakenMor+ δ) (weakenTm t) | weakenTmInsert' k u δ t = refl
weakenTmInsert' k (id i a u v) δ t rewrite weakenTmInsert' k a δ t | weakenTmInsert' k u δ t | weakenTmInsert' k v δ t = refl
weakenTmInsert' k (refl A u) δ t rewrite weakenTyInsert' k A δ t | weakenTmInsert' k u δ t = refl
--weakenTmInsert' k (jj …) δ t = ?


weakenTyInsert : (A : TyExpr m) (δ : Mor n m) (t : TmExpr n) -> weakenTy A [ δ , t ]Ty ≡ A [ δ ]Ty
weakenTyInsert A δ t = weakenTyInsert' last A δ t

weakenTmInsert : (u : TmExpr m) (δ : Mor n m) (t : TmExpr n) -> weakenTm u [ δ , t ]Tm ≡ u [ δ ]Tm
weakenTmInsert u δ t = weakenTmInsert' last u δ t



weakenMorInsert : (θ : Mor n m) (δ : Mor k n) (t : TmExpr k) ->  weakenMor θ [ δ ,  t ]Mor ≡ θ [ δ ]Mor
weakenMorInsert ◇ _ _ = refl
weakenMorInsert (θ , u) δ t rewrite weakenMorInsert θ δ t | weakenTmInsert u δ t = refl


[weakenMor]Mor : (δ : Mor n m) (θ : Mor m l) → (weakenMor θ [ weakenMor+ δ ]Mor) ≡ weakenMor (θ [ δ ]Mor)
[weakenMor]Ty  : (δ : Mor n m) (C : TyExpr m) → (weakenTy C [ weakenMor+ δ ]Ty) ≡ weakenTy (C [ δ ]Ty)
[weakenMor]Tm  : (δ : Mor n m) (w : TmExpr m) → (weakenTm w [ weakenMor+ δ ]Tm) ≡ weakenTm (w [ δ ]Tm)

[weakenMor]Mor δ θ = weakenMorInsert θ (weakenMor δ) (var last) ∙ ! (weaken[]Mor θ δ last)
[weakenMor]Ty δ C = weakenTyInsert C (weakenMor δ) (var last) ∙ ! (weaken[]Ty C δ last)
[weakenMor]Tm δ w = weakenTmInsert w (weakenMor δ) (var last) ∙ ! (weaken[]Tm w δ last)

[weakenMor+]MorTy : (B : TyExpr (suc l)) {δ : Mor n m} {θ : Mor m l} → B [ weakenMor+ θ [ weakenMor+ δ ]Mor ]Ty ≡ B [ weakenMor+ (θ [ δ ]Mor) ]Ty
[weakenMor+]MorTy B = ap (λ z → B [ z , var last ]Ty) ([weakenMor]Mor _ _)

[weakenMor+]MorTm : (u : TmExpr (suc l)) {δ : Mor n m} {θ : Mor m l} → u [ weakenMor+ θ [ weakenMor+ δ ]Mor ]Tm ≡ u [ weakenMor+ (θ [ δ ]Mor) ]Tm
[weakenMor+]MorTm u = ap (λ z → u [ z , var last ]Tm) ([weakenMor]Mor _ _)

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
  def (quote _≡_) (earg (con s (iarg (var (half n * 3 + 1) []) ∷ iarg (var (half n * 3) []) ∷ make-args 2 n))
                 ∷ earg (con s (iarg (var (half n * 3 + 1) []) ∷ iarg (var (half n * 3) []) ∷ make-args 1 n)) ∷ [])  where

    make-args : ℕ → ℕ → List (Arg Term)
    make-args k zero = []
    make-args k (suc zero) = []
    make-args k (suc (suc n)) = earg (var (half n * 3 + k) []) ∷ make-args k n

generate-pattern : Type → List (Arg Pattern)
generate-pattern (pi _ (abs _ B)) = earg (con (quote _≡_.refl) []) ∷ generate-pattern B
generate-pattern _ = []

generate-ap : Name → Name → TC ⊤
generate-ap s res = do
  pi A (abs x (pi B (abs y ts))) ← getType s
    where _ → typeError (strErr "not a Pi" ∷ [])
  _ ← declareDef (earg res) (pi A (abs x (pi B (abs y (generate-type 0 s ts)))))
  _ ← defineFun res (clause (generate-pattern ts) (con (quote _≡_.refl) []) ∷ [])
  return _

unquoteDecl ap-uu-Ty = generate-ap (quote TyExpr.uu) ap-uu-Ty
unquoteDecl ap-el-Ty = generate-ap (quote TyExpr.el) ap-el-Ty
unquoteDecl ap-pi-Ty = generate-ap (quote TyExpr.pi) ap-pi-Ty
unquoteDecl ap-sig-Ty = generate-ap (quote TyExpr.sig) ap-sig-Ty
unquoteDecl ap-id-Ty = generate-ap (quote TyExpr.id) ap-id-Ty
unquoteDecl ap-nat-Ty = generate-ap (quote TyExpr.nat) ap-nat-Ty

unquoteDecl ap-var-Tm = generate-ap (quote TmExpr.var) ap-var-Tm
unquoteDecl ap-uu-Tm = generate-ap (quote TmExpr.uu) ap-uu-Tm
unquoteDecl ap-pi-Tm = generate-ap (quote TmExpr.pi) ap-pi-Tm
unquoteDecl ap-lam-Tm = generate-ap (quote TmExpr.lam) ap-lam-Tm
unquoteDecl ap-app-Tm = generate-ap (quote TmExpr.app) ap-app-Tm
unquoteDecl ap-sig-Tm = generate-ap (quote TmExpr.sig) ap-sig-Tm
unquoteDecl ap-pair-Tm = generate-ap (quote TmExpr.pair) ap-pair-Tm
unquoteDecl ap-pr1-Tm = generate-ap (quote TmExpr.pr1) ap-pr1-Tm
unquoteDecl ap-pr2-Tm = generate-ap (quote TmExpr.pr2) ap-pr2-Tm
unquoteDecl ap-nat-Tm = generate-ap (quote TmExpr.nat) ap-nat-Tm
unquoteDecl ap-zero-Tm = generate-ap (quote TmExpr.zero) ap-zero-Tm
unquoteDecl ap-suc-Tm = generate-ap (quote TmExpr.suc) ap-suc-Tm
unquoteDecl ap-nat-elim-Tm = generate-ap (quote TmExpr.nat-elim) ap-nat-elim-Tm
unquoteDecl ap-id-Tm = generate-ap (quote TmExpr.id) ap-id-Tm
unquoteDecl ap-refl-Tm = generate-ap (quote TmExpr.refl) ap-refl-Tm
--unquoteDecl ap-jj-Tm = generate-ap (quote TmExpr.jj) ap-jj-Tm

corresponding-ap : List (Name ×R Name)
corresponding-ap =
  (quote TyExpr.uu , quote ap-uu-Ty) ∷
  (quote TyExpr.el , quote ap-el-Ty) ∷
  (quote TyExpr.pi , quote ap-pi-Ty) ∷
  (quote TyExpr.sig , quote ap-sig-Ty) ∷
  (quote TyExpr.id , quote ap-id-Ty) ∷
  (quote TyExpr.nat , quote ap-nat-Ty) ∷
  (quote TmExpr.var , quote ap-var-Tm) ∷
  (quote TmExpr.uu , quote ap-uu-Tm) ∷
  (quote TmExpr.pi , quote ap-pi-Tm) ∷
  (quote TmExpr.lam , quote ap-lam-Tm) ∷
  (quote TmExpr.app , quote ap-app-Tm) ∷
  (quote TmExpr.sig , quote ap-sig-Tm) ∷
  (quote TmExpr.pair , quote ap-pair-Tm) ∷
  (quote TmExpr.pr1 , quote ap-pr1-Tm) ∷
  (quote TmExpr.pr2 , quote ap-pr2-Tm) ∷
  (quote TmExpr.nat , quote ap-nat-Tm) ∷
  (quote TmExpr.zero , quote ap-zero-Tm) ∷
  (quote TmExpr.suc , quote ap-suc-Tm) ∷
  (quote TmExpr.nat-elim , quote ap-nat-elim-Tm) ∷
  (quote TmExpr.id , quote ap-id-Tm) ∷
  (quote TmExpr.refl , quote ap-refl-Tm) ∷ []
  -- (quote TmExpr.jj , quote ap-jj-Tm) ∷ []


{- Substitution by the identity morphism does nothing -}

generate-[idMor] : Name → Name → Name → TC ⊤
generate-[idMor] [idMor]Ty [idMor]Tm [idMor]Var = (do
  data-type _ consTy ← getDefinition (quote TyExpr)
    where _ → typeError (strErr "TyExpr is not a datatype." ∷ [])
  clausesTy ← mapTC constructClause-[idMor] consTy
  _ ← defineFun [idMor]Ty clausesTy

  data-type _ consTm ← getDefinition (quote TmExpr)
    where _ → typeError (strErr "TmExpr is not a datatype." ∷ [])
  clausesTm ← mapTC constructClause-[idMor] consTm
  _ ← defineFun [idMor]Tm clausesTm
  return _)

   where

    constructPattern-[idMor] : Type → List (Arg Pattern)
    constructPattern-[idMor] (pi (arg i _) (abs s B)) =
      arg i (var s) ∷ constructPattern-[idMor] B
    constructPattern-[idMor] A = []

    make-args : ℕ → Type → List (Arg Term)
    make-args n (pi (arg i (def (quote TyExpr) _)) (abs s B)) =
      earg (def [idMor]Ty (earg (var n []) ∷ [])) ∷ make-args (n - 1) B
    make-args n (pi (arg i (def (quote TmExpr) _)) (abs s B)) =
      earg (def [idMor]Tm (earg (var n []) ∷ [])) ∷ make-args (n - 1) B
    make-args n (pi (arg (arg-info visible _) _) (abs s B)) =
      earg (con (quote _≡_.refl) []) ∷ make-args (n - 1) B
    make-args n (pi _ (abs s B)) = make-args (n - 1) B
    make-args n _ = []

    constructClause-[idMor] : Name → TC Clause
    constructClause-[idMor] c = do
      pi _ (abs _ tyC) ← getType c
        where _ → typeError (strErr "The constructor should have [n] as a first implicit argument" ∷ [])
      let result = if primQNameEquality c (quote TmExpr.var) then
                     (def [idMor]Var (earg (var 0 []) ∷ []))
                   else
                     (def (lookup corresponding-ap c) (make-args (getNumberOfPi tyC - 1) tyC))
      return (clause (earg (con c (constructPattern-[idMor] tyC)) ∷ [])
                     result)

[idMor]Ty : (A : TyExpr n) → A [ idMor n ]Ty ≡ A
[idMor]Tm : (u : TmExpr n) → u [ idMor n ]Tm ≡ u
[idMor]Var : (x : Fin n) → (var x) [ idMor n ]Tm ≡ var x

[idMor]Var {n = zero} ()
[idMor]Var {n = suc n} last = refl
[idMor]Var {n = suc n} (prev x) = ! (weaken[]Tm (var x) (idMor n) last) ∙ ap weakenTm ([idMor]Var x)

unquoteDef [idMor]Ty [idMor]Tm = generate-[idMor] [idMor]Ty [idMor]Tm (quote [idMor]Var)

[idMor]Mor : {n m : ℕ} (δ : Mor n m) → δ [ idMor n ]Mor ≡ δ
[idMor]Mor ◇ = refl
[idMor]Mor (δ , u) rewrite [idMor]Mor δ | [idMor]Tm u = refl

idMor[]Mor : (δ : Mor n m) → idMor m [ δ ]Mor ≡ δ

idMor[]Mor {m = zero} ◇ = refl
idMor[]Mor {m = suc m} (δ , u) rewrite weakenMorInsert (idMor m) δ u | idMor[]Mor δ  = refl


{- Substitution is associative -}

generate-assoc : Name → Name → Name → TC ⊤
generate-assoc assocTy assocTm assocVar = (do
  data-type _ consTy ← getDefinition (quote TyExpr)
    where _ → typeError (strErr "TyExpr is not a datatype." ∷ [])
  clausesTy ← mapTC constructClause-assoc consTy
  _ ← defineFun assocTy clausesTy

  data-type _ consTm ← getDefinition (quote TmExpr)
    where _ → typeError (strErr "TmExpr is not a datatype." ∷ [])
  clausesTm ← mapTC constructClause-assoc consTm
  _ ← defineFun assocTm clausesTm
  return _)

   where

    constructPattern-assoc : Type → List (Arg Pattern)
    constructPattern-assoc (pi (arg i _) (abs s B)) =
      arg i (var s) ∷ constructPattern-assoc B
    constructPattern-assoc A = []

    depth : Arg Term → ℕ
    depth (arg _ (con _ (n ∷ _))) = suc (depth n)
    depth _ = zero

    make-args : Arg Term → Arg Term → ℕ → Type → List (Arg Term)
    make-args δ θ n (pi (arg i (def T (_ ∷ nn ∷ _))) (abs s B)) with depth nn
    ... | 0 = earg (def (Ty?Tm T assocTy assocTm) (δ ∷ θ ∷ earg (var n []) ∷ [])) ∷ make-args δ θ (n - 1) B
    ... | _ = earg (def (quote _∙_) (earg (def (Ty?Tm T assocTy assocTm) (earg (def (quote weakenMor+) (δ ∷ [])) ∷ earg (def (quote weakenMor+) (θ ∷ [])) ∷ earg (var n []) ∷ [])) ∷
                                      earg (def (Ty?Tm T (quote [weakenMor+]MorTy) (quote [weakenMor+]MorTm)) (earg (var n []) ∷ [])) ∷ [])) ∷ make-args δ θ (n - 1) B
    make-args δ θ n (pi (arg (arg-info visible _) _) (abs s B)) =
      earg (con (quote _≡_.refl) []) ∷ make-args δ θ (n - 1) B
    make-args δ θ n (pi _ (abs s B)) = make-args δ θ (n - 1) B
    make-args δ θ n _ = []

    constructClause-assoc : Name → TC Clause
    constructClause-assoc c = do
      pi _ (abs _ tyC) ← getType c
        where _ → typeError (strErr "The constructor should have [n] as a first implicit argument" ∷ [])
      let l = getNumberOfPi tyC
      let result = if primQNameEquality c (quote TmExpr.var) then
                     (def assocVar (earg (var (l + 1) []) ∷ earg (var l []) ∷ earg (var 0 []) ∷ []))
                   else
                     (def (lookup corresponding-ap c) (make-args (earg (var (l + 1) [])) (earg (var l [])) (l - 1) tyC))
      return (clause (earg (var "θ") ∷ earg (var "δ") ∷ earg (con c (constructPattern-assoc tyC)) ∷ [])
                     result)

[]Ty-assoc : (δ : Mor n m) (θ : Mor m k) (A : TyExpr k) → (A [ θ ]Ty [ δ ]Ty) ≡ (A [ θ [ δ ]Mor ]Ty)
[]Tm-assoc : (δ : Mor n m) (θ : Mor m k) (u : TmExpr k) → u [ θ ]Tm [ δ ]Tm ≡ u [ θ [ δ ]Mor ]Tm

[]Var-assoc : (δ : Mor n m) (θ : Mor m k) (x : Fin k) → var x [ θ ]Tm [ δ ]Tm ≡ var x [ θ [ δ ]Mor ]Tm
[]Var-assoc δ (θ , v) last = refl
[]Var-assoc δ (θ , v) (prev x) = []Var-assoc δ θ x

unquoteDef []Ty-assoc []Tm-assoc = generate-assoc []Ty-assoc []Tm-assoc (quote []Var-assoc)

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


