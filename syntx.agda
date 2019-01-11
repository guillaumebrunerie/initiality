{-# OPTIONS --rewriting --prop --without-K -v tc.unquote:10 #-}
 
open import common
open import typetheory
open import reflection

{- Contexts and context morphisms -}

data Ctx : ℕ → Set where
  ◇ : Ctx 0
  _,_ : {n : ℕ} (Γ : Ctx n) (A : TyExpr n) → Ctx (suc n)

data Mor (n : ℕ) : ℕ → Set where
  ◇ : Mor n 0
  _,_ : {m : ℕ} (δ : Mor n m) (u : TmExpr n) → Mor n (suc m)


{- Weakening -}

generate-weaken : Name → Name → Name → TC ⊤
generate-weaken weakenTy' weakenTm' weakenVar' = (do
  generateClausewise weakenTy' weakenTm'
    (earg (var "k") ∷ []) []
    (λ _ → con (quote TmExpr.var) (earg (def weakenVar' (earg (var 2 []) ∷ earg (var 0 []) ∷ [])) ∷ []))
    (λ l c tyC → con c (makeArgs' 0 (λ T n k → earg (def (Ty?Tm T weakenTy' weakenTm') (earg (iterate k (con (quote prev)) (var l [])) ∷ earg (var n []) ∷ []))) (l - 1) tyC)))

weakenTy' : (k : Fin (suc n)) → TyExpr {s} n → TyExpr {s} (suc n)
weakenTm' : (k : Fin (suc n)) → TmExpr {s} n → TmExpr {s} (suc n)

weakenVar' : (k : Fin (suc n)) → Fin n → Fin (suc n)
weakenVar' last = prev
weakenVar' (prev k) last = last
weakenVar' (prev k) (prev x) = prev (weakenVar' k x) 

unquoteDef weakenTy' weakenTm' = generate-weaken weakenTy' weakenTm' (quote weakenVar')

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
insertMor last u δ = (δ , u)
insertMor (prev ()) u ◇ 
insertMor (prev k) u (δ , u') = (insertMor k u δ  , u')

weakenCommutesInsert : (k : Fin (suc m)) (l : Fin (suc n)) (u : TmExpr n) (δ : Mor n m) → insertMor k (weakenTm' l u) (weakenMor' l δ) ≡ weakenMor' l (insertMor k u δ)
weakenCommutesInsert last l u ◇ = refl
weakenCommutesInsert (prev ()) l u ◇ 
weakenCommutesInsert last l u (δ , u') = refl
weakenCommutesInsert (prev k) l u (δ , u') = ap (λ z → z , _) (weakenCommutesInsert k l u δ)


{- Total substitutions -}

weakenMor+ : Mor n m → Mor (suc n) (suc m)
weakenMor+ δ = weakenMor δ , var last

generate-subst : Name → Name → Name → TC ⊤
generate-subst []Ty []Tm []Var = do
  generateClausewise []Ty []Tm
    [] (earg (var "δ") ∷ [])
    (λ _ → def []Var (earg (var 1 []) ∷ earg (var 0 []) ∷ []))
    (λ l c tyC → con c (makeArgs' 1 (λ T n k → earg (def (Ty?Tm T []Ty []Tm) (earg (var (suc n) []) ∷ earg (iterate k (def (quote weakenMor+)) (var 0 [])) ∷ []))) (l - 1) tyC))

infix 42 _[_]Ty
infix 42 _[_]Tm

_[_]Ty : {n m : ℕ} → TyExpr m → (δ : Mor n m) → TyExpr n
_[_]Tm : {n m : ℕ} → TmExpr m → (δ : Mor n m) → TmExpr n

_[_]Var : Fin m → (δ : Mor n m) → TmExpr n
last [ δ , u ]Var = u
prev k [ δ , u ]Var = k [ δ ]Var

unquoteDef _[_]Ty _[_]Tm = generate-subst _[_]Ty _[_]Tm (quote _[_]Var)

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


weakenCommutesTy'old : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TyExpr {s} (n + m))
                  → weakenTy' (prev^ m last) (weakenTy' (prev^ m k) A)
                  ≡ weakenTy' (prev^ m (prev k)) (weakenTy' (prev^ m last) A)
weakenCommutesTy+'old : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TyExpr {s} (suc (n + m)))
                   → FTy n m (suc (n + m)) k A reflR
-- weakenCommutesTy+++' : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TyExpr {s} (suc (suc (suc (n + m)))))
--                    → FTy ? ? (suc (suc (suc (n + m)))) k A reflR

weakenCommutesTm+'old : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TmExpr {s} (suc (n + m)))
                   → FTm n m (suc (n + m)) k A reflR
weakenCommutesTm'old : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : TmExpr {s} (n + m))
                  → weakenTm' (prev^ m last) (weakenTm' (prev^ m k) A)
                  ≡ weakenTm' (prev^ m (prev k)) (weakenTm' (prev^ m last) A)

weakenCommutesVar'old : {n : ℕ} (m : ℕ) (k : Fin (suc n)) (A : Fin (n + m))
                   → weakenVar' (prev^ m last) (weakenVar' (prev^ m k) A)
                   ≡ weakenVar' (prev^ m (prev k)) (weakenVar' (prev^ m last) A)


-- weakenCommutesTy+++' {n = n} m k A =
--   trFTy n m (n + suc m) k A (n+suc n m) (weakenCommutesTy' (suc (suc (suc m))) k (trTyExpr (!R (n+suc n m)) A))

weakenCommutesTy+'old {n = n} m k A =
  trFTy n m (n + suc m) k A (n+suc n m) (weakenCommutesTy'old (suc m) k (trTyExpr (!R (n+suc n m)) A))

weakenCommutesTy'old m k (uu i) = refl
weakenCommutesTy'old m k (el i v) rewrite weakenCommutesTm'old m k v = refl
weakenCommutesTy'old m k (pi A B) rewrite weakenCommutesTy'old m k A
                                     | weakenCommutesTy+'old m k B = refl
weakenCommutesTy'old m k (sig A B) rewrite weakenCommutesTy'old m k A
                                      | weakenCommutesTy+'old m k B = refl
weakenCommutesTy'old m k nat = refl
weakenCommutesTy'old m k (id A u v) rewrite weakenCommutesTy'old m k A
                                       | weakenCommutesTm'old m k u
                                       | weakenCommutesTm'old m k v = refl

weakenCommutesTm+'old {n = n} m k A =
  trFTm n m (n + suc m) k A (n+suc n m) (weakenCommutesTm'old (suc m) k (trTmExpr (!R (n+suc n m)) A))

weakenCommutesTm'old m k (var x) rewrite weakenCommutesVar'old m k x = refl
weakenCommutesTm'old m k (uu i) = refl
weakenCommutesTm'old m k (pi i a b)
  rewrite weakenCommutesTm'old m k a
        | weakenCommutesTm+'old m k b
  = refl
weakenCommutesTm'old m k (lam A B u)
  rewrite weakenCommutesTy'old m k A
        | weakenCommutesTy+'old m k B
        | weakenCommutesTm+'old m k u
  = refl
weakenCommutesTm'old m k (app A B f a)
  rewrite weakenCommutesTy'old m k A
        | weakenCommutesTy+'old m k B
        | weakenCommutesTm'old m k f
        | weakenCommutesTm'old m k a
  = refl
weakenCommutesTm'old m k (sig i a b)
  rewrite weakenCommutesTm'old m k a
        | weakenCommutesTm+'old m k b
  = refl
weakenCommutesTm'old m k (pair A B a b)
  rewrite weakenCommutesTy'old m k A
        | weakenCommutesTy+'old m k B
        | weakenCommutesTm'old m k a
        | weakenCommutesTm'old m k b
  = refl
weakenCommutesTm'old m k (pr1 A B u)
  rewrite weakenCommutesTy'old m k A
        | weakenCommutesTy+'old m k B
        | weakenCommutesTm'old m k u
  = refl
weakenCommutesTm'old m k (pr2 A B u)
  rewrite weakenCommutesTy'old m k A
        | weakenCommutesTy+'old m k B
        | weakenCommutesTm'old m k u
  = refl
weakenCommutesTm'old m k (nat i) = refl
weakenCommutesTm'old m k zero = refl
weakenCommutesTm'old m k (suc u)
  rewrite weakenCommutesTm'old m k u
  = refl
-- weakenCommutesTm'old m k (nat-elim P d0 dS u)
--   rewrite weakenCommutesTy+'old m k P
--         | weakenCommutesTm'old m k d0
--         | weakenCommutesTm+'old m k dS
--         | weakenCommutesTm'old m k u
--   = refl
weakenCommutesTm'old m k (id i a u v)
  rewrite weakenCommutesTm'old m k a
        | weakenCommutesTm'old m k u
        | weakenCommutesTm'old m k v
  = refl
weakenCommutesTm'old m k (refl A u)
  rewrite weakenCommutesTy'old m k A
        | weakenCommutesTm'old m k u
  = refl
-- weakenCommutesTm'old m k (jj A P d a b p)
--   rewrite weakenCommutesTy'old m k A
-- --        | {!weakenCommutesTy+++'old m k P!}
--         | weakenCommutesTm+'old m k d
--         | weakenCommutesTm'old m k a
--         | weakenCommutesTm'old m k b
--         | weakenCommutesTm'old m k p
--   = {!weakenCommutesTy'old m (prev (prev (prev k))) P!}

weakenCommutesVar'old {n = n} zero k x with n + 0 | n+0 n
... | _ | reflR = refl
weakenCommutesVar'old {n = n} (suc m) k x with n + suc m | n+suc n m
... | _ | reflR with x
...   | last = refl
...   | prev x' = ap prev (weakenCommutesVar'old m k x')


GTy : (n : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TyExpr {s} n) (p : u ≡R n) → Prop
GTy n u k A p =
  weakenTy' (trFin (apR suc (!R (apR suc p))) last) (weakenTy' (trFin (apR suc (!R p)) k) (trTyExpr (!R p) A)) ≡
  weakenTy' (trFin (apR suc (!R (apR suc p))) (prev k)) (weakenTy' (trFin (apR suc (!R p)) last) (trTyExpr ((!R p)) A))

trGTy : {s : Size} (n : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TyExpr n) (p : u ≡R n) → GTy {s} n u k A p → GTy {s} n n k A reflR
trGTy n u k A reflR x = x

weakenTyCommutesold : {n : ℕ} (k : Fin (suc n)) (A : TyExpr n) → weakenTy' last (weakenTy' k A) ≡ weakenTy' (prev k) (weakenTy' last A)
weakenTyCommutesold {n = n} k A = trGTy n (n + 0) k A (n+0 n) (weakenCommutesTy'old 0 k (trTyExpr (!R (n+0 n)) A))

GTm : (n : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TmExpr {s} n) (p : u ≡R n) → Prop
GTm n u k A p =
  weakenTm' (trFin (apR suc (!R (apR suc p))) last) (weakenTm' (trFin (apR suc (!R p)) k) (trTmExpr (!R p) A)) ≡
  weakenTm' (trFin (apR suc (!R (apR suc p))) (prev k)) (weakenTm' (trFin (apR suc (!R p)) last) (trTmExpr ((!R p)) A))

trGTm : {s : Size} (n : ℕ) (u : ℕ) (k : Fin (suc n)) (A : TmExpr n) (p : u ≡R n) → GTm {s} n u k A p → GTm {s} n n k A reflR
trGTm n u k A reflR x = x

weakenTmCommutesold : {n : ℕ} (k : Fin (suc n)) (A : TmExpr n) → weakenTm' last (weakenTm' k A) ≡ weakenTm' (prev k) (weakenTm' last A)
weakenTmCommutesold {n = n} k A = trGTm n (n + 0) k A (n+0 n) (weakenCommutesTm'old 0 k (trTmExpr (!R (n+0 n)) A))

lemma : suc k < suc n → k < n
lemma {k} {suc k} <-refl = <-refl
lemma {k} {zero} (<-suc ())
lemma {k} {suc n} (<-suc le) = <-suc (lemma le)


lemma2 : k < n → suc k < suc n
lemma2 {k} {suc k} <-refl = <-refl
lemma2 {k} {suc n} (<-suc le) = <-suc (lemma2 le)

<-= : k < m → m ≡ n → k < n
<-= le refl = le

insertFin : (k : ΣS ℕ (λ k → k < n)) → Fin n
insertFin {n = zero} (k , ())
insertFin {suc n} (zero , le) = last
insertFin {suc n} (suc k , le) = prev (insertFin (k , lemma le)) 

exportFin : Fin n → ΣS ℕ (λ k → k < n)
exportFin last = 0 , suc-pos _
exportFin (prev k) = (suc (fst (exportFin k)) , lemma2 (snd (exportFin k)))

weakenTy'sig : (k : ΣS ℕ (λ k → k < suc n)) (A : ΣSS ℕ (TyExpr {s})) (p : fst A ≡ n) → ΣSS ℕ (TyExpr {s})
weakenTy'sig {n = n} (k , le) (l , A) p  = (suc l , weakenTy' (insertFin (k , <-= le (ap suc (! p)))) A)

weakenTm'sig : (k : ΣS ℕ (λ k → k < suc n)) (u : ΣSS ℕ (TmExpr {s})) (p : fst u ≡ n) → ΣSS ℕ (TmExpr {s})
weakenTm'sig {n = n} (k , le) (l , u) p = (suc l , weakenTm' (insertFin (k , <-= le (ap suc (! p)))) u)



postulate
  projEqΣSS : {B : ℕ → Set} {n : ℕ} {b : B n} {b' : B n} → ΣSS._,_ {B = B} n b ≡ (n , b') → b ≡ b'
-- projEqΣSS refl = refl

ΣSS= : {B : ℕ → Set} {n : ℕ} {b : B n} {b' : B n} → b ≡ b' →  ΣSS._,_ {B = B} n b ≡ (n , b')
ΣSS= refl = refl

suc^ : (m : ℕ) → ℕ → ℕ
suc^ zero n = n
suc^ (suc m) n = suc (suc^ m n)

suc^+ : suc^ m (suc n) ≡ suc (n + m)
suc^+ {zero} {n} = ap suc (+-zero n)
suc^+ {suc m} {n} = ap suc (suc^+ ∙ +-suc n m)

suc^lemma : k < n → suc^ m k < suc^ m n
suc^lemma {k} {n} {zero} le = le
suc^lemma {k} {n} {suc m} le = lemma2 (suc^lemma le)

lastsig : ΣS ℕ (λ k → k < suc n)
lastsig = (zero , suc-pos _)

prevsig : (k : ΣS ℕ (λ k → k < n)) → ΣS ℕ (λ k → k < suc n)
prevsig (n , le) = (suc n , lemma2 le)


weakenVar'sig : (k : ΣS ℕ (λ k → k < suc n)) (x : ΣS ℕ (λ k → k < n)) → ΣS ℕ (λ k → k < suc n)
weakenVar'sig (zero , kle) (x , xle) = (suc x , lemma2 xle)
weakenVar'sig (suc k , kle) (zero , xle) = (zero , <-suc xle)
weakenVar'sig {n = zero} (suc k , kle) (suc x , ())
weakenVar'sig {n = suc n} (suc k , kle) (suc x , xle)  = prevsig (weakenVar'sig (k , lemma kle) (x , lemma xle))

prev^sig : (m : ℕ) → (k : ΣS ℕ (λ k → k < suc n)) → ΣS ℕ (λ k → k < suc (n + m))
prev^sig {n = n} m (k , le) = (suc^ m k , <-= (suc^lemma le) suc^+)


lemma5 : _≡_ {A = ℕ} (suc m) (suc n) → m ≡ n
lemma5 refl = refl

lemma6 : {k k' : Fin n} → _≡_ {A = TmExpr n} (var k) (var k') → k ≡ k'
lemma6 refl = refl

weakenCommutesTy' : {n : ℕ} (m : ℕ) (k : ΣS ℕ (λ k → k < suc n)) (A : ΣSS ℕ (TyExpr {s})) (p : fst A ≡ (n + m))
                  → weakenTy'sig (prev^sig m lastsig)  (weakenTy'sig (prev^sig m k) A p) (ap suc p) ≡ weakenTy'sig (prev^sig m (prevsig k)) (weakenTy'sig (prev^sig m lastsig) A  p) (ap suc p)

weakenCommutesTm' : {n : ℕ} (m : ℕ) (k : ΣS ℕ (λ k → k < suc n)) (A : ΣSS ℕ (TmExpr {s})) (p : fst A ≡ (n + m))
                  → weakenTm'sig (prev^sig m lastsig)  (weakenTm'sig (prev^sig m k) A p) (ap suc p) ≡ weakenTm'sig (prev^sig m (prevsig k)) (weakenTm'sig (prev^sig m lastsig) A  p) (ap suc p)
                  
weakenCommutesVar' : {s : Size} {n : ℕ} (m : ℕ) (u : ℕ) (k : ΣS ℕ (λ k → k < suc n)) (x : Fin u) (p : u ≡ n + m)
                   → weakenTm'sig {s = s} (prev^sig m lastsig) (weakenTm'sig (prev^sig m k) ((u , var x)) p) (ap suc p) ≡ weakenTm'sig (prev^sig m (prevsig k)) (weakenTm'sig (prev^sig m lastsig) ((u , var x)) p) (ap suc p)



weakenCommutesTy' m k (l , uu i) p = refl
weakenCommutesTy' m k (l , el i v) p rewrite projEqΣSS (weakenCommutesTm' m k (l , v) p) = refl
weakenCommutesTy' m k  (l , pi A B) p = ΣSS= (ap-pi-Ty (projEqΣSS (weakenCommutesTy' m k (l , A) p)) (projEqΣSS (weakenCommutesTy' (suc m) k (suc l , B) (ap suc p ∙ +-suc _ m))))
weakenCommutesTy' m k (l , sig A B) p = ΣSS= (ap-sig-Ty (projEqΣSS (weakenCommutesTy' m k (l , A) p)) (projEqΣSS (weakenCommutesTy' (suc m) k (suc l , B) (ap suc p ∙ +-suc _ m))))
weakenCommutesTy' m k (l , nat) p = refl
weakenCommutesTy' m (k , le) (l , id A u v) p rewrite projEqΣSS (weakenCommutesTy' m (k , le) (l , A) p) | projEqΣSS (weakenCommutesTm' m (k , le) (l , u) p) | projEqΣSS (weakenCommutesTm' m (k , le) (l , v) p)  = refl                 

weakenCommutesTm' m k (l , var x) p = weakenCommutesVar' m l k x p
weakenCommutesTm' m k (l , uu i) p = refl
weakenCommutesTm' m k (l , pi i a b) p = ΣSS= (ap-pi-Tm refl (projEqΣSS (weakenCommutesTm' m k (l , a) p)) (projEqΣSS (weakenCommutesTm' (suc m) k (suc l , b) (ap suc p ∙ +-suc _ m))))
weakenCommutesTm' m k (l , lam A B u) p = ΣSS= (ap-lam-Tm (projEqΣSS (weakenCommutesTy' m k (l , A) p)) (projEqΣSS (weakenCommutesTy' (suc m) k (suc l , B) (ap suc p ∙ +-suc _ m))) (projEqΣSS (weakenCommutesTm' (suc m) k (suc l , u) (ap suc p ∙ +-suc _ m))))
weakenCommutesTm' m k (l , app A B f a) p = ΣSS= (ap-app-Tm (projEqΣSS (weakenCommutesTy' m k (l , A) p)) (projEqΣSS (weakenCommutesTy' (suc m) k (suc l , B) (ap suc p ∙ +-suc _ m))) (projEqΣSS (weakenCommutesTm' m k (l , f) p)) (projEqΣSS (weakenCommutesTm' m k (l , a) p)))
weakenCommutesTm' m k (l , sig i a b) p = ΣSS= (ap-sig-Tm refl (projEqΣSS (weakenCommutesTm' m k (l , a) p)) (projEqΣSS (weakenCommutesTm' (suc m) k (suc l , b) (ap suc p ∙ +-suc _ m))))
weakenCommutesTm' m k (l , pair A B a b) p = ΣSS= (ap-pair-Tm (projEqΣSS (weakenCommutesTy' m k (l , A) p)) (projEqΣSS (weakenCommutesTy' (suc m) k (suc l , B) (ap suc p ∙ +-suc _ m))) (projEqΣSS (weakenCommutesTm' m k (l , a) p)) (projEqΣSS (weakenCommutesTm' m k (l , b) p)))
weakenCommutesTm' m k (l , pr1 A B u) p = ΣSS= (ap-pr1-Tm (projEqΣSS (weakenCommutesTy' m k (l , A) p)) (projEqΣSS (weakenCommutesTy' (suc m) k (suc l , B) (ap suc p ∙ +-suc _ m))) (projEqΣSS (weakenCommutesTm' m k (l , u) p)))
weakenCommutesTm' m k (l , pr2 A B u) p = ΣSS= (ap-pr2-Tm (projEqΣSS (weakenCommutesTy' m k (l , A) p)) (projEqΣSS (weakenCommutesTy' (suc m) k (suc l , B) (ap suc p ∙ +-suc _ m))) (projEqΣSS (weakenCommutesTm' m k (l , u) p)))
weakenCommutesTm' m k (l , nat i) p = refl
weakenCommutesTm' m k (l , zero) p = refl
weakenCommutesTm' m k (l , suc x) p rewrite projEqΣSS (weakenCommutesTm' m k (l , x) p) = refl
-- weakenCommutesTm' m k (l , nat-elim P d0 dS u) p = ΣSS= (ap-nat-elim-Tm (projEqΣSS (weakenCommutesTy' (suc m) k (suc l , P) (ap suc p ∙ +-suc _ m))) (projEqΣSS (weakenCommutesTm' m k (l , d0) p)) (projEqΣSS (weakenCommutesTm' (suc (suc m)) k ((suc (suc l) , dS)) (ap suc (ap suc p) ∙ ap suc (+-suc _ m) ∙ +-suc _ (suc m)))) (projEqΣSS (weakenCommutesTm' m k (l , u) p)))
weakenCommutesTm' m k (l , id i a u v) p rewrite projEqΣSS (weakenCommutesTm' m k (l , a) p) | projEqΣSS (weakenCommutesTm' m k (l , u) p) | projEqΣSS (weakenCommutesTm' m k (l , v) p) = refl
weakenCommutesTm' m k (l , refl A a) p rewrite projEqΣSS (weakenCommutesTy' m k (l , A) p) | projEqΣSS (weakenCommutesTm' m k (l , a) p) = refl
-- weakenCommutesTm' m k (l , jj A P d a b p) q = ΣSS= (ap-jj-Tm (projEqΣSS (weakenCommutesTy' m k (l , A) q)) (projEqΣSS (weakenCommutesTy' (suc (suc (suc m))) k (suc (suc (suc l)) , P)  (ap suc (ap suc (ap suc q)) ∙ (ap suc (ap suc (+-suc _ m)) ∙ ap suc (+-suc _ (suc m))) ∙ +-suc _ (suc (suc m))))) (projEqΣSS (weakenCommutesTm' (suc m) k (suc l , d) (ap suc q ∙ +-suc _ m))) (projEqΣSS (weakenCommutesTm' m k (l , a) q)) (projEqΣSS (weakenCommutesTm' m k (l , b) q)) (projEqΣSS (weakenCommutesTm' m k (l , p) q)))


weakenCommutesVar' zero u (k , le) x p = refl
weakenCommutesVar' (suc m) (suc u) (k , le) last p = refl
weakenCommutesVar' (suc m) (suc u) (k , le) (prev x) p = ΣSS= (ap-var-Tm (ap prev (lemma6 (projEqΣSS (weakenCommutesVar' m u (k , le) x (lemma5 (p ∙ ! (+-suc _ m))))))))

weakenTyCommutessig : {n : ℕ} (k : ΣS ℕ (λ k → k < suc n)) (A : ΣSS ℕ (TyExpr {s})) (p : fst A ≡ n)
  → weakenTy'sig lastsig (weakenTy'sig k A p) (ap suc p) ≡ weakenTy'sig (prevsig k) (weakenTy'sig lastsig A p) (ap suc p)
weakenTyCommutessig k A p = weakenCommutesTy' zero k A (p ∙ +-zero _)

weakenTmCommutessig : {n : ℕ} (k : ΣS ℕ (λ k → k < suc n)) (u : ΣSS ℕ (TmExpr {s})) (p : fst u ≡ n)
  → weakenTm'sig lastsig (weakenTm'sig k u p) (ap suc p) ≡ weakenTm'sig (prevsig k) (weakenTm'sig lastsig u p) (ap suc p)
weakenTmCommutessig k u p = weakenCommutesTm' zero k u (p ∙ +-zero _)




insertexport : (k : Fin n) → k ≡ insertFin (exportFin k)
insertexport last = refl
insertexport (prev k) = ap prev (insertexport k)

lemma3Ty : {n : ℕ} (k : Fin (suc n)) (A : TyExpr {s} n) → weakenTy' last (weakenTy' k A) ≡ snd (weakenTy'sig lastsig (weakenTy'sig (exportFin k) (n , A) refl) refl)
lemma3Ty last A = refl
lemma3Ty (prev k) A = ap (λ z → weakenTy' last (weakenTy' (prev z) A)) (insertexport k)

lemma4Ty : {n : ℕ} (k : Fin (suc n)) (A : TyExpr {s} n) → snd (weakenTy'sig (prevsig (exportFin k)) (weakenTy'sig lastsig (n , A) refl) refl) ≡ weakenTy' (prev k) (weakenTy' last A)
lemma4Ty last A = refl
lemma4Ty (prev k) A = ap (λ z → weakenTy' (prev (prev z)) (weakenTy' last A)) (! (insertexport k))

weakenTyCommutes : {n : ℕ} (k : Fin (suc n)) (A : TyExpr n) → weakenTy' last (weakenTy' k A) ≡ weakenTy' (prev k) (weakenTy' last A)
weakenTyCommutes {n = n} k A = lemma3Ty k A ∙ projEqΣSS (weakenTyCommutessig (exportFin k) (n , A) refl) ∙ lemma4Ty k A

lemma3Tm : {n : ℕ} (k : Fin (suc n)) (A : TmExpr {s} n) → weakenTm' last (weakenTm' k A) ≡ snd (weakenTm'sig lastsig (weakenTm'sig (exportFin k) (n , A) refl) refl)
lemma3Tm last A = refl
lemma3Tm (prev k) A = ap (λ z → weakenTm' last (weakenTm' (prev z) A)) (insertexport k)

lemma4Tm : {n : ℕ} (k : Fin (suc n)) (A : TmExpr {s} n) → snd (weakenTm'sig (prevsig (exportFin k)) (weakenTm'sig lastsig (n , A) refl) refl) ≡ weakenTm' (prev k) (weakenTm' last A)
lemma4Tm last A = refl
lemma4Tm (prev k) A = ap (λ z → weakenTm' (prev (prev z)) (weakenTm' last A)) (! (insertexport k))

weakenTmCommutes : {n : ℕ} (k : Fin (suc n)) (A : TmExpr n) → weakenTm' last (weakenTm' k A) ≡ weakenTm' (prev k) (weakenTm' last A)
weakenTmCommutes {n = n} k A = lemma3Tm k A ∙ projEqΣSS (weakenTmCommutessig (exportFin k) (n , A) refl) ∙ lemma4Tm k A

weakenMorCommutes : (k : Fin (suc n)) (δ : Mor n m) → weakenMor' last (weakenMor' k δ) ≡ weakenMor' (prev k) (weakenMor' last δ)
weakenMorCommutes {m = zero} k ◇ = refl
weakenMorCommutes {m = suc m} k (δ , u) rewrite weakenMorCommutes k δ | weakenTmCommutes k u = refl


{- Weakening commutes with total substitution -}

weakenMorCommutesLemmaTy : (A : TyExpr (suc m)) (δ : Mor n m) (k : Fin (suc n)) → A [ weakenMor' (prev k) (weakenMor+ δ) ]Ty ≡
                                                                                  A [ weakenMor+ (weakenMor' k δ) ]Ty
weakenMorCommutesLemmaTy A δ k = ap (λ z → A [ z , var last ]Ty) (! (weakenMorCommutes k δ))

weakenMorCommutesLemmaTm : (u : TmExpr (suc m)) (δ : Mor n m) (k : Fin (suc n)) → u [ weakenMor' (prev k) (weakenMor+ δ) ]Tm ≡
                                                                                  u [ weakenMor+ (weakenMor' k δ) ]Tm
weakenMorCommutesLemmaTm u δ k = ap (λ z → u [ z , var last ]Tm) (! (weakenMorCommutes k δ))

generate-weaken[] : Name → Name → Name → TC ⊤
generate-weaken[] weaken[]Ty weaken[]Tm weaken[]Var =
  generateClausewise weaken[]Ty weaken[]Tm
    [] (earg (var "δ") ∷ earg (var "k") ∷ [])
    (λ l → def weaken[]Var (earg (var 2 []) ∷ earg (var 1 []) ∷ earg (var 0 []) ∷ []))
    (apify thing)

   where

    thing : Name → ℕ → ℕ → Arg Term
    thing T n 0 =
      earg (def (Ty?Tm T weaken[]Ty weaken[]Tm) (earg (var (n + 2) []) ∷ earg (var 1 []) ∷ earg (var 0 []) ∷ []))
    thing T n 1 =
      earg (def (quote _∙_) (earg (def (Ty?Tm T weaken[]Ty weaken[]Tm)
                                         (earg (var (n + 2) [])
                                        ∷ earg (def (quote weakenMor+) (earg (var 1 []) ∷ []))
                                        ∷ earg (con (quote prev) (earg (var 0 []) ∷ [])) ∷ []))
                           ∷ earg (def (Ty?Tm T (quote weakenMorCommutesLemmaTy) (quote weakenMorCommutesLemmaTm))
                                         (earg (var (n + 2) [])
                                        ∷ earg (var 1 [])
                                        ∷ earg (var 0 []) ∷ []))
                           ∷ []))
    thing T n _ = earg unknown

weaken[]Ty : (A : TyExpr n) (δ : Mor m n) (k : Fin (suc m)) → weakenTy' k (A [ δ ]Ty) ≡ A [ weakenMor' k δ ]Ty
weaken[]Tm : (u : TmExpr n) (δ : Mor m n) (k : Fin (suc m)) → weakenTm' k (u [ δ ]Tm) ≡ u [ weakenMor' k δ ]Tm

weaken[]Var : (x : Fin n) (δ : Mor m n) (k : Fin (suc m)) → weakenTm' k (x [ δ ]Var) ≡ x [ weakenMor' k δ ]Var
weaken[]Var last (δ , u) k = refl
weaken[]Var (prev x) (δ , u) k = weaken[]Var x δ k

unquoteDef weaken[]Ty weaken[]Tm = generate-weaken[] weaken[]Ty weaken[]Tm (quote weaken[]Var)

weaken[]Mor : (θ : Mor n k) (δ : Mor m n) (k : Fin (suc m)) → weakenMor' k (θ [ δ ]Mor) ≡ (θ [ weakenMor' k δ ]Mor)

weaken[]Mor ◇ _ k = refl
weaken[]Mor (θ , u) δ k rewrite weaken[]Mor θ δ k | weaken[]Tm u δ k = refl


{- Substituting a morphism where a term is inserted into a type/term/morphism that is weakened at that point does nothing -}

weakenTyInsertLemma : (k : Fin (suc n)) (A : TyExpr (suc n)) (δ : Mor m n) (t : TmExpr m)
  → weakenTy' (prev k) A [ weakenMor+ (insertMor k t δ) ]Ty ≡
    weakenTy' (prev k) A [ insertMor (prev k) (weakenTm t) (weakenMor+ δ) ]Ty
weakenTyInsertLemma k A δ t = ap (λ z → weakenTy' (prev k) A [ z , var last ]Ty) (! (weakenCommutesInsert k last t δ))

weakenTmInsertLemma : (k : Fin (suc n)) (u : TmExpr (suc n)) (δ : Mor m n) (t : TmExpr m)
  → weakenTm' (prev k) u [ weakenMor+ (insertMor k t δ) ]Tm ≡
    weakenTm' (prev k) u [ insertMor (prev k) (weakenTm t) (weakenMor+ δ) ]Tm
weakenTmInsertLemma k u δ t = ap (λ z → weakenTm' (prev k) u [ z , var last ]Tm) (! (weakenCommutesInsert k last t δ))


generate-weakenInsert : Name → Name → Name → TC ⊤
generate-weakenInsert weakenInsertTy weakenInsertTm weakenInsertVar =
  generateClausewise weakenInsertTy weakenInsertTm
    (earg (var "k") ∷ []) (earg (var "δ") ∷ earg (var "t") ∷ [])
    (λ l → def weakenInsertVar (earg (var 4 []) ∷ earg (var 2 []) ∷ earg (var 1 []) ∷ earg (var 0 []) ∷ []))
    (λ l → apify (thing l) l)

   where

    thing : ℕ → Name → ℕ → ℕ → Arg Term
    thing l T n 0 =
      earg (def (Ty?Tm T weakenInsertTy weakenInsertTm) (earg (var (l + 2) []) ∷ earg (var (n + 2) []) ∷ earg (var 1 []) ∷ earg (var 0 []) ∷ []))
    thing l T n 1 =
      earg (def (quote _∙_) (earg (def (Ty?Tm T (quote weakenTyInsertLemma) (quote weakenTmInsertLemma))
                                         (earg (var (l + 2) [])
                                        ∷ earg (var (n + 2) [])
                                        ∷ earg (var 1 [])
                                        ∷ earg (var 0 []) ∷ []))
                           ∷ earg (def (Ty?Tm T weakenInsertTy weakenInsertTm)
                                         (earg (con (quote prev) (earg (var (l + 2) []) ∷ []))
                                        ∷ earg (var (n + 2) [])
                                        ∷ earg (def (quote weakenMor+) (earg (var 1 []) ∷ []))
                                        ∷ earg (def (quote weakenTm) (earg (var 0 []) ∷ [])) ∷ []))
                           ∷ []))
    thing l T n _ = earg unknown

weakenTyInsert' : (k : Fin (suc m)) (A : TyExpr m) (δ : Mor n m) (t : TmExpr n) -> weakenTy' k A [ insertMor k t δ ]Ty ≡ A [ δ ]Ty
weakenTmInsert' : (k : Fin (suc m)) (u : TmExpr m) (δ : Mor n m) (t : TmExpr n) -> weakenTm' k u [ insertMor k t δ ]Tm ≡ u [ δ ]Tm

weakenVarInsert' : (k : Fin (suc m)) (x : Fin m) (δ : Mor n m) (t : TmExpr n) -> weakenVar' k x [ insertMor k t δ ]Var ≡ x [ δ ]Var
weakenVarInsert' last x δ t = refl
weakenVarInsert' (prev k) last (δ , u) t = refl
weakenVarInsert' (prev k) (prev x) (δ , u) t = weakenVarInsert' k x δ t

unquoteDef weakenTyInsert' weakenTmInsert' = generate-weakenInsert weakenTyInsert' weakenTmInsert' (quote weakenVarInsert')


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

{- Substitution by the identity morphism does nothing -}

[idMor]Ty : (A : TyExpr n) → A [ idMor n ]Ty ≡ A
[idMor]Tm : (u : TmExpr n) → u [ idMor n ]Tm ≡ u
[idMor]Var : (x : Fin n) → (var x) [ idMor n ]Tm ≡ var x

[idMor]Var {n = zero} ()
[idMor]Var {n = suc n} last = refl
[idMor]Var {n = suc n} (prev x) = ! (weaken[]Tm (var x) (idMor n) last) ∙ ap weakenTm ([idMor]Var x)

unquoteDef [idMor]Ty [idMor]Tm =
  generateClausewise [idMor]Ty [idMor]Tm [] []
    (λ _ → def (quote [idMor]Var) (earg (var 0 []) ∷ []))
    (apify (λ T n _ → earg (def (Ty?Tm T [idMor]Ty [idMor]Tm) (earg (var n []) ∷ []))))

[idMor]Mor : {n m : ℕ} (δ : Mor n m) → δ [ idMor n ]Mor ≡ δ
[idMor]Mor ◇ = refl
[idMor]Mor (δ , u) rewrite [idMor]Mor δ | [idMor]Tm u = refl

idMor[]Mor : (δ : Mor n m) → idMor m [ δ ]Mor ≡ δ

idMor[]Mor {m = zero} ◇ = refl
idMor[]Mor {m = suc m} (δ , u) rewrite weakenMorInsert (idMor m) δ u | idMor[]Mor δ  = refl


{- Substitution is associative -}

generate-assoc : Name → Name → Name → TC ⊤
generate-assoc []Ty-assoc []Tm-assoc []Var-assoc =
  generateClausewise []Ty-assoc []Tm-assoc
    (earg (var "θ") ∷ earg (var "δ") ∷ []) []
    (λ l → def []Var-assoc (earg (var 3 []) ∷ earg (var 2 []) ∷ earg (var 0 []) ∷ []))
    (λ l → apify (thing (earg (var (l + 1) [])) (earg (var l []))) l)

   where

    thing : Arg Term → Arg Term → Name → ℕ → ℕ → Arg Term
    thing δ θ T n 0 =
      earg (def (Ty?Tm T []Ty-assoc []Tm-assoc) (δ ∷ θ ∷ earg (var n []) ∷ []))
    thing δ θ T n 1 =
      earg (def (quote _∙_) (earg (def (Ty?Tm T []Ty-assoc []Tm-assoc)
                                         (earg (def (quote weakenMor+) (δ ∷ []))
                                        ∷ earg (def (quote weakenMor+) (θ ∷ []))
                                        ∷ earg (var n []) ∷ []))
                           ∷ earg (def (Ty?Tm T (quote [weakenMor+]MorTy) (quote [weakenMor+]MorTm))
                                         (earg (var n []) ∷ [])) ∷ []))
    thing δ θ T n _ = earg unknown

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
