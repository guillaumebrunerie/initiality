{-# OPTIONS --rewriting --prop -v tc.unquote:10 #-}
 
open import common
open import typetheory
open import reflection

{- Contexts and context morphisms -}

data Ctx : ℕ → Set where
  ◇ : Ctx 0
  _,_ : {n : ℕ} (Γ : Ctx n) (A : TyExpr n) → Ctx (suc n)

Ctx+= : {Γ Γ' : Ctx n} {A A' : TyExpr n} → Γ ≡ Γ' → A ≡ A' → Ctx._,_ Γ A ≡ (Γ' , A')
Ctx+= refl refl = refl


data Mor (n : ℕ) : ℕ → Set where 
 ◇ : Mor n 0
 _,_ : {m : ℕ} (δ : Mor n m) (u : TmExpr n) → Mor n (suc m)

Mor+= : {δ δ' : Mor n m} {u u' : TmExpr n} → δ ≡ δ' → u ≡ u' → Mor._,_ δ u ≡ (δ' , u')
Mor+= refl refl = refl


{- Weakening -}

generate-weaken : Name → Name → Name → TC ⊤
generate-weaken weakenTy' weakenTm' weakenVar' = (do
  generateClausewise weakenTy' weakenTm'
    (earg (var "k") ∷ []) []
    (λ _ → con (quote TmExpr.var) (earg (def weakenVar' (earg (var 1 []) ∷ earg (var 0 []) ∷ [])) ∷ []))
    (λ l c tyC → con c (makeArgs' 0 (λ T n k → earg (def (Ty?Tm T weakenTy' weakenTm') (earg (iterate k (con (quote WeakPos.prev)) (var l [])) ∷ earg (var n []) ∷ []))) (l - 1) tyC)))

weakenTy' : (k : WeakPos n) → TyExpr n → TyExpr (suc n)
weakenTm' : (k : WeakPos n) → TmExpr n → TmExpr (suc n)

weakenVar' : (k : WeakPos n) → VarPos n → VarPos (suc n)
weakenVar' last = prev
weakenVar' (prev k) last = last
weakenVar' (prev k) (prev x) = prev (weakenVar' k x) 

unquoteDef weakenTy' weakenTm' = generate-weaken weakenTy' weakenTm' (quote weakenVar')

weakenTy : TyExpr n → TyExpr (suc n)
weakenTy = weakenTy' last
 
weakenTm : TmExpr n → TmExpr (suc n)
weakenTm = weakenTm' last

weakenMor' : (k : WeakPos n) → Mor n m → Mor (suc n) m
weakenMor' k ◇ = ◇
weakenMor' k (δ , u) = (weakenMor' k δ , weakenTm' k u)

weakenMor : Mor n m → Mor (suc n) m
weakenMor = weakenMor' last

weakenCtx : (k : WeakPos n) (Γ : Ctx n) (T : TyExpr (n -WeakPos k)) → Ctx (suc n)
weakenCtx last Γ T = Γ , T
weakenCtx (prev k) (Γ , A) T = weakenCtx k Γ T , weakenTy' k A 

idMor : (n : ℕ) → Mor n n
idMor zero = ◇
idMor (suc n) = weakenMor (idMor n) , var last

insertMor : (k : WeakPos m) → TmExpr n  → Mor n m → Mor n (suc m)
insertMor last u δ = (δ , u)
insertMor (prev k) u (δ , u') = (insertMor k u δ  , u')

weakenCommutesInsert : (k : WeakPos m) (l : WeakPos n) (u : TmExpr n) (δ : Mor n m) → insertMor k (weakenTm' l u) (weakenMor' l δ) ≡ weakenMor' l (insertMor k u δ)
weakenCommutesInsert last l u ◇ = refl
weakenCommutesInsert last l u (δ , u') = refl
weakenCommutesInsert (prev k) l u (δ , u') = ap (λ z → z , _) (weakenCommutesInsert k l u δ)


{- Total substitutions -}

weakenMor+ : Mor n m → Mor (suc n) (suc m)
weakenMor+ δ = weakenMor δ , var last

getLHS : {n m : ℕ} → Mor n (suc m) → Mor n m
getLHS (δ , u) = δ

getRHS : {n m : ℕ} → Mor n (suc m) → TmExpr n
getRHS (δ , u) = u

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

_[_]Var : VarPos m → (δ : Mor n m) → TmExpr n
last [ δ ]Var = getRHS δ
prev k [ δ ]Var = k [ getLHS δ ]Var

unquoteDef _[_]Ty _[_]Tm = generate-subst _[_]Ty _[_]Tm (quote _[_]Var)

-- One could also define substitution of morphisms as follows:
--
-- _[_]Mor : {n m k : ℕ} → Mor n k → (δ : Mor m n) → Mor m k
-- ◇ [ δ ]Mor = ◇
-- (γ , u) [ δ ]Mor = (γ [ δ ]Mor , u [ δ ]Tm)
--
-- But the definition used here has the advantage that it reduces even if we do
-- not pattern match on the first morphism, we only need to know that its length
-- is of the form [suc n]. This is used to make the proofs of naturalities in
-- the term model much nicer.

_[_]Mor : {n m k : ℕ} → Mor n k → (δ : Mor m n) → Mor m k
_[_]Mor {k = 0} _ δ = ◇
_[_]Mor {k = suc k} γ δ = ((getLHS γ) [ δ ]Mor , (getRHS γ) [ δ ]Tm)

{- Partial substitutions as a special case of total substitutions -}

substTy : TyExpr (suc n) → TmExpr n → TyExpr n
substTm : TmExpr (suc n) → TmExpr n → TmExpr n

substTy A t = A [ idMor _ , t ]Ty
substTm u t = u [ idMor _ , t ]Tm


{- Weakening commutes with weakening -}

generate-weakenCommutes : Name → Name → Name → TC ⊤
generate-weakenCommutes weakenTyCommutes weakenTmCommutes weakenVarCommutes =
  generateClausewise weakenTyCommutes weakenTmCommutes
    [] (iarg (var "k") ∷ iarg (var "k'") ∷ earg (var "p") ∷ [])
    (λ l → def (quote ap-var-Tm) (earg (def weakenVarCommutes (earg (var 3 []) ∷ earg (var 0 []) ∷ [])) ∷ []))
    (apify λ T n k → earg (def (Ty?Tm T weakenTyCommutes weakenTmCommutes) (earg (var (3 + n) []) ∷ iarg unknown ∷ iarg unknown ∷ earg (iterate k (con (quote prev≤)) (var 0 [])) ∷ [])))

weakenTyCommutes : (A : TyExpr n) {k k' : WeakPos n} (_ : k ≤WP k') → weakenTy' (injWeakPos k') (weakenTy' k A) ≡ weakenTy' (prev k) (weakenTy' k' A)
weakenTmCommutes : (u : TmExpr n) {k k' : WeakPos n} (_ : k ≤WP k') → weakenTm' (injWeakPos k') (weakenTm' k u) ≡ weakenTm' (prev k) (weakenTm' k' u)

weakenVarCommutes : (x : VarPos n) {k k' : WeakPos n} (_ : k ≤WP k') → weakenVar' (injWeakPos k') (weakenVar' k x) ≡ weakenVar' (prev k) (weakenVar' k' x)
weakenVarCommutes last last≤ = refl
weakenVarCommutes last (prev≤ x) = refl
weakenVarCommutes (prev p) last≤ = refl
weakenVarCommutes (prev p) (prev≤ x) = ap prev (weakenVarCommutes p x)

unquoteDef weakenTyCommutes weakenTmCommutes = generate-weakenCommutes weakenTyCommutes weakenTmCommutes (quote weakenVarCommutes)

weakenMorCommutes' : (θ : Mor n m) {k k' : WeakPos n} (_ : k ≤WP k') → weakenMor' (injWeakPos k') (weakenMor' k θ) ≡ weakenMor' (prev k) (weakenMor' k' θ)
weakenMorCommutes' ◇ p = refl
weakenMorCommutes' (θ , u) p = Mor+= (weakenMorCommutes' θ p) (weakenTmCommutes u p)

weakenTmCommutes0 : {n : ℕ} (k : WeakPos n) (u : TmExpr n) → weakenTm' last (weakenTm' k u) ≡ weakenTm' (prev k) (weakenTm' last u)
weakenTmCommutes0 k u = weakenTmCommutes u last≤

weakenTyCommutesprev1 : {n : ℕ} (k : WeakPos n) (A : TyExpr (1 + n)) → weakenTy' (prev last) (weakenTy' (prev k) A) ≡ weakenTy' (prev (prev k)) (weakenTy' (prev last) A)
weakenTyCommutesprev1 k A = weakenTyCommutes A (prev≤ last≤)

weakenTyCommutesprev2 : {n : ℕ} (k : WeakPos n) (A : TyExpr (2 + n)) → weakenTy' (prev (prev last)) (weakenTy' (prev (prev k)) A) ≡ weakenTy' (prev (prev (prev k))) (weakenTy' (prev (prev last)) A)
weakenTyCommutesprev2 k A = weakenTyCommutes A (prev≤ (prev≤ last≤))

weakenTyCommutesprev3 : {n : ℕ} (k : WeakPos n) (A : TyExpr (3 + n)) → weakenTy' (prev (prev (prev last))) (weakenTy' (prev (prev (prev k))) A) ≡ weakenTy' (prev (prev (prev (prev k)))) (weakenTy' (prev (prev (prev last))) A)
weakenTyCommutesprev3 k A = weakenTyCommutes A (prev≤ (prev≤ (prev≤ last≤)))

weakenMorCommutes : (k : WeakPos n) (δ : Mor n m) → weakenMor' last (weakenMor' k δ) ≡ weakenMor' (prev k) (weakenMor' last δ)
weakenMorCommutes {m = zero} k ◇ = refl
weakenMorCommutes {m = suc m} k (δ , u) rewrite weakenMorCommutes k δ | weakenTmCommutes0 k u = refl


{- Weakening commutes with total substitution -}

weakenMor+^ : (k : ℕ) → Mor n m → Mor (k + n) (k + m)
weakenMor+^ zero δ = δ
weakenMor+^ (suc k) δ = weakenMor+ (weakenMor+^ k δ)

weakenMorCommutesLemmaTy : (A : TyExpr (suc m)) (δ : Mor n m) (k : WeakPos n)
                           → A [ weakenMor' (prev k) (weakenMor+ δ) ]Ty ≡ A [ weakenMor+ (weakenMor' k δ) ]Ty
weakenMorCommutesLemmaTy A δ k = ap (λ z → A [ z , var last ]Ty) (! (weakenMorCommutes k δ))

weakenMorCommutesLemmaTy2 : (A : TyExpr (suc (suc m))) (δ : Mor n m) (k : WeakPos n)
                            → A [ weakenMor' (prev (prev k)) (weakenMor+^ 2 δ) ]Ty ≡ A [ weakenMor+^ 2 (weakenMor' k δ) ]Ty
weakenMorCommutesLemmaTy2 A δ k = weakenMorCommutesLemmaTy A (weakenMor+ δ) (prev k) ∙ ap (λ z → A [ weakenMor+ (z , var last) ]Ty) (! (weakenMorCommutes k δ))

weakenMorCommutesLemmaTy3 : (A : TyExpr (suc (suc (suc m)))) (δ : Mor n m) (k : WeakPos n)
                            → A [ weakenMor' (prev (prev (prev k))) (weakenMor+^ 3 δ) ]Ty ≡ A [ weakenMor+^ 3 (weakenMor' k δ) ]Ty
weakenMorCommutesLemmaTy3 A δ k = weakenMorCommutesLemmaTy2 A (weakenMor+ δ) (prev k) ∙ ap (λ z → A [ weakenMor+^ 2 (z , var last) ]Ty) (! (weakenMorCommutes k δ))

weakenMorCommutesLemmaTm : (u : TmExpr (suc m)) (δ : Mor n m) (k : WeakPos n) → u [ weakenMor' (prev k) (weakenMor+ δ) ]Tm ≡
                                                                                  u [ weakenMor+ (weakenMor' k δ) ]Tm
weakenMorCommutesLemmaTm u δ k = ap (λ z → u [ z , var last ]Tm) (! (weakenMorCommutes k δ))

weakenMorCommutesLemmaTm2 : (u : TmExpr (suc (suc m))) (δ : Mor n m) (k : WeakPos n)
                            → u [ weakenMor' (prev (prev k)) (weakenMor+^ 2 δ) ]Tm ≡ u [ weakenMor+^ 2 (weakenMor' k δ) ]Tm
weakenMorCommutesLemmaTm2 u δ k = weakenMorCommutesLemmaTm u (weakenMor+ δ) (prev k) ∙ ap (λ z → u [ weakenMor+ (z , var last) ]Tm) (! (weakenMorCommutes k δ))

weakenMorCommutesLemmaTm3 : (u : TmExpr (suc (suc (suc m)))) (δ : Mor n m) (k : WeakPos n)
                            → u [ weakenMor' (prev (prev (prev k))) (weakenMor+^ 3 δ) ]Tm ≡ u [ weakenMor+^ 3 (weakenMor' k δ) ]Tm
weakenMorCommutesLemmaTm3 u δ k = weakenMorCommutesLemmaTm2 u (weakenMor+ δ) (prev k) ∙ ap (λ z → u [ weakenMor+^ 2 (z , var last) ]Tm) (! (weakenMorCommutes k δ))

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
                                        ∷ earg (def (quote weakenMor+^) (earg (lit (nat 1)) ∷ earg (var 1 []) ∷ []))
                                        ∷ earg (iterate 1 (con (quote WeakPos.prev)) (var 0 [])) ∷ []))
                           ∷ earg (def (Ty?Tm T (quote weakenMorCommutesLemmaTy) (quote weakenMorCommutesLemmaTm))
                                         (earg (var (n + 2) [])
                                        ∷ earg (var 1 [])
                                        ∷ earg (var 0 []) ∷ []))
                           ∷ []))
    thing T n 2 =
      earg (def (quote _∙_) (earg (def (Ty?Tm T weaken[]Ty weaken[]Tm)
                                         (earg (var (n + 2) [])
                                        ∷ earg (def (quote weakenMor+^) (earg (lit (nat 2)) ∷ earg (var 1 []) ∷ []))
                                        ∷ earg (iterate 2 (con (quote WeakPos.prev)) (var 0 [])) ∷ []))
                           ∷ earg (def (Ty?Tm T (quote weakenMorCommutesLemmaTy2) (quote weakenMorCommutesLemmaTm2))
                                         (earg (var (n + 2) [])
                                        ∷ earg (var 1 [])
                                        ∷ earg (var 0 []) ∷ []))
                           ∷ []))
    thing T n 3 =
      earg (def (quote _∙_) (earg (def (Ty?Tm T weaken[]Ty weaken[]Tm)
                                         (earg (var (n + 2) [])
                                        ∷ earg (def (quote weakenMor+^) (earg (lit (nat 3)) ∷ earg (var 1 []) ∷ []))
                                        ∷ earg (iterate 3 (con (quote WeakPos.prev)) (var 0 [])) ∷ []))
                           ∷ earg (def (Ty?Tm T (quote weakenMorCommutesLemmaTy3) (quote weakenMorCommutesLemmaTm3))
                                         (earg (var (n + 2) [])
                                        ∷ earg (var 1 [])
                                        ∷ earg (var 0 []) ∷ []))
                           ∷ []))
    thing T n _ = earg unknown

weaken[]Ty : (A : TyExpr n) (δ : Mor m n) (k : WeakPos m) → weakenTy' k (A [ δ ]Ty) ≡ A [ weakenMor' k δ ]Ty
weaken[]Tm : (u : TmExpr n) (δ : Mor m n) (k : WeakPos m) → weakenTm' k (u [ δ ]Tm) ≡ u [ weakenMor' k δ ]Tm

weaken[]Var : (x : VarPos n) (δ : Mor m n) (k : WeakPos m) → weakenTm' k (x [ δ ]Var) ≡ x [ weakenMor' k δ ]Var
weaken[]Var last (δ , u) k = refl
weaken[]Var (prev x) (δ , u) k = weaken[]Var x δ k

unquoteDef weaken[]Ty weaken[]Tm = generate-weaken[] weaken[]Ty weaken[]Tm (quote weaken[]Var)

weaken[]Mor : (θ : Mor n k) (δ : Mor m n) (k : WeakPos m) → weakenMor' k (θ [ δ ]Mor) ≡ (θ [ weakenMor' k δ ]Mor)

weaken[]Mor ◇ _ k = refl
weaken[]Mor (θ , u) δ k rewrite weaken[]Mor θ δ k | weaken[]Tm u δ k = refl




{- Substituting a morphism where a term is inserted into a type/term/morphism that is weakened at that point does nothing -}

weakenTyInsertLemma : (k : WeakPos n) (A : TyExpr (suc n)) (δ : Mor m n) (t : TmExpr m)
  → weakenTy' (prev k) A [ weakenMor+ (insertMor k t δ) ]Ty ≡
    weakenTy' (prev k) A [ insertMor k (weakenTm t) (weakenMor δ) , var last ]Ty
weakenTyInsertLemma k A δ t = ap (λ z → weakenTy' (prev k) A [ z , var last ]Ty) (! (weakenCommutesInsert k last t δ))

weakenTyInsertLemma2 : (k : WeakPos n) (A : TyExpr (suc (suc n))) (δ : Mor m n) (t : TmExpr m)
  → weakenTy' (prev (prev k)) A [ weakenMor+^ 2 (insertMor k t δ) ]Ty ≡
    weakenTy' (prev (prev k)) A [ insertMor (prev (prev k)) (weakenTm (weakenTm t)) (weakenMor+^ 2 δ) ]Ty
weakenTyInsertLemma2 k A δ t = ap (λ z → weakenTy' (prev (prev k)) A [ z , var last ]Ty) (ap (λ z → weakenMor z , var (prev last)) (! (weakenCommutesInsert k last t δ)) ∙ ! (weakenCommutesInsert (prev k) last (weakenTm t) (weakenMor+ δ)))

weakenTyInsertLemma3 : (k : WeakPos n) (A : TyExpr (suc (suc (suc n)))) (δ : Mor m n) (t : TmExpr m)
  → weakenTy' (prev (prev (prev k))) A [ weakenMor+^ 3 (insertMor k t δ) ]Ty ≡
    weakenTy' (prev (prev (prev k))) A [ insertMor (prev (prev (prev k))) (weakenTm (weakenTm (weakenTm t))) (weakenMor+^ 3 δ) ]Ty
weakenTyInsertLemma3 k A δ t = ap (λ z → weakenTy' (prev (prev (prev k))) A [ weakenMor+ (weakenMor+ (z , var last))]Ty) (! (weakenCommutesInsert k last t δ))
                               ∙ weakenTyInsertLemma2 (prev k) A (weakenMor+ δ) (weakenTm t)

weakenTmInsertLemma : (k : WeakPos n) (u : TmExpr (suc n)) (δ : Mor m n) (t : TmExpr m)
  → weakenTm' (prev k) u [ weakenMor+ (insertMor k t δ) ]Tm ≡
    weakenTm' (prev k) u [ insertMor k (weakenTm t) (weakenMor δ) , var last ]Tm
weakenTmInsertLemma k u δ t = ap (λ z → weakenTm' (prev k) u [ z , var last ]Tm) (! (weakenCommutesInsert k last t δ))

weakenTmInsertLemma2 : (k : WeakPos n) (u : TmExpr (suc (suc n))) (δ : Mor m n) (t : TmExpr m)
  → weakenTm' (prev (prev k)) u [ weakenMor+^ 2 (insertMor k t δ) ]Tm ≡
    weakenTm' (prev (prev k)) u [ insertMor (prev (prev k)) (weakenTm (weakenTm t)) (weakenMor+^ 2 δ) ]Tm
weakenTmInsertLemma2 k u δ t = ap (λ z → weakenTm' (prev (prev k)) u [ z , var last ]Tm) (ap (λ z → weakenMor z , var (prev last)) (! (weakenCommutesInsert k last t δ)) ∙ ! (weakenCommutesInsert (prev k) last (weakenTm t) (weakenMor+ δ)))

weakenTmInsertLemma3 : (k : WeakPos n) (u : TmExpr (suc (suc (suc n)))) (δ : Mor m n) (t : TmExpr m)
  → weakenTm' (prev (prev (prev k))) u [ weakenMor+^ 3 (insertMor k t δ) ]Tm ≡
    weakenTm' (prev (prev (prev k))) u [ insertMor (prev (prev (prev k))) (weakenTm (weakenTm (weakenTm t))) (weakenMor+^ 3 δ) ]Tm
weakenTmInsertLemma3 k u δ t = ap (λ z → weakenTm' (prev (prev (prev k))) u [ weakenMor+ (weakenMor+ (z , var last))]Tm) (! (weakenCommutesInsert k last t δ))
                               ∙ weakenTmInsertLemma2 (prev k) u (weakenMor+ δ) (weakenTm t)


generate-weakenInsert : Name → Name → Name → TC ⊤
generate-weakenInsert weakenInsertTy weakenInsertTm weakenInsertVar =
  generateClausewise weakenInsertTy weakenInsertTm
    (earg (var "k") ∷ []) (earg (var "δ") ∷ earg (var "t") ∷ [])
    (λ l → def weakenInsertVar (earg (var 3 []) ∷ earg (var 2 []) ∷ earg (var 1 []) ∷ earg (var 0 []) ∷ []))
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
                                         (earg (con (quote WeakPos.prev) (earg (var (l + 2) []) ∷ []))
                                        ∷ earg (var (n + 2) [])
                                        ∷ earg (def (quote weakenMor+) (earg (var 1 []) ∷ []))
                                        ∷ earg (def (quote weakenTm) (earg (var 0 []) ∷ [])) ∷ []))
                           ∷ []))
    thing l T n 2 =
      earg (def (quote _∙_) (earg (def (Ty?Tm T (quote weakenTyInsertLemma2) (quote weakenTmInsertLemma2))
                                         (earg (var (l + 2) [])
                                        ∷ earg (var (n + 2) [])
                                        ∷ earg (var 1 [])
                                        ∷ earg (var 0 []) ∷ []))
                           ∷ earg (def (Ty?Tm T weakenInsertTy weakenInsertTm)
                                         (earg (iterate 2 (con (quote WeakPos.prev)) (var (l + 2) []))
                                        ∷ earg (var (n + 2) [])
                                        ∷ earg (def (quote weakenMor+^) (earg (lit (nat 2)) ∷ earg (var 1 []) ∷ []))
                                        ∷ earg (iterate 2 (def (quote weakenTm)) (var 0 [])) ∷ []))
                           ∷ []))
    thing l T n 3 =
      earg (def (quote _∙_) (earg (def (Ty?Tm T (quote weakenTyInsertLemma3) (quote weakenTmInsertLemma3))
                                         (earg (var (l + 2) [])
                                        ∷ earg (var (n + 2) [])
                                        ∷ earg (var 1 [])
                                        ∷ earg (var 0 []) ∷ []))
                           ∷ earg (def (Ty?Tm T weakenInsertTy weakenInsertTm)
                                         (earg (iterate 3 (con (quote WeakPos.prev)) (var (l + 2) []))
                                        ∷ earg (var (n + 2) [])
                                        ∷ earg (def (quote weakenMor+^) (earg (lit (nat 3)) ∷ earg (var 1 []) ∷ []))
                                        ∷ earg (iterate 3 (def (quote weakenTm)) (var 0 [])) ∷ []))
                           ∷ []))
    thing l T n _ = earg unknown

weakenTyInsert' : (k : WeakPos m) (A : TyExpr m) (δ : Mor n m) (t : TmExpr n) → weakenTy' k A [ insertMor k t δ ]Ty ≡ A [ δ ]Ty
weakenTmInsert' : (k : WeakPos m) (u : TmExpr m) (δ : Mor n m) (t : TmExpr n) → weakenTm' k u [ insertMor k t δ ]Tm ≡ u [ δ ]Tm

weakenVarInsert' : (k : WeakPos m) (x : VarPos m) (δ : Mor n m) (t : TmExpr n) → weakenVar' k x [ insertMor k t δ ]Var ≡ x [ δ ]Var
weakenVarInsert' last x δ t = refl
weakenVarInsert' (prev k) last (δ , u) t = refl
weakenVarInsert' (prev k) (prev x) (δ , u) t = weakenVarInsert' k x δ t

unquoteDef weakenTyInsert' weakenTmInsert' = generate-weakenInsert weakenTyInsert' weakenTmInsert' (quote weakenVarInsert')


weakenTyInsert : (A : TyExpr m) (δ : Mor n m) (t : TmExpr n) → weakenTy A [ δ , t ]Ty ≡ A [ δ ]Ty
weakenTyInsert A δ t = weakenTyInsert' last A δ t

weakenTmInsert : (u : TmExpr m) (δ : Mor n m) (t : TmExpr n) → weakenTm u [ δ , t ]Tm ≡ u [ δ ]Tm
weakenTmInsert u δ t = weakenTmInsert' last u δ t



weakenMorInsert : (θ : Mor n m) (δ : Mor k n) (t : TmExpr k) →  weakenMor θ [ δ ,  t ]Mor ≡ θ [ δ ]Mor
weakenMorInsert ◇ _ _ = refl
weakenMorInsert (θ , u) δ t rewrite weakenMorInsert θ δ t | weakenTmInsert u δ t = refl

weakenMorInsert' : (θ : Mor n m) (δ : Mor k (suc n)) → weakenMor θ [ δ ]Mor ≡ θ [ getLHS δ ]Mor
weakenMorInsert' ◇ _  = refl
weakenMorInsert' θ (δ , t) = weakenMorInsert θ δ t

weakenMorInsert'' : (k : WeakPos m) (θ : Mor m l) (δ : Mor n m)  (t : TmExpr n) → weakenMor' k θ [ insertMor k t δ ]Mor ≡ θ [ δ ]Mor
weakenMorInsert'' k ◇ δ t = refl
weakenMorInsert'' k (θ , u) δ t = Mor+= (weakenMorInsert'' k θ δ t) (weakenTmInsert' k u δ t)


[weakenMor]Mor : (δ : Mor n m) (θ : Mor m l) → (weakenMor θ [ weakenMor+ δ ]Mor) ≡ weakenMor (θ [ δ ]Mor)
[weakenMor]Ty  : (δ : Mor n m) (C : TyExpr m) → (weakenTy C [ weakenMor+ δ ]Ty) ≡ weakenTy (C [ δ ]Ty)
[weakenMor]Tm  : (δ : Mor n m) (w : TmExpr m) → (weakenTm w [ weakenMor+ δ ]Tm) ≡ weakenTm (w [ δ ]Tm)

[weakenMor]Mor δ θ = weakenMorInsert θ (weakenMor δ) (var last) ∙ ! (weaken[]Mor θ δ last)
[weakenMor]Ty δ C = weakenTyInsert C (weakenMor δ) (var last) ∙ ! (weaken[]Ty C δ last)
[weakenMor]Tm δ w = weakenTmInsert w (weakenMor δ) (var last) ∙ ! (weaken[]Tm w δ last)

[weakenMor+]Mor-aux : (k : ℕ) {δ : Mor n m} {θ : Mor m l} → weakenMor+^ k θ [ weakenMor+^ k δ ]Mor ≡ weakenMor+^ k (θ [ δ ]Mor)
[weakenMor+]Mor-aux zero = refl
[weakenMor+]Mor-aux (suc k) = ap (λ z → z , var last) ([weakenMor]Mor _ _ ∙ ap weakenMor ([weakenMor+]Mor-aux k))

[weakenMor+]MorTy : (k : ℕ) (B : TyExpr (k + l)) {δ : Mor n m} {θ : Mor m l} → B [ weakenMor+^ k θ [ weakenMor+^ k δ ]Mor ]Ty ≡ B [ weakenMor+^ k (θ [ δ ]Mor) ]Ty
[weakenMor+]MorTy k B = ap (λ z → B [ z ]Ty) ([weakenMor+]Mor-aux k)

[weakenMor+]MorTm : (k : ℕ) (u : TmExpr (k + l)) {δ : Mor n m} {θ : Mor m l} → u [ weakenMor+^ k θ [ weakenMor+^ k δ ]Mor ]Tm ≡ u [ weakenMor+^ k (θ [ δ ]Mor) ]Tm
[weakenMor+]MorTm k u = ap (λ z → u [ z ]Tm) ([weakenMor+]Mor-aux k)

{- Substitution by the identity morphism does nothing -}

[idMor]Ty : (A : TyExpr n) → A [ idMor n ]Ty ≡ A
[idMor]Tm : (u : TmExpr n) → u [ idMor n ]Tm ≡ u
[idMor]Var : (x : VarPos n) → (var x) [ idMor n ]Tm ≡ var x

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
    (λ l → def []Var-assoc (earg (var (l + 1) []) ∷ earg (var l []) ∷ earg (var 0 []) ∷ []))
    (λ l → apify (thing (earg (var (l + 1) [])) (earg (var l []))) l)

   where

    thing : Arg Term → Arg Term → Name → ℕ → ℕ → Arg Term
    thing δ θ T n 0 =
      earg (def (Ty?Tm T []Ty-assoc []Tm-assoc) (δ ∷ θ ∷ earg (var n []) ∷ []))
    thing (arg _ δ) (arg _ θ) T n k =
      earg (def (quote _∙_) (earg (def (Ty?Tm T []Ty-assoc []Tm-assoc)
                                         (earg (iterate k (def (quote weakenMor+)) δ)
                                        ∷ earg (iterate k (def (quote weakenMor+)) θ)
                                        ∷ earg (var n []) ∷ []))
                           ∷ earg (def (Ty?Tm T (quote [weakenMor+]MorTy) (quote [weakenMor+]MorTm))
                                         (earg (lit (nat k)) ∷ earg (var n []) ∷ [])) ∷ []))

[]Ty-assoc : (δ : Mor n m) (θ : Mor m k) (A : TyExpr k) → (A [ θ ]Ty [ δ ]Ty) ≡ (A [ θ [ δ ]Mor ]Ty)
[]Tm-assoc : (δ : Mor n m) (θ : Mor m k) (u : TmExpr k) → u [ θ ]Tm [ δ ]Tm ≡ u [ θ [ δ ]Mor ]Tm

[]Var-assoc : (δ : Mor n m) (θ : Mor m k) (x : VarPos k) → var x [ θ ]Tm [ δ ]Tm ≡ var x [ θ [ δ ]Mor ]Tm
[]Var-assoc δ (θ , v) last = refl
[]Var-assoc δ (θ , v) (prev x) = []Var-assoc δ θ x

unquoteDef []Ty-assoc []Tm-assoc = generate-assoc []Ty-assoc []Tm-assoc (quote []Var-assoc)

[]Mor-assoc : (δ : Mor n m) (θ : Mor m k) (φ : Mor k l) → φ [ θ ]Mor [ δ ]Mor ≡ φ [ θ [ δ ]Mor ]Mor
[]Mor-assoc δ θ ◇ = refl
[]Mor-assoc δ θ (φ , w) rewrite []Mor-assoc δ θ φ | []Tm-assoc δ θ w = refl


{- Substituting a weakened term in a weaken type/term is the same as weakening the substitution -}

weakenCommutesSubstTy : (k : WeakPos n) (B : TyExpr (suc n)) (a : TmExpr n) → substTy (weakenTy' (prev k) B) (weakenTm' k a) ≡ weakenTy' k (substTy B a)
weakenCommutesSubstTy k B a = ap (λ z → substTy (weakenTy' (prev k) z) _) (! ([idMor]Ty B)) ∙
                              ap (λ z → substTy z _) (weaken[]Ty B (idMor _) _) ∙
                              []Ty-assoc _ _ B ∙
                              ap (λ z → B [ z [ (weakenMor' last (idMor _) , var last) , weakenTm' _ _ ]Mor , weakenTm' k a ]Ty) (! (weakenMorCommutes _ (idMor _))) ∙
                              ap (λ z → B [ z , weakenTm' _ _ ]Ty) (weakenMorInsert _ _ _ ∙ [idMor]Mor (weakenMor' _ (idMor _))) ∙
                              ! (weaken[]Ty B (idMor _ , _) _)

weakenCommutesSubstTm : (k : WeakPos n) (u : TmExpr (suc n)) (a : TmExpr n) → substTm (weakenTm' (prev k) u) (weakenTm' k a) ≡ weakenTm' k (substTm u a)
weakenCommutesSubstTm k u a = ap (λ z → substTm (weakenTm' (prev k) z) _) (! ([idMor]Tm u)) ∙
                              ap (λ z → substTm z _ ) (weaken[]Tm u (idMor _) _) ∙ 
                              []Tm-assoc ((weakenMor' last (idMor _) , var last) , weakenTm' _ _) (weakenMor' (prev k) (weakenMor' last (idMor _)) , var last) u ∙
                              ap (λ z → u [ z [ (weakenMor' last (idMor _) , var last) , weakenTm' _ _ ]Mor , weakenTm' k a ]Tm) (! (weakenMorCommutes _ (idMor _))) ∙ 
                              ap (λ z → u [ z , weakenTm' _ _ ]Tm) (weakenMorInsert _ _ _ ∙ [idMor]Mor (weakenMor' _ (idMor _))) ∙
                              ! (weaken[]Tm u (idMor _ , _) _)

weakenSubstTy : (A : TyExpr n) (t : TmExpr n) → substTy (weakenTy A) t ≡ A
weakenSubstTy A u = weakenTyInsert A (idMor _) u ∙ ([idMor]Ty _)

weakenSubstTm : (u : TmExpr n) (t : TmExpr n) → substTm (weakenTm u) t ≡ u
weakenSubstTm u t = weakenTmInsert u (idMor _) t ∙ ([idMor]Tm _)

{- Total substitution commutes with partial substitution -}

[]Ty-substTy : {B : TyExpr (suc m)} {a : TmExpr m} {δ : Mor n m} → (substTy B a) [ δ ]Ty ≡ substTy (B [ weakenMor+ δ ]Ty) (a [ δ ]Tm)
[]Ty-substTy {B = B} {a} {δ} = []Ty-assoc _ _ _ ∙ ap (λ z → B [ z , a [ δ ]Tm ]Ty) (idMor[]Mor δ ∙ ! ([idMor]Mor δ) ∙ ! (weakenMorInsert _ _ _)) ∙ ! ([]Ty-assoc _ _ _)

-- -- "Failed to give" error
-- substCommutes[]Ty : (B : TyExpr (suc m)) (a : TmExpr m) (δ : Mor n m) → substTy (B [ weakenMor+ δ ]Ty) (a [ δ ]Tm) ≡ (substTy B a) [ δ ]Ty
-- substCommutes[]Ty B a δ = []Ty-assoc _ _ _ ∙ {!? ∙ ! ([]Ty-assoc _ _ _)!}

[]Tm-substTm : (u : TmExpr (suc m)) {a : TmExpr m} {δ : Mor n m} → (substTm u a) [ δ ]Tm ≡ substTm (u [ weakenMor+ δ ]Tm) (a [ δ ]Tm)
[]Tm-substTm u {a} {δ} = []Tm-assoc _ _ u ∙ ap (λ z → u [ z , a [ δ ]Tm ]Tm) (idMor[]Mor δ ∙ ! ([idMor]Mor δ) ∙ ! (weakenMorInsert _ _ _)) ∙ ! ([]Tm-assoc _ _ u)

insertIdMor : (k  : WeakPos n) → insertMor k (var (WeakPosToVarPos k)) (weakenMor' k (idMor n)) ≡ idMor (suc n)
insertIdMor last = refl
insertIdMor {n = suc n} (prev k) = Mor+= ((ap (λ z → insertMor k (var (prev (WeakPosToVarPos k))) z) (! (weakenMorCommutes k (idMor n))) ∙ weakenCommutesInsert k last (var (WeakPosToVarPos k)) (weakenMor' k (idMor n))) ∙ ap weakenMor (insertIdMor k))  refl

ap-substTy : {A A' : TyExpr (suc n)} {u u' : TmExpr n} → A ≡ A' → u ≡ u' → substTy A u ≡ substTy A' u'
ap-substTy refl refl = refl

weakenTy-substTy : {k : WeakPos m} {A : TyExpr (suc m)} {u : TmExpr m} → weakenTy' k (substTy A u) ≡ substTy (weakenTy' (prev k) A) (weakenTm' k u)
weakenTy-substTy {k = k} {A} {u} =
  weaken[]Ty A _ _
  ∙ ! (weakenTyInsert' (prev k) A _ (var (WeakPosToVarPos k)))
  ∙ ap (λ z → weakenTy' (prev k) A [ z , weakenTm' k u ]Ty)
       (insertIdMor k)

weakenTm-substTm : {k : WeakPos m} (t : TmExpr (suc m)) {u : TmExpr m} → weakenTm' k (substTm t u) ≡ substTm (weakenTm' (prev k) t) (weakenTm' k u)
weakenTm-substTm {k = k} t {u} =
  weaken[]Tm t _ _
  ∙ ! (weakenTmInsert' (prev k) t _ (var (WeakPosToVarPos k)))
  ∙ ap (λ z → weakenTm' (prev k) t [ z , weakenTm' k u ]Tm)
       (insertIdMor k)

{- Double substitutions -}

subst2Ty : TyExpr (suc (suc n)) → TmExpr n → TmExpr n → TyExpr n
subst2Ty A u v = A [ (idMor _ , u) , v ]Ty

subst2Ty=2substTy : {A : TyExpr (suc (suc n))} {u v : TmExpr n} → subst2Ty A u v ≡ substTy (A [ (weakenMor (idMor n , u)) , var last ]Ty) v
subst2Ty=2substTy {u = u} {v = v} = ! ([]Ty-assoc _ _ _ ∙ ap (_[_]Ty _) (Mor+= (Mor+= (weakenMorInsert _ _ _ ∙ (idMor[]Mor _)) (weakenTmInsert u _ _ ∙ [idMor]Tm _)) refl)) 

subst2Tm : TmExpr (suc (suc n)) → TmExpr n → TmExpr n → TmExpr n
subst2Tm t u v = t [ (idMor _ , u) , v ]Tm

ap-subst2Ty : {A A' : TyExpr (suc (suc n))} {u u' v v' : TmExpr n} → A ≡ A' → u ≡ u' → v ≡ v' → subst2Ty A u v ≡ subst2Ty A' u' v'
ap-subst2Ty refl refl refl = refl

[]Ty-substTy2 : {A : TyExpr (suc (suc m))} {u v : TmExpr m} {δ : Mor n m} → (subst2Ty A u v) [ δ ]Ty ≡ subst2Ty (A [ weakenMor+ (weakenMor+ δ) ]Ty) (u [ δ ]Tm) (v [ δ ]Tm)
[]Ty-substTy2 {A = A} {u} {v} {δ} = []Ty-assoc _ _ A ∙ ap (λ z → A [ (z , u [ δ ]Tm) , v [ δ ]Tm ]Ty) (idMor[]Mor δ ∙ ! ([idMor]Mor δ) ∙ ! (weakenMorInsert _ _ _) ∙ ! (weakenMorInsert _ _ _)) ∙ ! ([]Ty-assoc _ _ A)

subst2Ty-substTy : {A : TyExpr (suc m)} {u v : TmExpr m} {t : TmExpr (suc (suc m))} → subst2Ty (substTy (weakenTy' (prev last) (weakenTy' (prev last) A)) t) u v ≡ substTy A (subst2Tm t u v)
subst2Ty-substTy {A = A} {u} {v} {t} = []Ty-substTy ∙ ap-substTy (weakenTyInsert' (prev last) _ _ (weakenTm v) ∙ weakenTyInsert' (prev last) _ _ (weakenTm u) ∙ [idMor]Ty _) refl


[]Tm-substTm2 : (t : TmExpr (suc (suc m))) {u v : TmExpr m} {δ : Mor n m} → (subst2Tm t u v) [ δ ]Tm ≡ subst2Tm (t [ weakenMor+ (weakenMor+ δ) ]Tm) (u [ δ ]Tm) (v [ δ ]Tm)
[]Tm-substTm2 t {u} {v} {δ} = []Tm-assoc _ _ t ∙ ap (λ z → t [ (z , u [ δ ]Tm) , v [ δ ]Tm ]Tm) (idMor[]Mor δ ∙ ! ([idMor]Mor δ) ∙ ! (weakenMorInsert _ _ _) ∙ ! (weakenMorInsert _ _ _)) ∙ ! ([]Tm-assoc _ _ t)

weakenTm-subst2Tm : {k : WeakPos m} (t : TmExpr (suc (suc m))) {u v : TmExpr m} → weakenTm' k (subst2Tm t u v) ≡ subst2Tm (weakenTm' (prev (prev k)) t) (weakenTm' k u) (weakenTm' k v)
weakenTm-subst2Tm {k = k} t {u} {v} = ! ((ap (λ z → weakenTm' (prev (prev k)) t [ (z , weakenTm' k u) , weakenTm' k v ]Tm) (! (insertIdMor k)) ∙ weakenTmInsert' (prev (prev _)) t _ (var (WeakPosToVarPos k))) ∙ ! (weaken[]Tm t _ _))

{- Triple substitutions -}

subst3Ty : TyExpr (suc (suc (suc n))) → TmExpr n → TmExpr n → TmExpr n → TyExpr n
subst3Ty A u v w = A [ ((idMor _ , u) , v) , w ]Ty

subst3Ty=3substTy : {A : TyExpr (suc (suc (suc n)))} {u v w : TmExpr n} → subst3Ty A u v w ≡ substTy ((A [ (weakenMor (weakenMor (idMor n , u)) , var (prev last)) , var last ]Ty) [ weakenMor (idMor n , v) , var last ]Ty) w
subst3Ty=3substTy {u = u} {v = v} {w = w} = ! ([]Ty-assoc _ _ _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty _) (Mor+= (Mor+= (Mor+= (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _) (weakenTmInsert (weakenTm u) _ _ ∙ weakenTmInsert u _ _ ∙ ap (_[_]Tm u) (weakenMorInsert _ _ _ ∙ (idMor[]Mor _)) ∙ [idMor]Tm _)) (weakenTmInsert v _ _ ∙ ([idMor]Tm _))) refl)) 

ap-subst3Ty : {A A' : TyExpr (suc (suc (suc n)))} {u u' v v' w w' : TmExpr n} → A ≡ A' → u ≡ u' → v ≡ v' → w ≡ w' → subst3Ty A u v w ≡ subst3Ty A' u' v' w'
ap-subst3Ty refl refl refl refl = refl

[]Ty-subst3Ty : {A : TyExpr (suc (suc (suc m)))} {u v w : TmExpr m} {δ : Mor n m} → (subst3Ty A u v w) [ δ ]Ty ≡ subst3Ty (A [ weakenMor+ (weakenMor+ (weakenMor+ δ)) ]Ty) (u [ δ ]Tm) (v [ δ ]Tm) (w [ δ ]Tm)
[]Ty-subst3Ty {A = A} {u} {v} {w} {δ} = []Ty-assoc _ _ _ ∙ ap (λ z → A [ ((z , u [ δ ]Tm) , v [ δ ]Tm) , w [ δ ]Tm ]Ty) (! (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ [idMor]Mor δ ∙ ! (idMor[]Mor δ))) ∙ ! ([]Ty-assoc _ _ _)

substTy-subst3Ty : {A : TyExpr (suc (suc (suc m)))} {u v w : TmExpr (suc m)} {t : TmExpr m}
                 → substTy (subst3Ty (weakenTy' (prev (prev (prev last))) A) u v w) t
                   ≡ subst3Ty A (substTm u t) (substTm v t) (substTm w t)
substTy-subst3Ty {A = A} {u} {v} {w} {t} = []Ty-subst3Ty
                                           ∙ ap-subst3Ty (weakenTyInsert' (prev (prev (prev last))) A (idMor _) _ ∙ [idMor]Ty _)
                                                         refl
                                                         refl
                                                         refl

weakenTy-subst3Ty : {k : WeakPos m} {A : TyExpr (suc (suc (suc m)))} {u v w : TmExpr m}
                  → weakenTy' k (subst3Ty A u v w)
                    ≡ subst3Ty (weakenTy' (prev (prev (prev k))) A)
                               (weakenTm' k u) (weakenTm' k v) (weakenTm' k w)
weakenTy-subst3Ty {k = k} {A} {u} {v} {w} =
  weaken[]Ty A _ _
  ∙ ! (weakenTyInsert' (prev (prev (prev k))) A _ (var (WeakPosToVarPos k)))
  ∙ ap (λ z → weakenTy' (prev (prev (prev k))) A [ ((z , weakenTm' k u) , weakenTm' k v) , weakenTm' k w ]Ty)
       (insertIdMor k)

[]Ty-weakenTy : {δ : Mor n m} {A : TyExpr m} → (weakenTy A [ weakenMor+ δ ]Ty) ≡ weakenTy (A [ δ ]Ty)
[]Ty-weakenTy {A = A} = [weakenMor]Ty _ A

[]Ty-weakenTy1 : {δ : Mor n m} {A : TyExpr (suc m)} {u : TmExpr (suc (suc n))} {v : TmExpr (suc n)}
  → (weakenTy' (prev last) A [ (weakenMor (weakenMor δ) , u) , weakenTm' (prev last) v ]Ty) ≡ weakenTy' (prev last) (A [ weakenMor δ , v ]Ty)
[]Ty-weakenTy1 {δ = δ} {A} {u} {v} = weakenTyInsert' (prev last) A (weakenMor (weakenMor δ) , _) u ∙ ap (λ z → A [ z , _ ]Ty) (weakenMorCommutes last δ) ∙ ! (weaken[]Ty A (weakenMor δ , _) (prev last))

[]Ty-weakenTy1-weakenTy1 : {δ : Mor n m} {A : TyExpr (suc m)} → weakenTy' (prev last) (weakenTy' (prev last) A) [ weakenMor+ (weakenMor+ (weakenMor+ δ)) ]Ty ≡ weakenTy' (prev last) (weakenTy' (prev last) (A [ weakenMor+ δ ]Ty))
[]Ty-weakenTy1-weakenTy1 = ([]Ty-weakenTy1 ∙ ap (weakenTy' (prev last)) []Ty-weakenTy1)

[]Ty-weakenTy2 : {δ : Mor n m} {A : TyExpr (suc (suc m))} → (weakenTy' (prev (prev last)) A [ weakenMor+ (weakenMor+ (weakenMor+ δ)) ]Ty) ≡ weakenTy' (prev (prev last)) (A [ weakenMor+ (weakenMor+ δ) ]Ty)
[]Ty-weakenTy2 {A = A} = (weakenTyInsert' _ _ _ _ ∙ ap (λ z → A [ (z , _) , _ ]Ty) (ap (weakenMor' last) (weakenMorCommutes _ _) ∙ weakenMorCommutes _ _)) ∙ ! (weaken[]Ty A _ _)

[]Ty-weakenTy3 : {δ : Mor n m} {A : TyExpr (suc (suc (suc m)))} → (weakenTy' (prev (prev (prev last))) A [ weakenMor+ (weakenMor+ (weakenMor+ (weakenMor+ δ))) ]Ty) ≡ weakenTy' (prev (prev (prev last))) (A [ weakenMor+ (weakenMor+ (weakenMor+  δ)) ]Ty)
[]Ty-weakenTy3 {A = A} = (weakenTyInsert' _ _ _ _ ∙ ap (λ z → A [ ((z , _) , _) , _ ]Ty) (ap (weakenMor' last) (ap (weakenMor' last) (weakenMorCommutes _ _) ∙ weakenMorCommutes _ _) ∙ weakenMorCommutes _ _)) ∙ ! (weaken[]Ty A _ _)

weakenTy-weakenTy : {k : WeakPos n} {A : TyExpr n} → weakenTy' (prev k) (weakenTy A) ≡ weakenTy (weakenTy' k A)
weakenTy-weakenTy = ! (weakenTyCommutes _ last≤)

weakenTy-weakenTy1 : {k : WeakPos n} {A : TyExpr (1 + n)} → weakenTy' (prev (prev k)) (weakenTy' (prev last) A) ≡ weakenTy' (prev last) (weakenTy' (prev k) A)
weakenTy-weakenTy1 = ! (weakenTyCommutesprev1 _ _)

weakenTy-weakenTy-weakenTy1 : {k : WeakPos n} {A : TyExpr (1 + n)} → weakenTy' (prev (prev (prev k))) (weakenTy' (prev last) (weakenTy' (prev last) A)) ≡ weakenTy' (prev last) (weakenTy' (prev last) (weakenTy' (prev k) A))
weakenTy-weakenTy-weakenTy1 = weakenTy-weakenTy1 ∙ ap (weakenTy' (prev last)) weakenTy-weakenTy1

weakenTy-weakenTy2 : {k : WeakPos n} {A : TyExpr (2 + n)} → weakenTy' (prev (prev (prev k))) (weakenTy' (prev (prev last)) A) ≡ weakenTy' (prev (prev last)) (weakenTy' (prev (prev k)) A)
weakenTy-weakenTy2 = ! (weakenTyCommutesprev2 _ _)

weakenTy-weakenTy3 : {k : WeakPos n} {A : TyExpr (3 + n)} → weakenTy' (prev (prev (prev (prev k)))) (weakenTy' (prev (prev (prev last))) A) ≡ weakenTy' (prev (prev (prev last))) (weakenTy' (prev (prev (prev k))) A)
weakenTy-weakenTy3 = ! (weakenTyCommutesprev3 _ _)

[]Tm-weakenTm : {δ : Mor n m} (u : TmExpr m) → (weakenTm u [ weakenMor+ δ ]Tm) ≡ weakenTm (u [ δ ]Tm)
[]Tm-weakenTm u = [weakenMor]Tm _ u

[]Mor-weakenMor : {δ : Mor n m} (θ : Mor m l) → (weakenMor θ [ weakenMor+ δ ]Mor) ≡ weakenMor (θ [ δ ]Mor)
[]Mor-weakenMor θ = [weakenMor]Mor _ θ

substTy-weakenTy' : {k : WeakPos m} {A : TyExpr m} {δ : Mor n m} {t : TmExpr n} → weakenTy' k A [ insertMor k t δ ]Ty ≡ A [ δ ]Ty
substTy-weakenTy' = weakenTyInsert' _ _ _ _

substTy-weakenTy : {A : TyExpr n} {u : TmExpr n} → substTy (weakenTy A) u ≡ A
substTy-weakenTy = weakenTyInsert _ _ _ ∙ [idMor]Ty _

subst2Ty-weakenTy : {A : TyExpr n} {u v : TmExpr n} → subst2Ty (weakenTy (weakenTy A)) u v ≡ A
subst2Ty-weakenTy = weakenTyInsert _ _ _ ∙ substTy-weakenTy

subst2Ty-weakenTy1 : {A : TyExpr (suc n)} {u v : TmExpr n} → subst2Ty (weakenTy A) u v ≡ substTy A u
subst2Ty-weakenTy1 = weakenTyInsert _ _ _

-- we don't use this
-- subst2Ty-weakenTy2 : {A : TyExpr (suc n)} {u v : TmExpr n} → subst2Ty (weakenTy' (prev last) A) u v ≡ substTy A v
-- subst2Ty-weakenTy2 = weakenTyInsert' _ _ _ _

substTy-substTy : {A : TyExpr (suc (suc n))} {u : TmExpr (suc n)} {v : TmExpr n} → substTy (substTy A u) v ≡ subst2Ty A v (substTm u v)
substTy-substTy {A = A} {u} {v} = []Ty-assoc _ _ _ ∙ ap (λ z → A [ (z , _) , substTm u v ]Ty) (weakenMorInsert _ _ _ ∙ idMor[]Mor _)

weakenTy-to-[]Ty : {A : TyExpr n} → weakenTy A ≡ A [ weakenMor (idMor n) ]Ty
weakenTy-to-[]Ty = ap weakenTy (! ([idMor]Ty _)) ∙ weaken[]Ty _ _ _

weakenTy+-to-[]Ty : {A : TyExpr (suc n)} → weakenTy' (prev last) A ≡ A [ weakenMor+ (weakenMor (idMor n)) ]Ty
weakenTy+-to-[]Ty = ap (weakenTy' (prev last)) (! ([idMor]Ty _)) ∙ weaken[]Ty _ _ _ ∙ ap (λ z → _ [ z , var last ]Ty) (! (weakenMorCommutes _ _))

weakenTy+++-to-[]Ty : {A : TyExpr (suc (suc (suc n)))} → weakenTy' (prev (prev (prev last))) A ≡ A [ weakenMor+ (weakenMor+ (weakenMor+ (weakenMor (idMor n)))) ]Ty
weakenTy+++-to-[]Ty = ap (weakenTy' (prev (prev (prev last)))) (! ([idMor]Ty _)) ∙ weaken[]Ty _ _ _ ∙ ap (λ z → _ [ ((z , var (prev (prev last))) , var (prev last)) , var last ]Ty) (! (weakenMorCommutes _ _) ∙ ap weakenMor (! (weakenMorCommutes _ _) ∙ ap weakenMor (! (weakenMorCommutes _ _))))

weakenTm-to-[]Tm : {u : TmExpr n} → weakenTm u ≡ u [ weakenMor (idMor n) ]Tm
weakenTm-to-[]Tm {u = u} = ap weakenTm (! ([idMor]Tm _)) ∙ weaken[]Tm u _ _

weakenMor-to-[]Mor : {δ : Mor m n} → weakenMor δ ≡ δ [ weakenMor (idMor _) ]Mor
weakenMor-to-[]Mor {δ = δ} = ap weakenMor (! ([idMor]Mor _)) ∙ weaken[]Mor δ _ _ 

ap-[]Ty : {A A' : TyExpr n} {δ δ' : Mor m n} → A ≡ A' → δ ≡ δ' → A [ δ ]Ty ≡ A' [ δ' ]Ty
ap-[]Ty refl refl = refl

ap-[]Tm : {u u' : TmExpr n} {δ δ' : Mor m n} → u ≡ u' → δ ≡ δ' → u [ δ ]Tm ≡ u' [ δ' ]Tm
ap-[]Tm refl refl = refl

ap-[]Mor : {θ θ' : Mor n k} {δ δ' : Mor m n} → θ ≡ θ' → δ ≡ δ' → θ [ δ ]Mor ≡ θ' [ δ' ]Mor
ap-[]Mor refl refl = refl


{- Extracting types from contexts -}

getTy : {n : ℕ} (k : VarPos n) → Ctx n → TyExpr n
getTy last (Γ , A) = weakenTy A
getTy (prev k) (Γ , A) = weakenTy (getTy k Γ)

weaken-getTy : (k : WeakPos n) (k' : VarPos n) (Γ : Ctx n) (T : TyExpr (n -WeakPos k)) → weakenTy' k (getTy k' Γ) ≡ getTy (weakenVar' k k') (weakenCtx k Γ T)
weaken-getTy last last (Γ , A) T = refl
weaken-getTy (prev k) last (Γ , A) T = weakenTy-weakenTy
weaken-getTy last (prev k') (Γ , A) T = refl
weaken-getTy (prev k) (prev k') (Γ , A) T = weakenTy-weakenTy ∙ ap weakenTy (weaken-getTy k k' Γ T)
