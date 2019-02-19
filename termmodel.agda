{-# OPTIONS --rewriting --prop --without-K --allow-unsolved-metas #-}

open import common
open import typetheory
open import syntx
open import rules
open import contextualcat
open import quotients

{- Unfinished attempt to use reflection to automatically get the type of the StrSNat things

open import reflection hiding (proj)

expl : Type → Type
expl (pi (arg (arg-info v r) A) (abs s B)) = pi (arg (arg-info visible r) A) (abs s (expl B))
expl T = T

apply : Term → Term → TC Term
apply (def f args) a = return (def f (arg (arg-info visible relevant) a ∷ args))
apply f a = typeError (strErr "Do not know how to apply" ∷ [])

{- Given [u] of type [expl hole], returns a term of type [hole] -}
convert : ℕ → Term → Type → TC Term
convert k u (pi (arg (arg-info v r) A) (abs s B)) = do
  u' ← apply u (var k [])
  u'' ← convert (suc k) u' B
  return (lam v (abs s u''))
convert k u T = return u

is-in : Name → List (Arg Name) → Bool
is-in _ [] = false
is-in s (arg _ s' ∷ ss) = if primQNameEquality s s' then true else is-in s ss

myreduce : List (Arg Name) → Term → TC Term
mapMyreduce : List (Arg Name) → List (Arg Term) → TC (List (Arg Term))

myreduce fields (pi (arg i A) (abs s B)) = do
  A' ← myreduce fields A
  B' ← extendContext (arg i A') (myreduce fields B)
  return (pi (arg i A') (abs s B'))
myreduce fields t@(def f args) =
  if is-in f fields then
    normalise t
  else (do
    args' ← mapMyreduce fields args
    return (def f args'))
myreduce fields t@(var f args) =
  do
    args' ← mapMyreduce fields args
    return (var f args')
myreduce fields t = return t

mapMyreduce fields [] = return []
mapMyreduce fields (arg i u ∷ us) = do
  u' ← myreduce fields u
  us' ← mapMyreduce fields us
  return (arg i u' ∷ us')

getClauses : List Clause → TC (List (ΣSS Name (λ _ → Term)))
getClauses [] = return []
getClauses (clause (arg _ (reflection.proj f) ∷ _) t ∷ cs) = do
  ls ← getClauses cs
  return ((f , t) ∷ ls)
getClauses (_ ∷ cs) = getClauses cs

print : List (ΣSS Name (λ _ → Term)) → List ErrorPart
print [] = strErr "END" ∷ []
print ((n , t) ∷ ls) = nameErr n ∷ strErr " // " ∷ termErr t ∷ strErr " \\ " ∷ print ls

macro
  explicitify : Name → Term → Term → TC ⊤   -- u is of type [expl] of the type of the hole
  explicitify rec u hole = do
    function cs ← getDefinition rec
      where _ → typeError (strErr "Not a function." ∷ [])
    l ← getClauses cs
    typeError (strErr "START" ∷ print l)
    def t _ ← getType rec
      where _ → typeError (strErr "Problem." ∷ [])
    record-type _ fields ← getDefinition t
      where _ → typeError (strErr "Not a record type." ∷ [])
    T ← inferType hole
    T' ← myreduce fields T
    u' ← checkType u (expl T')
    u'' ← convert 0 u' T
    unify hole u''

 End of reflection thing -}

open CCat hiding (Mor) renaming (id to idC)

{- Preliminary definitions -}

record DCtx (n : ℕ) : Set where
  constructor _,_
  field
    ctx : Ctx n
    der : ⊢ ctx
open DCtx public

record DMor (n m : ℕ) : Set where
  constructor dmor
  field
    lhs : DCtx n
    rhs : DCtx m
    mor : Mor n m
    morDer : ctx lhs ⊢ mor ∷> ctx rhs
open DMor public

{-
Defining _Ob≃_ as a datatype as follows rather than being equal to ⊢ ctx Γ == ctx Γ'
allows us to have more arguments implicit.
The reason is that if you want to solve the definitional equality
   (Γ ≃ Γ') = (Δ ≃ Δ')
you get that Γ = Δ and Γ' = Δ' rather than simply ctx Γ = ctx Δ and ctx Γ' = ctx Δ'.
-}

data _Ob≃_ (Γ Γ' : DCtx n) : Prop where
  box : ⊢ ctx Γ == ctx Γ' → Γ Ob≃ Γ'

unOb≃ : {Γ Γ' : DCtx n} → Γ Ob≃ Γ' → ⊢ ctx Γ == ctx Γ'
unOb≃ (box x) = x

data _Mor≃_ (δ δ' : DMor n m) : Prop where
  box : ⊢ ctx (lhs δ) == ctx (lhs δ') → ⊢ ctx (rhs δ) == ctx (rhs δ') → ctx (lhs δ) ⊢ mor δ == mor δ' ∷> ctx (rhs δ) → δ Mor≃ δ'

unMor≃-lhs : {δ δ' : DMor n m} → δ Mor≃ δ' → ⊢ ctx (lhs δ) == ctx (lhs δ')
unMor≃-lhs (box x _ _) = x

unMor≃-rhs : {δ δ' : DMor n m} → δ Mor≃ δ' → ⊢ ctx (rhs δ) == ctx (rhs δ')
unMor≃-rhs (box _ x _) = x

unMor≃-mor : {δ δ' : DMor n m} → δ Mor≃ δ' → ctx (lhs δ) ⊢ mor δ == mor δ' ∷> ctx (rhs δ)
unMor≃-mor (box _ _ x) = x

instance
  ObEquiv : {n : ℕ} → EquivRel (DCtx n)
  EquivRel._≃_ ObEquiv Γ Γ' = Γ Ob≃ Γ'
  EquivRel.ref ObEquiv Γ = box (CtxRefl (der Γ))
  EquivRel.sym ObEquiv (box p) = box (CtxSymm p)
  EquivRel.tra ObEquiv (box p) (box q) = box (CtxTran p q)

  MorEquiv : {n m : ℕ} → EquivRel (DMor n m)
  EquivRel._≃_ MorEquiv δ δ' = δ Mor≃ δ'
  EquivRel.ref MorEquiv δ = box (CtxRefl (der (lhs δ))) (CtxRefl (der (rhs δ))) (MorRefl (morDer δ))
  EquivRel.sym MorEquiv (box Γ= Δ= δ=) = box (CtxSymm Γ=) (CtxSymm Δ=) (ConvMorEq (MorSymm (CtxEqCtx1 Γ=) (CtxEqCtx1 Δ=) δ=) Γ= Δ=)
  EquivRel.tra MorEquiv (box Γ= Δ= δ=) (box Γ'= Δ'= δ'=) = box (CtxTran Γ= Γ'=) (CtxTran Δ= Δ'=) (MorTran (CtxEqCtx1 Γ=) (CtxEqCtx1 Δ=) δ= (ConvMorEq δ'= (CtxSymm Γ=) (CtxSymm Δ=)))

reflectOb : {Γ Γ' : DCtx n} → proj {R = ObEquiv} Γ ≡ proj Γ' → ⊢ ctx Γ == ctx Γ'
reflectOb p = unOb≃ (reflect p)

DCtx= : {Γ Γ' : Ctx n} {w₁ : _} {w₂ : _} → Γ ≡ Γ' → proj {R = ObEquiv} (Γ , w₁) ≡ proj (Γ' , w₂)
DCtx= refl = refl

DMor= : {Γ Γ' : Ctx m} {w₁ : _} {w₂ : _} {Δ Δ' : Ctx n} {w₃ : _} {w₄ : _} {δ δ' : Mor m n} {w₅ : _} {w₆ : _} → Γ ≡ Γ' → Δ ≡ Δ' → δ ≡ δ' → proj {R = MorEquiv} (dmor (Γ , w₁) (Δ , w₃) δ w₅) ≡ proj (dmor (Γ' , w₂) (Δ' , w₄) δ' w₆)
DMor= refl refl refl = refl

idMor+ : {Γ : Ctx n} {A : TyExpr n} {a : TmExpr n} → ⊢ Γ → Derivable (Γ ⊢ a :> A) → Γ ⊢ (idMor n , a) ∷> (Γ , A)
idMor+ dΓ da = (idMorDerivable dΓ , congTm (! ([idMor]Ty _)) refl da)

idMor+= : {Γ : Ctx n} {A : TyExpr n} {a a' : TmExpr n} → ⊢ Γ → Derivable (Γ ⊢ a == a' :> A) → Γ ⊢ (idMor n , a) == (idMor n , a') ∷> (Γ , A)
idMor+= dΓ da= = (MorRefl (idMorDerivable dΓ) , congTmEqTy (! ([idMor]Ty _)) da=)

{- helper function to extract data from DCtx/DMor -}
getCtx : (Γ : DCtx (suc n)) → Ctx n
getCtx ((Γ , _) , _) = Γ

getdCtx : (Γ : DCtx (suc n)) → ⊢ getCtx Γ
getdCtx ((_ , _) , (dΓ , _)) = dΓ

getTy : (X : DCtx (suc n)) → TyExpr n
getTy ((_ , A) , _) = A

getdTy : (Γ : DCtx (suc n)) → Derivable (getCtx Γ ⊢ getTy Γ)
getdTy ((_ , _) , (_ , dA)) = dA

getTm : (u : DMor m (suc n)) → TmExpr m
getTm u = getRHS (mor u)

getMor : (a : DMor m (suc n)) → Mor m n
getMor a = getLHS (mor a)

getdTm : (a : DMor m (suc n)) → Derivable (ctx (lhs a) ⊢ getTm a :> (getTy (rhs a) [ getMor a ]Ty))
getdTm (dmor _ ((_ , _) , _) (_ , _) (_ , da)) = da

getdMor : (a : DMor m (suc n)) → ctx (lhs a) ⊢ getMor a ∷> getCtx (rhs a)
getdMor (dmor _ ((_ , _) , _) (_ , _) (dδ , _)) = dδ



CtxTy=Ctx : {Γ : DCtx n} (A : DCtx (suc n)) (A= : proj {R = ObEquiv} (getCtx A , getdCtx A) ≡ proj Γ) → ⊢ ctx Γ , getTy A == ctx A
CtxTy=Ctx {Γ = Γ} A@((_ , _) , (_ , _)) A= = CtxSymm (reflectOb A=) ,, TyRefl (ConvTy (getdTy A) (reflectOb A=))

CtxTy=Ctx' : (Γ : DCtx (suc n)) → ⊢ (getCtx Γ , getTy Γ) == ctx Γ
CtxTy=Ctx' ((_ , _) , dΓ@(_ , _)) = CtxRefl dΓ

getCtx= : {Γ Γ' : DCtx (suc n)} (rΓ : Γ ≃ Γ') → ⊢ getCtx Γ == getCtx Γ'
getCtx= {Γ = (Γ , A) , _} {(Γ' , A') , _} (box (dΓ= , _ , _ , _ , _)) = dΓ=

getTy= : {Γ Γ' : DCtx (suc n)} (rΓ : Γ ≃ Γ') → Derivable (getCtx Γ  ⊢ getTy Γ == getTy Γ')
getTy= {Γ = (Γ , A) , (dΓ , A)} {(Γ' , A') , (dΓ' , dA')} (box (_ , _ , _ , dA= , _)) = dA=

dLHS : {Γ : Ctx m} {Δ : DCtx (suc n)} {δ : Mor m (suc n)} → Γ ⊢ δ ∷> ctx Δ → Γ ⊢ getLHS δ ∷> getCtx Δ
dLHS {Δ = (Δ , B) , (dΔ , dB)} {δ = δ , u} (dδ , du) = dδ

getLHS= : {Γ : Ctx m} {Δ : DCtx (suc n)} {δ δ' : Mor m (suc n)} → Γ  ⊢ δ == δ' ∷> ctx Δ → Γ ⊢ getLHS δ == getLHS δ' ∷> getCtx Δ
getLHS= {Δ = (Δ , B) , (dΔ , dB)} {δ = (δ , u)} {δ' = (δ' , u')} (dδ= , du=) = dδ=

getRHS= : {Γ : Ctx m} {Δ : DCtx (suc n)} {δ δ' : Mor m (suc n)} → Γ  ⊢ δ == δ' ∷> ctx Δ → Derivable (Γ ⊢ getRHS δ == getRHS δ' :> (getTy Δ [ getLHS δ ]Ty))
getRHS= {Δ = (Δ , B) , (dΔ , dB)} {δ = (δ , u)} {δ' = (δ' , u')} (dδ= , du=) = du=


{- The syntactic contextual category -}

ObS : ℕ → Set
ObS n = DCtx n // ObEquiv

MorS : ℕ → ℕ → Set
MorS n m = DMor n m // MorEquiv

∂₀S : {n m : ℕ} → MorS n m → ObS n
∂₀S = //-rec (λ δ → proj (lhs δ)) (λ r → eq (box (unMor≃-lhs r)))

∂₁S : {n m : ℕ} → MorS n m → ObS m
∂₁S = //-rec (λ δ → proj (rhs δ)) (λ r → eq (box (unMor≃-rhs r)))

idS-u : (n : ℕ) → DCtx n → DMor n n
idS-u n Γ = dmor Γ Γ (idMor n) (idMorDerivable (der Γ))

idS : (n : ℕ) → ObS n → MorS n n
idS n = //-rec (λ Γ → proj (idS-u n Γ)) (λ {(box r) → eq (box r r (MorRefl (idMorDerivable (CtxEqCtx1 r))))})

id₀S : (n : ℕ) (X : ObS n) → ∂₀S (idS n X) ≡ X
id₀S n = //-elimP (λ Γ → refl)

id₁S : (n : ℕ) (X : ObS n) → ∂₁S (idS n X) ≡ X
id₁S n = //-elimP (λ Γ → refl)

compS-//-u : (g : DMor m k) (f : DMor n m) (_ : ∂₁S (proj f) ≡ ∂₀S (proj g)) → DMor n k
compS-//-u g f p = dmor (lhs f) (rhs g) (mor g [ mor f ]Mor) (SubstMor (morDer g) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb p)))

compS-// : (g : DMor m k) (f : DMor n m) (_ : ∂₁S (proj f) ≡ ∂₀S (proj g)) → MorS n k
compS-// g f p = proj (compS-//-u g f p)

compS-eq : (g g' : DMor m k) (r : g ≃ g') (f f' : DMor n m) (r' : f ≃ f') (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj f') ≡ ∂₀S (proj g')) → compS-// g f p ≡ compS-// g' f' q
compS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ') (box dΓ= dΔ= dδ=) (dmor (Γ'' , dΓ'') (Δ'' , dΔ'') δ'' dδ'') (dmor (Γ''' , dΓ''') (Δ''' , dΔ''') δ''' dδ''') (box dΓ''= dΔ''= dδ''=) p q =
  eq (box dΓ''= dΔ= (SubstMorFullEq dΔ'' dΔ (ConvMor dδ' (CtxSymm (CtxTran (reflectOb p) dΓ=)) (CtxSymm dΔ=)) (ConvMorEq dδ= (CtxSymm (CtxTran (reflectOb p) (CtxRefl dΓ))) (CtxRefl dΔ)) dδ'' dδ''=))


compS : (g : MorS m k) (f : MorS n m) (_ : ∂₁S f ≡ ∂₀S g) → MorS n k
compS {m = m} {k = k} {n = n} =
 //-elim-PiS (λ g → //-elim-PiP (λ f p → compS-// g f p)
                        (λ {a} {b} r → compS-eq g g (ref g) a b r))
         (λ {a} {b} r → //-elimP-PiP (λ f → compS-eq a b r f f (ref f)))

comp₀S-// : (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) → ∂₀S (compS (proj g) (proj f) p) ≡ ∂₀S (proj f)
comp₀S-// g f p = refl

comp₀S : (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) → ∂₀S (compS g f p) ≡ ∂₀S f
comp₀S = //-elimP (λ g → //-elimP (comp₀S-// g))

comp₁S-// : (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) → ∂₁S (compS (proj g) (proj f) p) ≡ ∂₁S (proj g)
comp₁S-// g f p = refl

comp₁S : (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) → ∂₁S (compS g f p) ≡ ∂₁S g
comp₁S = //-elimP (λ g → //-elimP (comp₁S-// g))

ftS-// : {n : ℕ} → DCtx (suc n) → DCtx n
ftS-// Γ = (getCtx Γ , getdCtx Γ)

ftS-eq : {Γ Γ' : DCtx (suc n)} → Γ ≃ Γ' → proj {R = ObEquiv} (ftS-// Γ) ≡ proj (ftS-// Γ')
ftS-eq {Γ = (_ , _) , _} {(_ , _) , _} (box r) = eq (box (fst r))

ftS : {n : ℕ} → ObS (suc n) → ObS n
ftS = //-rec (λ X → proj (ftS-// X)) ftS-eq

ppS-// : (X : DCtx (suc n)) → MorS (suc n) n
ppS-// Γ = proj (dmor Γ (ftS-// Γ) (weakenMor (idMor _)) (ConvMor (WeakMor (getTy Γ) (idMorDerivable (getdCtx Γ))) (CtxTy=Ctx' Γ) (CtxRefl (getdCtx Γ)) ))
--ppS-// Γd@((Γ , A), (dΓ , dA)) = proj (dmor Γd (Γ , dΓ) (weakenMor (idMor n)) (WeakMor A (idMorDerivable dΓ)))

ppS-eq : {X X' : DCtx (suc n)} (_ : X ≃ X') → ppS-// X ≡ ppS-// X'
ppS-eq {X = (Γ , A), (dΓ , dA)} {(Γ' , A'), (dΓ' , dA')} (box (dΓ= , dA=)) = eq (box (dΓ= , dA=) dΓ= (MorRefl (WeakMor A (idMorDerivable dΓ))))

ppS : (X : ObS (suc n)) → MorS (suc n) n
ppS = //-rec ppS-// ppS-eq

pp₀S : (X : ObS (suc n)) → ∂₀S (ppS X) ≡ X
pp₀S = //-elimP (λ {((Γ , A), (dΓ , dA)) → refl})

pp₁S : (X : ObS (suc n)) → ∂₁S (ppS X) ≡ ftS X
pp₁S = //-elimP (λ {((Γ , A), (dΓ , dA)) → refl})

ptS : ObS 0
ptS = proj (◇ , tt)

pt-uniqueS : (X : ObS 0) → X ≡ proj (◇ , tt)
pt-uniqueS = //-elimP (λ {(◇ , tt) → eq (box tt)})

ptmorS : (X : ObS n) → MorS n 0
ptmorS = //-rec (λ Γ → proj (dmor Γ (◇ , tt) ◇ tt)) (λ r → eq (box (unOb≃ r) tt tt))

ptmor₀S : (X : ObS n) → ∂₀S (ptmorS X) ≡ X
ptmor₀S = //-elimP (λ Γ → refl)

ptmor₁S : (X : ObS n) → ∂₁S (ptmorS X) ≡ ptS
ptmor₁S = //-elimP (λ Γ → refl)

ptmor-uniqueS-// : (X : DCtx n) (f : DMor n 0) (p : ∂₀S (proj f) ≡ proj X) (q : ∂₁S (proj f) ≡ ptS) → proj f ≡ ptmorS (proj X)
ptmor-uniqueS-// X (dmor Γ (◇ , tt) ◇ tt) p q = eq (box (reflectOb p) tt tt)

ptmor-uniqueS : (X : ObS n) (f : MorS n 0) (p : ∂₀S f ≡ X) (q : ∂₁S f ≡ ptS) → f ≡ ptmorS X
ptmor-uniqueS = //-elimP (λ X → //-elimP (ptmor-uniqueS-// X))

id-rightS-// : (f : DMor n m) → compS (idS m (∂₁S (proj f))) (proj f) (! (id₀S m (∂₁S (proj f)))) ≡ (proj f)
id-rightS-// {m = m} (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) = DMor= refl refl (idMor[]Mor δ) --ap-irr (λ x z → proj (dmor (Γ , dΓ) (Δ , dΔ) x z)) (idMor[]Mor δ)

id-rightS : (f : MorS n m) → compS (idS m (∂₁S f)) f (! (id₀S m (∂₁S f))) ≡ f
id-rightS = //-elimP id-rightS-//

id-leftS-// : (f : DMor n m) → compS (proj f) (idS n (∂₀S (proj f))) (id₁S n (∂₀S (proj f))) ≡ (proj f)
id-leftS-// {n = n} (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) = DMor= refl refl ([idMor]Mor δ) --ap-irr (λ x z → proj (dmor (Γ , dΓ) (Δ , dΔ) x z)) ([idMor]Mor δ)

id-leftS : (f : MorS n m) → compS f (idS n (∂₀S f)) (id₁S n (∂₀S f)) ≡ f
id-leftS = //-elimP id-leftS-//

assocS-// : (h : DMor k l) (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj g) ≡ ∂₀S (proj h)) → compS (compS (proj h) (proj g) q) (proj f) (p ∙ ! (comp₀S (proj h) (proj g) q)) ≡ compS (proj h) (compS (proj g) (proj f) p) (comp₁S (proj g) (proj f) p ∙ q)
assocS-// (dmor (Θ' , dΘ') (Φ , dΦ) φ dφ) (dmor (Δ' , dΔ') (Θ , dΘ) θ dθ) (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) p q = DMor= refl refl ([]Mor-assoc δ θ φ)
  --ap-irr (λ x z → proj (dmor (Γ , dΓ) (Φ , dΦ) x z)) ([]Mor-assoc δ θ φ)

assocS : (h : MorS k l) (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) (q : ∂₁S g ≡ ∂₀S h) → compS (compS h g q) f (p ∙ ! (comp₀S h g q)) ≡ compS h (compS g f p) (comp₁S g f p ∙ q)
assocS = //-elimP (λ h → //-elimP (λ g → //-elimP (λ f → assocS-// h g f)))

starS-//-u : (f : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj f) ≡ ftS (proj X)) → DCtx (suc m)
starS-//-u f X p = ((ctx (lhs f) , getTy X [ mor f ]Ty) , (der (lhs f) , (SubstTy (getdTy X) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb p)))))

starS-// : (f : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj f) ≡ ftS (proj X)) → ObS (suc m)
starS-// f x p = proj (starS-//-u f x p)

starS-eq : (f g : DMor m n) (r : f ≃ g) (X Y : DCtx (suc n)) (r' : X ≃ Y) (p : ∂₁S (proj f) ≡ ftS (proj X)) (q : ∂₁S (proj g) ≡ ftS (proj Y)) → starS-// f X p ≡ starS-// g Y q
starS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ)
         (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ')
         (box dΓ= dΔ= dδ=)
         ((Γ'' , A) , (dΓ'' , dA))
         ((Δ'' , B) , (dΔ'' , dB))
         (box (dΓ''= , dA , dB , dA= , dA='))
         p q = eq (box (dΓ= ,, SubstTyFullEq dB (ConvMor dδ (CtxRefl dΓ) (CtxTran dΔ= (reflectOb q)))
                                                (ConvTyEq dA= dΓ''=)
                                                (ConvMorEq dδ= (CtxRefl dΓ) (CtxTran dΔ= (reflectOb q)))))

starS : (f : MorS m n) (X : ObS (suc n)) (_ : ∂₁S f ≡ ftS X) → ObS (suc m)
starS {m = m} {n = n} =
  //-elim-PiS (λ f → //-elim-PiP (starS-// f)
                         (λ r → starS-eq f f (ref f) _ _ r))
          (λ r → //-elimP-PiP (λ X → starS-eq _ _ r X X (ref X)))

qqS-// : (δ : DMor m n) (X : DCtx (suc n)) (_ : ∂₁S (proj δ) ≡ ftS (proj X)) → MorS (suc m) (suc n)
qqS-// f X p = proj (dmor (starS-//-u f X p) X (weakenMor+ (mor f)) (ConvMor
                                                                       (WeakMor+ (getdTy X)
                                                                        (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb p)))
                                                                       (CtxRefl ((der (lhs f)) , SubstTy (getdTy X) (ConvMor (morDer f) (CtxRefl (der (lhs f))) (reflectOb p)))) (CtxTy=Ctx' X)))

qqS-eq : (f g : DMor m n) (r : f ≃ g) (Γ Δ : DCtx (suc n)) (r' : Γ ≃ Δ) (p : ∂₁S (proj f) ≡ ftS (proj Γ)) (q : ∂₁S (proj g) ≡ ftS (proj Δ)) → qqS-// f Γ p ≡ qqS-// g Δ q
qqS-eq (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (dmor (Γ' , dΓ') (Δ' , dΔ') δ' dδ') (box dΓ= dΔ= dδ=) ((Γ'' , A) , (dΓ'' , dA)) ((Δ'' , B) , (dΔ'' , dB)) (box (dΓ''= , dA , dB , dA= , dA=')) p q = eq (((box (dΓ= , SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflectOb p)) , SubstTy dB (ConvMor dδ' (CtxRefl dΓ') (reflectOb q)) , SubstTyFullEq dB (ConvMor dδ (CtxRefl dΓ) (CtxTran dΔ= (reflectOb q))) (ConvTyEq dA= dΓ''=) (ConvMorEq dδ= (CtxRefl dΓ) (CtxTran dΔ= (reflectOb q))) , SubstTyFullEq dB (ConvMor dδ dΓ= (CtxTran dΔ= (reflectOb q))) (ConvTyEq dA= dΓ''=) (ConvMorEq dδ= dΓ= (CtxTran dΔ= (reflectOb q)))) (dΓ''= , dA , dB , dA= , dA=') (WeakMorEq _ (ConvMorEq dδ= (CtxRefl dΓ) (reflectOb p)) , congTmRefl (congTmTy (weaken[]Ty _ _ _) (VarLast (SubstTy dA (ConvMor dδ (CtxRefl dΓ) (reflectOb p))))) refl))))



qqS : (f : MorS m n) (X : ObS (suc n)) (_ : ∂₁S f ≡ ftS X) → MorS (suc m) (suc n)
qqS {m = m} {n = n} =
  //-elim-PiS
    (λ f → //-elim-PiP (qqS-// f)
                       (λ r → qqS-eq f f (ref f) _ _ r))
    (λ r → //-elimP-PiP (λ X → qqS-eq _ _ r X X (ref X)))


qq₀S-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → ∂₀S (qqS (proj f) (proj X) p) ≡ starS (proj f) (proj X) p
qq₀S-// f X@((Δ , A) , (dΔ , dA)) p = refl

qq₀S : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → ∂₀S (qqS f X p) ≡ starS f X p
qq₀S = //-elimP (λ f → //-elimP (qq₀S-// f))

qq₁S-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → ∂₁S (qqS (proj f) (proj X) p) ≡ proj X
qq₁S-// f X@((Δ , A) , (dΔ , dA)) p = refl

qq₁S : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → ∂₁S (qqS f X p) ≡ X
qq₁S = //-elimP (λ f → //-elimP (qq₁S-// f))

ssS-//-u : (f : DMor m (suc n)) → DMor m (suc m)
ssS-//-u {m = m} f = dmor (lhs f) ((ctx (lhs f) , getTy (rhs f) [ getMor f ]Ty) , (der (lhs f) , SubstTy (getdTy (rhs f)) (getdMor f))) (idMor _ , getTm f) (idMor+ (der (lhs f)) (getdTm f))

ssS-// : (f : DMor m (suc n)) → MorS m (suc m)
ssS-// f = proj (ssS-//-u f)

ssS-eq : {f f' : DMor m (suc n)} (_ : f ≃ f') → ssS-// f ≡ ssS-// f'
ssS-eq {m = m} {f = f@(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du))} {f'@(dmor (Γ' , dΓ') ((Δ' , B'), (dΔ' , dB')) (δ' , u') (dδ' , du'))} p@(box dΓ= (dΔ= , dB , dB' , dB= , dB=') (dδ= , du=))
  = eq {a = ssS-//-u f} {b = ssS-//-u f'} (box dΓ= (dΓ= ,, SubstTyMorEq2 dΓ dΔ dB= dδ=) (idMor+= dΓ du=))

ssS : (f : MorS m (suc n)) → MorS m (suc m)
ssS {n = n} = //-rec ssS-// ssS-eq

ss₀S : (f : MorS m (suc n)) → ∂₀S (ssS f) ≡ ∂₀S f
ss₀S = //-elimP (λ {(dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) → refl})

ss₁S-// : (f : DMor m (suc n)) → ∂₁S (ssS (proj f)) ≡ starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S _))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S _)) ∙ pp₁S (∂₁S (proj f)))
ss₁S-// (dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = DCtx= (ap (_,_ Γ) (ap (_[_]Ty B) (! (weakenMorInsert (idMor _) δ u ∙ idMor[]Mor δ)))) --ap-irr (λ x z → proj ((Γ , B [ x ]Ty) , z)) (! (weakenMorInsert (idMor _) δ u ∙ idMor[]Mor δ)) 

ss₁S : (f : MorS m (suc n)) → ∂₁S (ssS f) ≡ starS (compS (ppS (∂₁S f)) f (! (pp₀S _))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S _)) ∙ pp₁S (∂₁S f))
ss₁S = //-elimP ss₁S-//
 
ft-starS-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → ftS (starS (proj f) (proj X) p) ≡ ∂₀S (proj f)
ft-starS-// (dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) ((Δ , B), (dΔ , dB)) p = refl 

ft-starS : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → ftS (starS f X p) ≡ ∂₀S f
ft-starS = //-elimP (λ f → //-elimP (ft-starS-// f))

pp-qqS-// : (f : DMor m n) (X : DCtx (suc n)) (p : ∂₁S (proj f) ≡ ftS (proj X)) → compS (ppS (proj X)) (qqS (proj f) (proj X) p) (qq₁S (proj f) (proj X) p ∙ ! (pp₀S (proj X))) ≡ compS (proj f) (ppS (starS (proj f) (proj X) p)) (pp₁S (starS (proj f) (proj X) p) ∙ ft-starS (proj f) (proj X) p)
pp-qqS-// (dmor (Γ , dΓ) (Δ' , dΔ') δ dδ) ((Δ , B), (dΔ , dB)) p = eq (box (CtxRefl dΓ , SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflectOb p)) , SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflectOb p)) , TyRefl (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflectOb p))) , TyRefl (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflectOb p)))) (CtxSymm (reflectOb p)) (MorSymm (dΓ , (SubstTy dB (ConvMor dδ (CtxRefl dΓ) (reflectOb p)))) dΔ (congMorRefl ( ! (weaken[]Mor δ (idMor _) last) ∙ ap weakenMor ([idMor]Mor δ) ∙ ! ([weakenMor]Mor δ (idMor _) ∙ ap weakenMor (idMor[]Mor δ))) (SubstMor (ConvMor dδ (CtxRefl dΓ) (reflectOb p)) (WeakMor _ (idMorDerivable dΓ))))))

pp-qqS : (f : MorS m n) (X : ObS (suc n)) (p : ∂₁S f ≡ ftS X) → compS (ppS X) (qqS f X p) (qq₁S f X p ∙ ! (pp₀S X)) ≡ compS f (ppS (starS f X p)) (pp₁S (starS f X p) ∙ ft-starS f X p)
pp-qqS = //-elimP (λ f → //-elimP (pp-qqS-// f))

star-idS : {n : ℕ} (X : ObS (suc n)) → starS (idS n (ftS X)) X (id₁S n (ftS X)) ≡ X
star-idS = //-elimP (λ {((Γ , A), (dΓ , dA)) → DCtx= (ap (_,_ Γ) ([idMor]Ty A))}) --ap-irr (λ x z → proj ((Γ , x) , z)) ([idMor]Ty A)

qq-idS : (X : ObS (suc n)) → qqS (idS n (ftS X)) X (id₁S n (ftS X)) ≡ idS (suc n) X
qq-idS {n = n} = //-elimP (λ {((Γ , A), (dΓ , dA)) → DMor= (ap (_,_ Γ) ([idMor]Ty A)) refl refl}) --ap-irr2 (λ x z t → (proj (dmor ((Γ , x) , (dΓ , z)) ((Γ , A), (dΓ , dA)) (weakenMor' last (idMor n) , var last) t))) ([idMor]Ty A) {b = SubstTy dA (idMorDerivable dΓ)} {b' = dA} {c = (WeakMor (A [ idMor _ ]Ty) (idMorDerivable dΓ)) , (congTm (weaken[]Ty A (idMor n) last) refl (VarLast (congTy (! ([idMor]Ty _)) dA)))} {c' = (WeakMor A (idMorDerivable dΓ)) , (congTm (ap weakenTy (! ([idMor]Ty A)) ∙ weaken[]Ty A (idMor n) last) refl (VarLast dA))

star-compS-// : (g : DMor m k) (f : DMor n m) (X : DCtx (suc k)) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (q : ∂₁S (proj g) ≡ ftS (proj X)) → starS (compS (proj g) (proj f) p) (proj X) (comp₁S (proj g) (proj f) p ∙ q) ≡ starS (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q))
star-compS-// (dmor Δd@(Δ , dΔ) Θd θ dθ) (dmor Γd@(Γ , dΓ) Δd'@(Δ' , dΔ') δ dδ) ((Γ' , A), (dΓ' , dA)) p q = DCtx= (ap (_,_ Γ) (! ([]Ty-assoc _ _ _))) --ap-irr (λ x z → proj ((Γ , x), z)) (! ([]Ty-assoc δ θ A))

star-compS : (g : MorS m k) (f : MorS n m) (X : ObS (suc k)) (p : ∂₁S f ≡ ∂₀S g) (q : ∂₁S g ≡ ftS X) → starS (compS g f p) X (comp₁S g f p ∙ q) ≡ starS f (starS g X q) (p ∙ ! (ft-starS g X q))
star-compS = //-elimP (λ g → //-elimP (λ f → //-elimP (star-compS-// g f)))


qq-compS-// : (g : DMor m k) (f : DMor n m) (p : ∂₁S (proj f) ≡ ∂₀S (proj g)) (X : DCtx (suc k)) (q : ∂₁S (proj g) ≡ ftS (proj X)) → qqS (compS (proj g) (proj f) p) (proj X) (comp₁S (proj g) (proj f) p ∙ q) ≡ compS (qqS (proj g) (proj X) q) (qqS (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q))) (qq₁S (proj f) (starS (proj g) (proj X) q) (p ∙ ! (ft-starS (proj g) (proj X) q)) ∙ ! (qq₀S (proj g) (proj X) q))
qq-compS-// (dmor Δd@(Δ , dΔ) Θd θ dθ) (dmor Γd@(Γ , dΓ) Δd'@(Δ' , dΔ') δ dδ) p ((Γ' , A), (dΓ' , dA)) q = DMor= (ap (_,_ Γ) (! ([]Ty-assoc _ _ _))) refl (ap (λ z → z , var last) (weaken[]Mor _ _ _ ∙ ! (weakenMorInsert _ _ _ ))) --eq (((CtxRefl dΓ ,, congTyRefl (SubstTy dA (SubstMor (ConvMor dθ (CtxSymm (reflect p)) (reflect q)) dδ)) (! ([]Ty-assoc δ θ A))) , (CtxRefl dΓ' ,, TyRefl dA)) , (congMorRefl (weaken[]Mor _ _ _ ∙ ! (weakenMorInsert _ _ _)) (WeakMor _ (SubstMor (ConvMor dθ (CtxSymm (reflect p)) (reflect q)) dδ)) , TmRefl (weakenDerLast dA (SubstMor (ConvMor dθ (CtxSymm (reflect p)) (reflect q)) dδ))))

qq-compS : (g : MorS m k) (f : MorS n m) (p : ∂₁S f ≡ ∂₀S g) (X : ObS (suc k)) (q : ∂₁S g ≡ ftS X) → qqS (compS g f p) X (comp₁S g f p ∙ q) ≡ compS (qqS g X q) (qqS f (starS g X q) (p ∙ ! (ft-starS g X q))) (qq₁S f (starS g X q) (p ∙ ! (ft-starS g X q)) ∙ ! (qq₀S g X q))
qq-compS = //-elimP (λ g → //-elimP (λ f p → //-elimP λ X → qq-compS-// g f p X))


ss-ppS-// : {m n : ℕ} (f : DMor m (suc n)) → compS (ppS (starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f))))) (ssS (proj f)) (ss₁S (proj f) ∙ ! (pp₀S (starS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))))) ≡ idS m (∂₀S (proj f))
ss-ppS-// (dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = DMor= refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor _) --eq (((CtxRefl dΓ) , (CtxRefl dΓ)) , MorSymm dΓ dΓ (congMorRefl (! (weakenMorInsert (idMor _) (idMor _) u ∙ idMor[]Mor (idMor _))) (idMorDerivable dΓ)))

ss-ppS : {m n : ℕ} (f : MorS m (suc n)) → compS (ppS (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f)))) (ssS f) (ss₁S f ∙ ! (pp₀S (starS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))))) ≡ idS m (∂₀S f)
ss-ppS {m} {n} = //-elimP (ss-ppS-// {m} {n})

ss-qqS-// : {m n : ℕ} (f : DMor m (suc n)) → (proj f) ≡ compS (qqS (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))) (ssS (proj f)) (ss₁S (proj f) ∙ ! (qq₀S (compS (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f))))) (∂₁S (proj f)) (comp₁S (ppS (∂₁S (proj f))) (proj f) (! (pp₀S (∂₁S (proj f)))) ∙ pp₁S (∂₁S (proj f)))))
ss-qqS-// (dmor (Γ , dΓ) ((Δ , B), (dΔ , dB)) (δ , u) (dδ , du)) = DMor= refl refl (ap (λ z → z , u) (! (weakenMorInsert _ _ _ ∙ [idMor]Mor _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor δ))) -- eq ((CtxRefl dΓ , CtxRefl dΔ , dB , dB , (TyRefl dB) , (TyRefl dB)) , (congMorRefl (! (weakenMorInsert _ (idMor _) u ∙ [idMor]Mor _ ∙ weakenMorInsert _ δ u ∙ idMor[]Mor δ)) dδ) , (TmRefl du))

ss-qqS : {m n : ℕ} (f : MorS m (suc n)) → f ≡ compS (qqS (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))) (ssS f) (ss₁S f ∙ ! (qq₀S (compS (ppS (∂₁S f)) f (! (pp₀S (∂₁S f)))) (∂₁S f) (comp₁S (ppS (∂₁S f)) f (! (pp₀S (∂₁S f))) ∙ pp₁S (∂₁S f))))
ss-qqS = //-elimP ss-qqS-//

ss-compS-// : {m n k : ℕ} (U : DCtx (suc k)) (g : DMor n k) (f : DMor m (suc n)) (g₁ : ∂₁S (proj g) ≡ ftS (proj U)) (f₁ : ∂₁S (proj f) ≡ starS (proj g) (proj U) g₁) {-g₀ : ∂₀ g ≡ ft (∂₁ f)-} → ssS (proj f) ≡ ssS (compS (qqS (proj g) (proj U) g₁) (proj f) (! (qq₀S (proj g) (proj U) g₁ ∙ ! f₁)))
ss-compS-// U@((Γ , A), (dΓ , dA)) g@(dmor (Δg , dΔg) (Γg , dΓg) δ dδ) f@(dmor (Θ , dΘ) ((Δf , A[g]), (dΔf , dA[g])) (θ , u) (dθ , du)) g₁ f₁ =
                  let (dΔf=Δg , _ , _ , dA[g]=A[δ] , _) = reflectOb f₁
                  in
                  eq (box (CtxRefl dΘ) (CtxRefl dΘ ,, TyTran (SubstTy (SubstTy dA (ConvMor dδ (CtxSymm dΔf=Δg) (reflectOb g₁))) dθ) (SubstTyEq dA[g]=A[δ] dθ) (congTyEq (! ([]Ty-assoc _ _ _)) (ap (_[_]Ty A) (! (weakenMorInsert _ _ _))) (TyRefl (SubstTy dA (SubstMor (ConvMor dδ (CtxSymm dΔf=Δg) (reflectOb g₁)) dθ))))) (idMor+= dΘ (TmRefl du)))


ss-compS : {m n k : ℕ} (U : ObS (suc k)) (g : MorS n k) (f : MorS m (suc n)) (g₁ : ∂₁S g ≡ ftS U) (f₁ : ∂₁S f ≡ starS g U g₁) → ssS f ≡ ssS (compS (qqS g U g₁) f (! (qq₀S g U g₁ ∙ ! f₁)))
ss-compS = //-elimP (λ U → //-elimP (λ g → //-elimP (ss-compS-// U g)))

{- The syntactic contextual category -}

synCCat : CCat
Ob synCCat = ObS
CCat.Mor synCCat = MorS
∂₀ synCCat = ∂₀S
∂₁ synCCat = ∂₁S
CCat.id synCCat = idS _
id₀ synCCat {n = n} {X = X} = id₀S n X
id₁ synCCat {n = n} {X = X} = id₁S n X
comp synCCat g f g₀ f₁ = compS g f (f₁ ∙ ! g₀)
comp₀ synCCat {g = g} {f = f} {g₀ = g₀} {f₁ = f₁} = comp₀S g f (f₁ ∙ ! g₀)
comp₁ synCCat {g = g} {f = f} {g₀ = g₀} {f₁ = f₁} = comp₁S g f (f₁ ∙ ! g₀)
ft synCCat = ftS
pp synCCat = ppS
pp₀ synCCat {X = X} = pp₀S X
pp₁ synCCat {X = X} = pp₁S X
star synCCat f X q f₁ = starS f X (f₁ ∙ ! q)
qq synCCat f X q f₁ = qqS f X (f₁ ∙ ! q)
qq₀ synCCat {f = f} {X = X} {q = q} {f₁ = f₁} = qq₀S f X (f₁ ∙ ! q)
qq₁ synCCat {f = f} {X = X} {q = q} {f₁ = f₁} = qq₁S f X (f₁ ∙ ! q)
ss synCCat f = ssS f
ss₀ synCCat {f = f} = ss₀S f
ss₁ synCCat {f = f} refl = ss₁S f
pt synCCat = ptS
pt-unique synCCat = pt-uniqueS
ptmor synCCat = ptmorS
ptmor₀ synCCat {X = X} = ptmor₀S X
ptmor₁ synCCat {X = X} = ptmor₁S X
ptmor-unique synCCat = ptmor-uniqueS
id-right synCCat {f = f} refl = id-rightS f
id-left synCCat {f = f} refl = id-leftS f
assoc synCCat {h = h} {g = g} {f = f} {f₁ = f₁} {g₀ = g₀} {g₁ = g₁} {h₀ = h₀} = assocS h g f (f₁ ∙ ! g₀) (g₁ ∙ ! h₀)
ft-star synCCat {f = f} {X = X} {p = p} {f₁ = f₁} = ft-starS f X (f₁ ∙ ! p)
pp-qq synCCat {f = f} {X = X} {p = p} {f₁ = f₁} = pp-qqS f X (f₁ ∙ ! p)
star-id synCCat {X = X} {p = refl} = star-idS X
qq-id synCCat {X = X} {p = refl} = qq-idS X
star-comp synCCat {g = g} {f = f} {f₁ = f₁} {g₀ = g₀} {X = X} {p = p} {g₁ = g₁} = star-compS g f X (f₁ ∙ ! g₀) (g₁ ∙ ! p)
qq-comp synCCat {g = g} {f} {f₁ = f₁} {g₀ = g₀} {X = X} {p = p} {g₁ = g₁} = qq-compS g f (f₁ ∙ ! g₀) X (g₁ ∙ ! p)
ss-pp synCCat {f = f} refl {f₁ = refl} = ss-ppS f
ss-qq synCCat {f = f} {f₁ = refl} = ss-qqS f
ss-comp synCCat {U = U} {p = p} {g = g} {g₁ = g₁} {f = f} {f₁ = f₁} = ss-compS U g f (g₁ ∙ ! p) f₁


{- The syntactic structured contextual category. We start with some helper functions. -}

module S = CCat synCCat

sectionS-eq : {Γ Δ : Ctx n} {dΓ : ⊢ Γ} {A : TyExpr n} {dΔ : ⊢ Δ} {dA : Derivable (Δ ⊢ A)} {δ : Mor n n} {dδ : Γ ⊢ δ ∷> Δ} {u : TmExpr n} {du : Derivable (Γ ⊢ u :> A [ δ ]Ty)}
            → S.is-section (proj (dmor (Γ , dΓ) ((Δ , A), (dΔ , dA)) (δ , u) (dδ , du)))
            → Γ ⊢ δ == idMor n ∷> Δ
sectionS-eq uₛ with reflect (S.is-section= refl uₛ refl)
... | box _ dΔ= dδ= = congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor _) refl dδ=

sectionS-eq-ctx : {Γ Δ : Ctx n} {dΓ : ⊢ Γ} {A : TyExpr n} {dΔ : ⊢ Δ} {dA : Derivable (Δ ⊢ A)} {δ : Mor n n} {dδ : Γ ⊢ δ ∷> Δ} {u : TmExpr n} {du : Derivable (Γ ⊢ u :> A [ δ ]Ty)}
            → S.is-section (proj (dmor (Γ , dΓ) ((Δ , A), (dΔ , dA)) (δ , u) (dδ , du)))
            → ⊢ Δ == Γ
sectionS-eq-ctx uₛ with reflect (S.is-section= refl uₛ refl)
... | box dΓ= dΔ= dδ= = CtxSymm dΓ=

getMor=idMor' : {a : DMor n (suc n)} (aₛ : S.is-section (proj a)) → ctx (lhs a) ⊢ getMor a == idMor n ∷> getCtx (rhs a)
getMor=idMor' {a = dmor _ _ (δ , _) _} aₛ = congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor _) refl (unMor≃-mor (reflect (S.is-section= refl aₛ refl)))

morTm=idMorTm' : {a : DMor n (suc n)} (aₛ : S.is-section (proj a)) → ctx (lhs a) ⊢ mor a == idMor n , getRHS (mor a) ∷> (ctx (rhs a))
morTm=idMorTm' {a = dmor _ ((_ , _) , (_ , _)) (δ , _) (_ , du)} aₛ = (getMor=idMor' aₛ) , (TmRefl du)


dTy : {Γ : DCtx n} (A : DCtx (suc n)) (A= : proj {R = ObEquiv} (getCtx A , getdCtx A) ≡ proj Γ) → Derivable (ctx Γ ⊢ getTy A)
dTy ((_ , _ ) , (_ , dA)) dA= = ConvTy dA (reflectOb dA=)

dTy= : {Γ : DCtx n} {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : ftS (proj A) ≡ proj Γ) → Derivable (ctx Γ ⊢ getTy A == getTy A')
dTy= {A = ((ΓA , A) , (dΓA , dA))} {A' = ((ΓA' , A') , (dΓA' , dA'))} (box (_ , _ , _ , dA= , _)) A= = ConvTyEq dA= (reflectOb A=)


combine : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : ftS (proj B) ≡ proj A) → ftS (proj B) ≡ proj ((ctx Γ , getTy A) , (der Γ , dTy A A=))
combine {A = A} A= B B= = B= ∙ eq (box (CtxTran (CtxSymm (CtxTy=Ctx' A)) (reflectOb A= ,, TyRefl (getdTy A)) ))

dTy+ : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : ftS (proj B) ≡ proj A) → Derivable ((ctx Γ , getTy A) ⊢ getTy B)
dTy+ A= B B= = dTy B (combine A= B B=)

dTy+= : {Γ : DCtx n} {A  : DCtx (suc n)} {B B' : DCtx (suc (suc n))} (A= : ftS (proj A) ≡ proj Γ) (rB : B ≃ B') (B= : ftS (proj B) ≡ proj A) → Derivable ((ctx Γ , getTy A) ⊢ getTy B == getTy B')
dTy+= {B = B} A= rB B= = dTy= rB (combine A= B B=)

lemmathing : {Γ Δ : DCtx (suc n)} → Γ ≃ Δ → Derivable (ctx (ftS-// Δ) ⊢ getTy Γ == getTy Δ)
lemmathing {Γ = ((Γ , A) , (dΓ , dA))} {Δ = ((Δ , B) , (dΔ , dB))} (box (_ , _ , _ , _ , dA=)) = dA=


dMor : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) → ctx Γ ⊢ mor a ∷> (ctx Γ , getTy A)
dMor {A = A} A= a aₛ a₁ = ConvMor (morDer a) (reflectOb (S.is-section₀ aₛ a₁ ∙ A=)) (CtxTran (reflectOb a₁) (CtxSymm (CtxTy=Ctx A A=)))

--ConvMor (getdMor a) (reflectOb (S.is-section₀ aₛ a₁ ∙ A=)) (CtxTran (getCtx= (reflect a₁)) (reflectOb A=))

getMor=idMor : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) → ctx Γ ⊢ getMor a == idMor n ∷> ctx Γ
getMor=idMor A= a aₛ a₁ = ConvMorEq (getMor=idMor' aₛ) (reflectOb (S.is-section₀ aₛ a₁ ∙ A=)) (CtxTran (getCtx= (reflect a₁)) (reflectOb A=))

morTm=idMorTm : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A)  → ctx Γ ⊢ mor a == idMor n , getRHS (mor a) ∷> (ctx Γ , getTy A)
morTm=idMorTm {A = A} A= a aₛ a₁ = ConvMorEq (morTm=idMorTm' aₛ) (reflectOb (S.is-section₀ aₛ a₁ ∙ A=)) (CtxTran (reflectOb a₁) (CtxSymm (CtxTy=Ctx A A=)))

dTm : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) → Derivable (ctx Γ ⊢ getTm a :> getTy A)
dTm {A = A} A= a aₛ a₁ =
  let lhsa=Γ = reflectOb (S.is-section₀ aₛ a₁ ∙ A=)
      lhsa=ftA = reflectOb (S.is-section₀ aₛ a₁)     
  in
  ConvTm2 (getdTm a) lhsa=Γ (TyTran (ConvTy (getdTy (rhs a)) (CtxTran (getCtx= (reflect a₁)) (CtxSymm (lhsa=ftA)))) (congTyEq refl ([idMor]Ty _) (SubstTyMorEq (getdTy (rhs a)) (getdMor a) (getMor=idMor' aₛ))) (ConvTyEq (lemmathing (reflect a₁)) (CtxSymm lhsa=ftA)))
                        
dTmSubst : {Γ : DCtx n} {A : DCtx (suc n)} (A= : S.ft (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : S.ft (proj B) ≡ proj A) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : S.∂₁ (proj a) ≡ proj A) (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : S.∂₁ (proj b) ≡ S.star (proj a) (proj B) B= a₁) → Derivable (ctx Γ ⊢ getTm b :> substTy (getTy B) (getTm a)) 
dTmSubst {Γ = Γ} {A} A= B B= a aₛ a₁ b bₛ b₁ =
  let lhsa=Γ = reflectOb (S.is-section₀ aₛ a₁ ∙ A=)
      lhsa=ftA = reflectOb (S.is-section₀ aₛ a₁)
      rhsa=A = reflectOb a₁
  in
  Conv (SubstTy (dTy B B=) (ConvMor (morDer a) lhsa=Γ rhsa=A)) (dTm (S.is-section₀ aₛ a₁ ∙ A=) b bₛ b₁) (SubstTyMorEq (dTy B B=) (ConvMor (morDer a) lhsa=Γ rhsa=A) (ConvMorEq (morTm=idMorTm' aₛ) lhsa=Γ rhsa=A))

dTm+ : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) {B : DCtx (suc (suc n))} (B= : ftS (proj B) ≡ proj A) (u : DMor (suc n) (suc (suc n))) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) → Derivable ((ctx Γ , getTy A) ⊢ getTm u :> getTy B)
dTm+ A= {B = B} B= u uₛ u₁ = dTm (combine A= B B=) u uₛ u₁

dTm= : {Γ : DCtx n} {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : ftS (proj A) ≡ proj Γ) {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ proj A) (a'₁ : ∂₁S (proj a') ≡ proj A') → Derivable (ctx Γ ⊢ getTm a == getTm a' :> getTy A)
dTm= rA A= {a} {a'} ra aₛ a'ₛ a₁ a'₁ = 
  let lhsa=Γ = reflectOb (S.is-section₀ aₛ a₁ ∙ A=)
      lhsa=ftA = reflectOb (S.is-section₀ aₛ a₁)
      rhsa=A = reflectOb a₁
  in
  ConvTmEq2 (getRHS= (unMor≃-mor ra)) lhsa=Γ (TyTran (ConvTy (getdTy (rhs a)) (CtxTran (getCtx= (reflect a₁)) (CtxSymm (lhsa=ftA)))) (congTyEq refl ([idMor]Ty _) (SubstTyMorEq (getdTy (rhs a)) (getdMor a) (getMor=idMor' aₛ))) (ConvTyEq (lemmathing (reflect a₁)) (CtxSymm lhsa=ftA)))

dTmSubst= : {Γ : DCtx n} {A A' : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : ftS (proj B) ≡ proj A) (B'= : ftS (proj B') ≡ proj A') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ proj A) (a'₁ : ∂₁S (proj a') ≡ proj A') {b b' : DMor n (suc n)} (rb : b ≃ b') (bₛ : S.is-section (proj b)) (b'ₛ : S.is-section (proj b')) (b₁ : ∂₁S (proj b) ≡ S.star (proj a) (proj B) B= a₁) (b'₁ : ∂₁S (proj b') ≡ S.star (proj a') (proj B') B'= a'₁) → Derivable (ctx Γ ⊢ getTm b == getTm b' :> substTy (getTy B) (getTm a))
dTmSubst= {A = A} A= {B} {B'} rB B= B'= {a} {a'} ra aₛ a'ₛ a₁ a'₁ {b} {b'} rb bₛ b'ₛ b₁ b'₁  = 
  let lhsa=Γ = reflectOb (S.is-section₀ aₛ a₁ ∙ A=)
      lhsa=ftA = reflectOb (S.is-section₀ aₛ a₁)
      rhsa=A = reflectOb a₁     
  in
    ConvEq ((SubstTy (dTy B B=) (ConvMor (morDer a) lhsa=Γ rhsa=A))) (dTm= (box (unMor≃-lhs ra ,, SubstTyMorEq2 (der (lhs a)) (der (rhs a)) (ConvTyEq (dTy+= A= rB B=) (CtxTran (CtxTy=Ctx A A=) (CtxSymm rhsa=A))) (unMor≃-mor ra))) (S.is-section₀ aₛ a₁ ∙ A=) rb bₛ b'ₛ b₁ b'₁) (SubstTyMorEq (dTy B B=) (ConvMor (morDer a) lhsa=Γ rhsa=A) (ConvMorEq (morTm=idMorTm' aₛ) lhsa=Γ rhsa=A))


dTm+= : {Γ : DCtx n} {A : DCtx (suc n)} (A= : ftS (proj A) ≡ proj Γ) {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : ftS (proj B) ≡ proj A) {u u' : DMor (suc n) (suc (suc n))} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : ∂₁S (proj u) ≡ proj B) (u'₁ : ∂₁S (proj u') ≡ proj B') → Derivable ((ctx Γ , getTy A) ⊢ getTm u == getTm u' :> getTy B)
dTm+= A= {B = B} rB B= ru uₛ u'ₛ u₁ u'₁ = dTm= rB (combine A= B B=) ru uₛ u'ₛ u₁ u'₁

{- Elimination principles for Ty and Tm -}

_×S_ : (A B : Set) → Set
A ×S B = ΣSS A (λ _ → B)

infixr 42 _×S_

//-elim-Ctx : ∀ {l} {C : (Γ : ObS n) → Set l}
           → (proj* : (Γ : DCtx n) → C (proj Γ))
           → (eq* : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → PathOver C (eqR rΓ) (proj* Γ) (proj* Γ'))
           → (Γ : ObS n) → C Γ
//-elim-Ctx proj* eq* = //-elim proj* eq*

uncurrifyTy : ∀ {l} {Γ : ObS n} (C : (A : ObS (suc n)) (A= : ftS A ≡ Γ) → Set l) → ΣS (ObS (suc n)) (λ A → ftS A ≡ Γ) → Set l
uncurrifyTy C (A , A=) = C A A=

uncurrifyTy+ : ∀ {l} {X : Set} {Γ : X → ObS n} (C : (x : X) (A : ObS (suc n)) (A= : ftS A ≡ Γ x) → Set l) → ΣS (X ×S ObS (suc n)) (λ {(x , A) → ftS A ≡ Γ x}) → Set l
uncurrifyTy+ C ((x , A) , A=) = C x A A=

//-elim-Ty : ∀ {l} {Γ : ObS n} {C : (A : ObS (suc n)) (A= : ftS A ≡ Γ) → Set l}
           → (proj* : (A : DCtx (suc n)) (A= : ftS (proj A) ≡ Γ) → C (proj A) A=)
           → (eq* : {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : ftS (proj A) ≡ Γ) (A'= : ftS (proj A') ≡ Γ) → PathOver (uncurrifyTy C) (Σ= (eqR rA)) (proj* A A=) (proj* A' A'=))
           → (A : ObS (suc n)) (A= : ftS A ≡ Γ) → C A A=
//-elim-Ty proj* eq* = //-elim proj* (λ a= → PathOver-PropPi (λ A= A'= → eq* a= A= A'=))

//-elimP-Ty : ∀ {l} {X : Set} {Γ : X → ObS n} {C : (x : X) (A : ObS (suc n)) (A= : ftS A ≡ Γ x) → Set l}
           → {x x' : X} {p : x ≡R x'}
           → {lhs : (A : ObS (suc n)) (A= : ftS A ≡ Γ x) → C x A A=}
           → {rhs : (A : ObS (suc n)) (A= : ftS A ≡ Γ x') → C x' A A=}
           → (proj* : (A : DCtx (suc n)) (A= : _) (A=' : _) → PathOver (uncurrifyTy+ C) (Σ= (apR (λ z → z , proj A) p)) (lhs (proj A) A=) (rhs (proj A) A='))
           → PathOver (λ x → (A : ObS (suc n)) (A= : ftS A ≡ Γ x) → C x A A=) p lhs rhs
//-elimP-Ty {p = reflR} proj* = PathOver-CstPi (//-elimP (λ A → PathOver-PropPi (λ A= A=' → PathOver-in (PathOver-out (proj* A A= A=')))))

uncurrifyTm : ∀ {l} {A : ObS (suc n)} (C : (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ A) → Set l) → ΣS (MorS n (suc n)) (λ u → (S.is-section u) × (S.∂₁ u ≡ A)) → Set l
uncurrifyTm C (u , (uₛ , u₁)) = C u uₛ u₁

uncurrifyTm+ : ∀ {l} {X : Set} {A : X → ObS (suc n)} (C : (x : X) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ A x) → Set l) → ΣS (X ×S MorS n (suc n)) (λ {(x , u) → (S.is-section u) × (S.∂₁ u ≡ A x)}) → Set l
uncurrifyTm+ C ((x , u) , (uₛ , u₁)) = C x u uₛ u₁

//-elim-Tm : ∀ {l} {A : ObS (suc n)} {C : (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ A) → Set l}
           → (proj* : (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : S.∂₁ (proj u) ≡ A) → C (proj u) uₛ u₁)
           → (eq* : {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : _) (u'ₛ : _) (u₁ :  S.∂₁ (proj u) ≡ A) (u'₁ : S.∂₁ (proj u') ≡ A ) → PathOver (uncurrifyTm C) (Σ= {b = uₛ , u₁} {b' = u'ₛ , u'₁} (eqR ru)) (proj* u uₛ u₁) (proj* u' u'ₛ u'₁))
           → (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ A) → C u uₛ u₁
//-elim-Tm {n = n} {C = C} proj* eq* = //-elim proj* (λ ru → PathOver-PropPi (λ uₛ uₛ' → PathOver-PropPi (λ u₁ u₁' → PathOver-in (PathOver-= (lemma (eqR ru)) (PathOver-out (eq* ru uₛ uₛ' u₁ u₁'))))))  where

  lemma : {u u' : MorS n (suc n)} (p : u ≡R u') {uₛ : _} {u'ₛ : _} {u₁ : _} {u'₁ : _}
        → apR (uncurrifyTm C) (Σ= {b = uₛ , u₁} {b' = u'ₛ , u'₁} p) ≡R apR (uncurrify (λ a z → C (fst a) (snd a) z)) (Σ= {b = u₁} {b' = u'₁} (Σ= {b = uₛ} {b' = u'ₛ} p))
  lemma reflR = reflR


//-elimP-Tm : ∀ {l} {X : Set} {A : X → ObS (suc n)} {C : (x : X) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ A x) → Set l}
           → {x x' : X} {p : x ≡R x'}
           → {lhs : (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ A x) → C x u uₛ u₁}
           → {rhs : (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ A x') → C x' u uₛ u₁}
           → (proj* : (u : DMor n (suc n)) (uₛ : _) (u₁ : _) (u₁' : _) → PathOver (uncurrifyTm+ C) (Σ= {b = uₛ , u₁} {b' = uₛ , u₁'} (apR (λ z → z , proj u) p)) (lhs (proj u) uₛ u₁) (rhs (proj u) uₛ u₁'))
           → PathOver (λ x → (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ A x) → C x u uₛ u₁) p lhs rhs
//-elimP-Tm {p = reflR} proj* = PathOver-CstPi (//-elimP (λ u → PathOver-CstPropPi (λ uₛ → PathOver-PropPi (λ u₁ u₁' → PathOver-in (PathOver-out (proj* u uₛ u₁ u₁'))))))

proj= : ∀ {l l'} {A : Set l} {B : Set l'} {a a' : A} {p : a ≡R a'} {u v : B}
      → u ≡ v → PathOver (λ _ → B) p u v
proj= {p = reflR} refl = reflo


{- UU -}

UUStrS-// : (i : ℕ) → DCtx n → DCtx (suc n)
UUStrS-// i Γ = ((ctx Γ , uu i) , (der Γ , UU))

UUStrS-eq : {i : ℕ} {Γ Γ' : DCtx n} → Γ ≃ Γ' → proj {R = ObEquiv} (UUStrS-// i Γ) ≡ proj (UUStrS-// i Γ')
UUStrS-eq dΓ= = eq (box (unOb≃ dΓ= ,, UUCong))

UUStrS : (i : ℕ) → ObS n → ObS (suc n)
UUStrS i = //-elim-Ctx (λ Γ → proj (UUStrS-// i Γ)) (λ rΓ → proj= (UUStrS-eq rΓ))

UUStr=S : (i : ℕ) (Γ : ObS n) → ftS (UUStrS i Γ) ≡ Γ
UUStr=S i = //-elimP (λ Γ → refl)

UUStrNatS : {i : ℕ} (g : MorS n m) (Γ : ObS m) (g₁ : ∂₁S g ≡ Γ) → S.star g (UUStrS i Γ) (UUStr=S i Γ) g₁ ≡ UUStrS i (∂₀S g)
UUStrNatS = //-elimP (λ g → //-elimP (λ Γ g₁ → refl))

UUStrSynCCat : CCatwithUU synCCat
CCatwithUU.UUStr UUStrSynCCat = UUStrS
CCatwithUU.UUStr= UUStrSynCCat = UUStr=S _ _
CCatwithUU.UUStrNat UUStrSynCCat = {!explicitify UUStrSynCCat f!}  where   --{g = g} refl {Γ = Γ} {g₁ = g₁} = UUStrNatS g Γ g₁
  f : {!!}
  f = {!!}


{- El -}

ElStrS-// : (i : ℕ) (Γ : DCtx n) (v : DMor n (suc n)) (vₛ : S.is-section (proj v)) (v₁ : ∂₁S (proj v) ≡ UUStrS i (proj Γ)) → DCtx (suc n)
ElStrS-// i Γ v vₛ v₁ = ((ctx Γ , el i (getTm v)) , (der Γ , El (dTm refl v vₛ v₁)))

ElStrS-eq : {i : ℕ} {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {v v' : DMor n (suc n)} (rv : v ≃ v') (vₛ : _) (v'ₛ : _) (v₁ : _) (v'₁ : _) → proj {R = ObEquiv} (ElStrS-// i Γ v vₛ v₁) ≡ proj {R = ObEquiv} (ElStrS-// i Γ' v' v'ₛ v'₁)
ElStrS-eq rΓ rv vₛ v'ₛ v₁ v'₁ =
  eq (box (unOb≃ rΓ ,, ElCong (dTm= (box (unOb≃ rΓ ,, TyRefl UU)) refl rv vₛ v'ₛ v₁ v'₁)))

ElStrS : (i : ℕ) (Γ : ObS n) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ UUStrS i Γ) → ObS (suc n)
ElStrS i = //-elim-Ctx (λ Γ → //-elim-Tm (λ v vₛ v₁ → proj (ElStrS-// i Γ v vₛ v₁))
                                         (λ ru uₛ u'ₛ u₁ u'₁ → proj= (ElStrS-eq (ref Γ) ru uₛ u'ₛ u₁ u'₁)))
                       (λ rΓ → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (ElStrS-eq rΓ (ref u) uₛ uₛ u₁ u₁')))

ElStr=S : (i : ℕ) (Γ : ObS n) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ UUStrS i Γ) → ftS (ElStrS i Γ u uₛ u₁) ≡ Γ
ElStr=S i = //-elimP (λ Γ → //-elimP (λ u uₛ u₁ → refl))

ElStrNatS : {i : ℕ} (g : MorS n m) (Γ : ObS m) (v : MorS m (suc m)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ UUStrS i Γ) (g₁ : ∂₁S g ≡ Γ)
  → S.star g (ElStrS i Γ v vₛ v₁) (ElStr=S i Γ v vₛ v₁) g₁ ≡ ElStrS i (∂₀S g) (S.starTm g v (S.is-section₀ vₛ v₁ ∙ UUStr=S i Γ) g₁) S.ssₛ (S.starTm₁ g (UUStr=S i Γ) v vₛ v₁ g₁ ∙ UUStrNatS g Γ g₁)
ElStrNatS = //-elimP (λ g → //-elimP (λ Γ → //-elimP (λ v vₛ v₁ g₁ → refl)))

ElStrSynCCat : CCatwithEl synCCat UUStrSynCCat
CCatwithEl.ElStr ElStrSynCCat i Γ v vₛ v₁ = ElStrS i Γ v vₛ v₁
CCatwithEl.ElStr= ElStrSynCCat = ElStr=S _ _ _ _ _
CCatwithEl.ElStrNat ElStrSynCCat {g = g} refl {g₁ = g₁} = ElStrNatS g _ _ _ _ g₁


{- Pi -}

PiStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : ftS (proj B) ≡ proj A) → DCtx (suc n)
PiStrS-// Γ A A= B B= = (ctx Γ , pi (getTy A) (getTy B)) , (der Γ , Pi (dTy A A=) (dTy+ A= B B=))

PiStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : _) (A'= : _) {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : _) (B'= : _)
          → proj {R = ObEquiv} (PiStrS-// Γ A A= B B=) ≡ proj (PiStrS-// Γ' A' A'= B' B'=)
PiStrS-eq rΓ {A = A} rA A= A'= {B = B} rB B= B'= = eq (box (unOb≃ rΓ ,, PiCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=)))

PiStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) → ObS (suc n)
PiStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → proj (PiStrS-// Γ A A= B B=))
                                                            (λ rB B= B=' → proj= (PiStrS-eq (ref Γ) (ref A) A= A= rB B= B=')))
                                       (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → proj= (PiStrS-eq (ref Γ) rA A= A'= (ref B) B= B='))))
                     (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → proj= (PiStrS-eq rΓ (ref A) A= A=' (ref B) B= B='))))

PiStr=S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) → ftS (PiStrS Γ A A= B B=) ≡ Γ
PiStr=S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → refl)))

PiStrNatS : (g : MorS n m) (Γ : ObS m) (A : ObS (suc m)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc m))) (B= : ftS B ≡ A) (g₁ : ∂₁S g ≡ Γ)
          → S.star g (PiStrS Γ A A= B B=) (PiStr=S Γ A A= B B=) g₁
          ≡ PiStrS (∂₀S g) (S.star g A A= g₁) (ft-starS g A (g₁ ∙ ! A=)) (S.star+ g B B= A= g₁) (ft-starS (qqS g A (g₁ ∙ ! A=)) B (qq₁S g A (g₁ ∙ ! A=) ∙ ! B=) ∙ qq₀S g A (g₁ ∙ ! A=))
PiStrNatS = //-elimP (λ g → //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= g₁ → refl))))

PiStrSynCCat : CCatwithPi synCCat
CCatwithPi.PiStr PiStrSynCCat = PiStrS 
CCatwithPi.PiStr= PiStrSynCCat = PiStr=S _ _ _ _ _
CCatwithPi.PiStrNat PiStrSynCCat {g = g} refl {g₁ = g₁} = PiStrNatS g _ _ _ _ _ g₁


{- Sig -}

SigStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : ftS (proj B) ≡ proj A) → DCtx (suc n)
SigStrS-// Γ A A= B B= = (ctx Γ , sig (getTy A) (getTy B)) , (der Γ , Sig (dTy A A=) (dTy+ A= B B=))

SigStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : _) (A'= : _) {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : _) (B'= : _)
          → proj {R = ObEquiv} (SigStrS-// Γ A A= B B=) ≡ proj (SigStrS-// Γ' A' A'= B' B'=)
SigStrS-eq rΓ {A = A} rA A= A'= rB B= B'= = eq (box (unOb≃ rΓ ,, SigCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=)))

SigStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) → ObS (suc n)
SigStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → proj (SigStrS-// Γ A A= B B=))
                                                             (λ rB B= B=' → proj= (SigStrS-eq (ref Γ) (ref A) A= A= rB B= B=')))
                                        (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → proj= (SigStrS-eq (ref Γ) rA A= A'= (ref B) B= B='))))
                      (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → proj= (SigStrS-eq rΓ (ref A) A= A=' (ref B) B= B='))))

SigStr=S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) → ftS (SigStrS Γ A A= B B=) ≡ Γ
SigStr=S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → refl)))

SigStrNatS : (g : MorS n m) (Γ : ObS m) (A : ObS (suc m)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc m))) (B= : ftS B ≡ A) (g₁ : ∂₁S g ≡ Γ)
           → S.star g (SigStrS Γ A A= B B=) (SigStr=S Γ A A= B B=) g₁
           ≡ SigStrS (∂₀S g) (S.star g A A= g₁) (ft-starS g A (g₁ ∙ ! A=)) (S.star+ g B B= A= g₁) (ft-starS (qqS g A (g₁ ∙ ! A=)) B (qq₁S g A (g₁ ∙ ! A=) ∙ ! B=) ∙ qq₀S g A (g₁ ∙ ! A=))
SigStrNatS = //-elimP (λ g → //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= g₁ → refl))))

SigStrSynCCat : CCatwithSig synCCat
CCatwithSig.SigStr SigStrSynCCat = SigStrS 
CCatwithSig.SigStr= SigStrSynCCat = SigStr=S _ _ _ _ _
CCatwithSig.SigStrNat SigStrSynCCat {g = g} refl {g₁ = g₁} = SigStrNatS g _ _ _ _ _ g₁

 
{- Nat -}

NatStrS-// : DCtx n → DCtx (suc n)
NatStrS-// Γ = ((ctx Γ , nat) , (der Γ , Nat))

NatStrS-eq : {Γ Γ' : DCtx n} → Γ ≃ Γ' → proj {R = ObEquiv} (NatStrS-// Γ) ≡ proj (NatStrS-// Γ')
NatStrS-eq dΓ= = eq (box (unOb≃ dΓ= ,, NatCong))

NatStrS : ObS n → ObS (suc n)
NatStrS = //-elim-Ctx (λ Γ → proj (NatStrS-// Γ)) (λ rΓ → proj= (NatStrS-eq rΓ))

NatStr=S : (Γ : ObS n) → ftS (NatStrS Γ) ≡ Γ
NatStr=S = //-elimP (λ Γ → refl)

NatStrNatS : (g : MorS n m) (Γ : ObS m) (g₁ : ∂₁S g ≡ Γ) → S.star g (NatStrS Γ) (NatStr=S Γ) g₁ ≡ NatStrS (∂₀S g)
NatStrNatS = //-elimP (λ g → //-elimP (λ Γ g₁ → refl))

NatStrSynCCat : CCatwithNat synCCat
CCatwithNat.NatStr NatStrSynCCat = NatStrS
CCatwithNat.NatStr= NatStrSynCCat = NatStr=S _
CCatwithNat.NatStrNat NatStrSynCCat {g = g} refl {g₁ = refl} = NatStrNatS g _ refl

module SNat = CCatwithNat NatStrSynCCat

{- Id -}

IdStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : ∂₁S (proj b) ≡ proj A) → DCtx (suc n)
IdStrS-// Γ A A= a aₛ a₁ b bₛ b₁ = (ctx Γ , id (getTy A) (getTm a) (getTm b)) , (der Γ , Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= b bₛ b₁))

IdStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : _) (A'= : _) {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : _) (a'ₛ : _) (a₁ : _) (a'₁ : _) {b b' : DMor n (suc n)} (rb : b ≃ b') (bₛ : _) (b'ₛ : _) (b₁ : _) (b'₁ : _) → proj {R = ObEquiv} (IdStrS-// Γ A A= a aₛ a₁ b bₛ b₁) ≡ proj (IdStrS-// Γ' A' A'= a' a'ₛ a'₁ b' b'ₛ b'₁)
IdStrS-eq rΓ rA A= A'= ra aₛ a'ₛ a₁ a'₁ rb bₛ b'ₛ b₁ b'₁ = eq (box (unOb≃ rΓ ,, IdCong (dTy= rA A=) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁) (dTm= rA A= rb bₛ b'ₛ b₁ b'₁)))

IdStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ A) → ObS (suc n)
IdStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Tm (λ a aₛ a₁ → //-elim-Tm (λ b bₛ b₁ → proj (IdStrS-// Γ A A= a aₛ a₁ b bₛ b₁))
                                                                                    (λ rb bₛ b'ₛ b₁ b'₁ → proj= (IdStrS-eq (ref Γ) (ref A) A= A= (ref a) aₛ aₛ a₁ a₁ rb bₛ b'ₛ b₁ b'₁)))
                                                            (λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (IdStrS-eq (ref Γ) (ref A) A= A= ra aₛ a'ₛ a₁ a'₁ (ref b) bₛ bₛ b₁ b₁'))))
                                       (λ rA A= A'= → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (IdStrS-eq (ref Γ) rA A= A'= (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁')))))
                     (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (IdStrS-eq rΓ (ref A) A= A=' (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁')))))

IdStr=S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ A) → ftS (IdStrS Γ A A= a aₛ a₁ b bₛ b₁) ≡ Γ
IdStr=S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → refl))))

IdStrSynCCat : CCatwithId synCCat
CCatwithId.IdStr IdStrSynCCat = IdStrS
CCatwithId.IdStr= IdStrSynCCat = IdStr=S _ _ _ _ _ _ _ _ _
CCatwithId.IdStrNat IdStrSynCCat p = {!!}

{-- Term formers --}

dmorTm : (Γ : DCtx n) (A : TyExpr n) (dA : Derivable (ctx Γ ⊢ A)) (u : TmExpr n) (du : Derivable (ctx Γ ⊢ u :> A)) → DMor n (suc n)
dmorTm Γ A dA u du = dmor Γ ((ctx Γ , A) , (der Γ , dA)) (idMor _ , u) (idMor+ (der Γ) du)

dmorTm= : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ')
         → {A A' : TyExpr n} (dA : _) (dA' : _) (dA= : Derivable (ctx Γ ⊢ A == A'))
         → {u u' : TmExpr n} (du : _) (du' : _) (du= : Derivable (ctx Γ ⊢ u == u' :> A))
         → proj {R = MorEquiv} (dmorTm Γ A dA u du) ≡ proj (dmorTm Γ' A' dA' u' du')
dmorTm= {Γ = Γ} rΓ _ _ dA= _ _ du= = eq (box (unOb≃ rΓ) (unOb≃ rΓ ,, dA=) (idMor+= (der Γ) du=))

dmorTmₛ : {Γ : DCtx n} {A : TyExpr n} (dA : Derivable (ctx Γ ⊢ A)) {u : TmExpr n} (du : Derivable (ctx Γ ⊢ u :> A)) → S.is-section (proj {R = MorEquiv} (dmorTm Γ A dA u du))
dmorTmₛ {Γ = Γ} dA du = S.is-section→ (eq (box (CtxRefl (der Γ)) (CtxRefl (der Γ)) (congMorEq refl refl (! (weakenMorInsert _ _ _ ∙ [idMor]Mor (idMor _))) refl (MorRefl (idMorDerivable (der Γ))))))


{- uu -}

uuStrS-// : (i : ℕ) (Γ : DCtx n) → DMor n (suc n)
uuStrS-// i Γ = dmorTm Γ (uu (suc i)) UU (uu i) UUUU

uuStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → proj {R = MorEquiv} (uuStrS-// i Γ) ≡ proj (uuStrS-// i Γ')
uuStrS-eq i rΓ = dmorTm= rΓ UU UU UUCong UUUU UUUU UUUUCong

uuStrS : (i : ℕ) (Γ : ObS n) → MorS n (suc n)
uuStrS i = //-elim-Ctx (λ Γ → proj (uuStrS-// i Γ)) (λ rΓ → proj= (uuStrS-eq i rΓ))

uuStrₛS : (i : ℕ) (Γ : ObS n) → S.is-section (uuStrS i Γ)
uuStrₛS i = //-elimP (λ Γ → dmorTmₛ UU UUUU)

uuStr₁S : (i : ℕ) (Γ : ObS n) → ∂₁S (uuStrS i Γ) ≡ UUStrS (suc i) Γ
uuStr₁S i = //-elimP (λ Γ → refl)

uuStrSynCCat : CCatwithuu synCCat UUStrSynCCat
CCatwithuu.uuStr uuStrSynCCat = uuStrS
CCatwithuu.uuStrₛ uuStrSynCCat {Γ = Γ} = uuStrₛS _ Γ
CCatwithuu.uuStr₁ uuStrSynCCat {Γ = Γ} = uuStr₁S _ Γ
CCatwithuu.uuStrNat uuStrSynCCat = {!explicitify uuStrSynCCat f!} where
  f : _
  f = {!!}

{- pi -}

piStrS-// : (i : ℕ) (Γ : DCtx n) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (proj Γ)) (b : DMor (suc n) (suc (suc n))) (bₛ : S.is-section (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj Γ) (proj a) aₛ a₁)) → DMor n (suc n)
piStrS-// i Γ a aₛ a₁ b bₛ b₁ = dmorTm Γ (uu i) UU (pi i (getTm a) (getTm b)) (PiUU (dTm refl a aₛ a₁) (dTm refl b bₛ b₁))

piStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : _) (a'ₛ : _) (a₁ : _) (a'₁ : _) {b b' : DMor (suc n) (suc (suc n))} (rb : b ≃ b') (bₛ : _) (b'ₛ : _) (b₁ : _) (b'₁ : _)
          → proj {R = MorEquiv} (piStrS-// i Γ a aₛ a₁ b bₛ b₁) ≡ proj (piStrS-// i Γ' a' a'ₛ a'₁ b' b'ₛ b'₁)
piStrS-eq i rΓ ra aₛ a'ₛ a₁ a'₁ rb bₛ b'ₛ b₁ b'₁ =
  dmorTm= rΓ UU UU UUCong (PiUU (dTm refl _ aₛ a₁) (dTm refl _ bₛ b₁)) (PiUU (dTm refl _ a'ₛ a'₁) (dTm refl _ b'ₛ b'₁))
    (PiUUCong (dTm refl _ aₛ a₁)
              (dTm= (box (unOb≃ rΓ ,, UUCong)) refl ra aₛ a'ₛ a₁ a'₁)
              (dTm= (box ((unOb≃ rΓ ,, ElCong (dTm= (box (unOb≃ rΓ ,, UUCong)) refl ra aₛ a'ₛ a₁ a'₁)) ,, UUCong)) refl rb bₛ b'ₛ b₁ b'₁))


piStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁)) → MorS n (suc n)
piStrS i = //-elim-Ctx (λ Γ → //-elim-Tm (λ a aₛ a₁ → //-elim-Tm (λ b bₛ b₁ → proj (piStrS-// i Γ a aₛ a₁ b bₛ b₁))
                                                                 (λ rb bₛ b'ₛ b₁ b'₁ → proj= (piStrS-eq i (ref Γ) (ref a) aₛ aₛ a₁ a₁ rb bₛ b'ₛ b₁ b'₁)))
                                         (λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (piStrS-eq i (ref Γ) ra aₛ a'ₛ a₁ a'₁ (ref b) bₛ bₛ b₁ b₁'))))
                       (λ rΓ → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (piStrS-eq i rΓ (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁'))))

piStrₛS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁)) → S.is-section (piStrS i Γ a aₛ a₁ b bₛ b₁)
piStrₛS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → dmorTmₛ UU (PiUU (dTm refl a aₛ a₁) (dTm refl b bₛ b₁)))))

piStr₁S : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁)) → ∂₁S (piStrS i Γ a aₛ a₁ b bₛ b₁) ≡ UUStrS i Γ
piStr₁S i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → refl)))

piStrSynCCat : CCatwithpi synCCat UUStrSynCCat ElStrSynCCat

-- piStrSNat : {i : ℕ} (g : MorS n m) (Γ : ObS m) (a : MorS m (suc m)) (aₛ : _) (a₁ : _) (b : MorS (suc m) (suc (suc m))) (bₛ : _) (b₁ : _) (g₁ : ∂₁S g ≡ Γ)
--             → S.starTm g (piStrS i Γ a aₛ a₁ b bₛ b₁) (S.is-section₀ (piStrₛS i Γ a aₛ a₁ b bₛ b₁) (piStr₁S i Γ a aₛ a₁ b bₛ b₁) ∙ UUStr=S i Γ) g₁
--             ≡ piStrS i (∂₀S g) (S.starTm g a a₀ g₁) {!starTmₛ!} (S.starTm₁ g (UUStr=S i Γ) a aₛ a₁ g₁ ∙ UUStrNatS g Γ g₁)
--                                (S.starTm+ g (ElStr=S i Γ a aₛ a₁) b b₀ g₁) {!starTmₛ!} (S.starTm+₁ g (UUStr=S i (ElStrS i Γ a aₛ a₁)) (ElStr=S i Γ a aₛ a₁) b bₛ b₁ g₁ ∙ UUStrNatS {!!} {!!} {!!})
-- piStrSNat = {!λ i → //-elimP (λ g → //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ g₁ → refl))))!}

CCatwithpi.piStr piStrSynCCat = piStrS
CCatwithpi.piStrₛ piStrSynCCat {Γ = Γ} {a = a} {b = b} = piStrₛS _ Γ a _ _ b _ _
CCatwithpi.piStr₁ piStrSynCCat {Γ = Γ} {a = a} {b = b} = piStr₁S _ Γ a _ _ b _ _
CCatwithpi.piStrNat piStrSynCCat = {!explicitify f!} where --piStrSNat g Γ a aₛ a₁ b bₛ b₁ g₁
  f : {!!}
  f = {!!}


{- lam -}

lamStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : ftS (proj B) ≡ proj A) (u : DMor (suc n) (suc (suc n))) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) → DMor n (suc n)
lamStrS-// Γ A A= B B= u uₛ u₁ = dmorTm Γ (pi (getTy A) (getTy B)) (Pi (dTy A A=) (dTy+ A= B B=)) (lam (getTy A) (getTy B) (getTm u)) (Lam (dTy A A=) (dTy+ A= B B=) (dTm+ A= B= u uₛ u₁))

lamStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : _) (A'= : _) {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : _) (B'= : _) {u u' : DMor (suc n) (suc (suc n))} (ru : u ≃ u') (uₛ : _) (u'ₛ : _) (u₁ : _) (u'₁ : _) → proj {R = MorEquiv} (lamStrS-// Γ A A= B B= u uₛ u₁) ≡ proj (lamStrS-// Γ' A' A'= B' B'= u' u'ₛ u'₁)
lamStrS-eq rΓ {A} {A'} rA A= A'= {B} {B'} rB B= B'= ru uₛ u'ₛ u₁ u'₁ = dmorTm= rΓ (Pi (dTy A A=) (dTy+ A= B B=)) (Pi (dTy A' A'=) (dTy+ A'= B' B'=)) (PiCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=)) (Lam (dTy A A=) (dTy+ A= B B=) (dTm+ A= B= _ uₛ u₁)) (Lam (dTy A' A'=) (dTy+ A'= B' B'=) (dTm+ A'= B'= _ u'ₛ u'₁)) (LamCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=) (dTm+= A= rB B= ru uₛ u'ₛ u₁ u'₁))

lamStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (u : MorS (suc n) (suc (suc n))) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ B) → MorS n (suc n)
lamStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → //-elim-Tm (λ u uₛ u₁ → proj (lamStrS-// Γ A A= B B= u uₛ u₁))
                                                                                  (λ ru uₛ u'ₛ u₁ u'₁ → proj= (lamStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= ru uₛ u'ₛ u₁ u'₁)))
                                                             (λ rB B= B'= → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (lamStrS-eq (ref Γ) (ref A) A= A= rB B= B'= (ref u) uₛ uₛ u₁ u₁'))))
                                        (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (lamStrS-eq (ref Γ) rA A= A'= (ref B) B= B=' (ref u) uₛ uₛ u₁ u₁')))))
                     (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (lamStrS-eq rΓ (ref A) A= A=' (ref B) B= B=' (ref u) uₛ uₛ u₁ u₁')))))

lamStrₛS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (u : MorS (suc n) (suc (suc n))) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ B) → S.is-section (lamStrS Γ A A= B B= u uₛ u₁)
lamStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → dmorTmₛ (Pi (dTy A A=) (dTy+ A= B B=)) (Lam (dTy A A=) (dTy+ A= B B=) (dTm+ A= B= u uₛ u₁))))))

lamStr₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (u : MorS (suc n) (suc (suc n))) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ B) → ∂₁S (lamStrS Γ A A= B B= u uₛ u₁) ≡ PiStrS Γ A A= B B=
lamStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → refl))))


lamStrSynCCat : CCatwithlam synCCat PiStrSynCCat
CCatwithlam.lamStr lamStrSynCCat = lamStrS
CCatwithlam.lamStrₛ lamStrSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = lamStrₛS Γ A _ B _ u _ _
CCatwithlam.lamStr₁ lamStrSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = lamStr₁S Γ A _ B _ u _ _
CCatwithlam.lamStrNat lamStrSynCCat = {!!}


{- app -}

appStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : ftS (proj B) ≡ proj A) (f : DMor n (suc n)) (fₛ : S.is-section (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj Γ) (proj A) A= (proj B) B=) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) → DMor n (suc n)
appStrS-// Γ A A= B B= f fₛ f₁ a aₛ a₁ = dmorTm Γ (substTy (getTy B) (getTm a)) (SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (dTm A= a aₛ a₁))) (app (getTy A) (getTy B) (getTm f) (getTm a)) (App (dTy A A=) (dTy+ A= B B=) (dTm refl f fₛ f₁) (dTm A= a aₛ a₁))
 
appStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : ftS (proj A) ≡ proj Γ) (A'= : ftS (proj A') ≡ proj Γ') {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : ftS (proj B) ≡ proj A) (B'= : ftS (proj B') ≡ proj A') {f f' : DMor n (suc n)} (rf : f ≃ f') (fₛ : S.is-section (proj f)) (f'ₛ : S.is-section (proj f')) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj Γ) (proj A) A= (proj B) B=) (f₁' : ∂₁S (proj f') ≡ PiStrS (proj Γ') (proj A') A'= (proj B') B'=) {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ proj A) (a'₁ : ∂₁S (proj a') ≡ proj A')
          → proj {R = MorEquiv} (appStrS-// Γ A A= B B= f fₛ f₁ a aₛ a₁) ≡ proj (appStrS-// Γ' A' A'= B' B'= f' f'ₛ f₁' a' a'ₛ a'₁)
appStrS-eq {Γ = Γ} {Γ'} rΓ {A} {A'} rA A= A'= {B} {B'} rB B= B'= {f} {f'} rf fₛ f'ₛ f₁ f'₁ {a} {a'} ra aₛ a'ₛ a₁ a'₁ =
  dmorTm= rΓ (SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (dTm A= a aₛ a₁))) (SubstTy (dTy+ A'= B' B'=) (idMor+ (der Γ') (dTm A'= a' a'ₛ a'₁)))
          (SubstTyMorEq2 (der Γ) (der Γ , dTy A A=) (dTy+= A= rB B=) (idMor+= (der Γ) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁))) (App (dTy A A=) (dTy+ A= B B=) (dTm refl f fₛ f₁) (dTm A= a aₛ a₁)) (App (dTy A' A'=) (dTy+ A'= B' B'=) (dTm refl f' f'ₛ f'₁) (dTm A'= a' a'ₛ a'₁))
          (AppCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=) (dTm= (box (unOb≃ rΓ ,, PiCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=))) refl rf fₛ f'ₛ f₁ f'₁) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁))

appStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (f : MorS n (suc n)) (fₛ : S.is-section f) (f₁ : ∂₁S f ≡ PiStrS Γ A A= B B=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
        → MorS n (suc n)
appStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → //-elim-Tm (λ f fₛ f₁ → //-elim-Tm (λ a aₛ a₁ → proj (appStrS-// Γ A A= B B= f fₛ f₁ a aₛ a₁))
                                                                                                          (λ ra aₛ a'ₛ a₁ a'₁ → proj= (appStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= (ref f) fₛ fₛ f₁ f₁ ra aₛ a'ₛ a₁ a'₁)))
                                                                                  (λ rf fₛ f'ₛ f₁ f'₁ → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (appStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= rf fₛ f'ₛ f₁ f'₁ (ref a) aₛ aₛ a₁ a₁'))))
                                                             (λ rB B= B'= → //-elimP-Tm (λ f fₛ f₁ f₁' → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (appStrS-eq (ref Γ) (ref A) A= A= rB B= B'= (ref f) fₛ fₛ f₁ f₁' (ref a) aₛ aₛ a₁ a₁')))))
                                        (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ f fₛ f₁ f₁' → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (appStrS-eq (ref Γ) rA A= A'= (ref B) B= B=' (ref f) fₛ fₛ f₁ f₁' (ref a) aₛ aₛ a₁ a₁'))))))
                      (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ f fₛ f₁ f₁' → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (appStrS-eq rΓ (ref A) A= A=' (ref B) B= B=' (ref f) fₛ fₛ f₁ f₁' (ref a) aₛ aₛ a₁ a₁'))))))

appStrₛS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (f : MorS n (suc n)) (fₛ : S.is-section f) (f₁ : ∂₁S f ≡ PiStrS Γ A A= B B=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
         → S.is-section (appStrS Γ A A= B B= f fₛ f₁ a aₛ a₁)
appStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ f fₛ f₁ → //-elimP (λ a aₛ a₁ → dmorTmₛ (SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (dTm A= a aₛ a₁))) (App (dTy A A=) (dTy+ A= B B=) (dTm refl f fₛ f₁) (dTm A= a aₛ a₁)))))))

appStr₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (f : MorS n (suc n)) (fₛ : S.is-section f) (f₁ : ∂₁S f ≡ PiStrS Γ A A= B B=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
         → ∂₁S (appStrS Γ A A= B B= f fₛ f₁ a aₛ a₁) ≡ S.star a B B= a₁
appStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ f fₛ f₁ → //-elimP (λ a aₛ a₁ → eq (box (CtxSymm ((reflectOb (S.is-section₀ aₛ a₁ ∙ A=)) ,, SubstTyMorEq (dTy B B=) (ConvMor (morDer a) (CtxRefl (der (lhs a))) (reflectOb a₁)) (ConvMorEq (morTm=idMorTm' aₛ) (CtxRefl (der (lhs a))) (reflectOb a₁))))))))))

-- appStrSNat : (g : MorS n m) (Γ : ObS m) (A : ObS (suc m)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc m))) (B= : ftS B ≡ A) (f : MorS m (suc m)) (fₛ : _) (f₁ : _) (a : MorS m (suc m)) (aₛ : _) (a₁ : _) (g₁ : _)
--              (let a₀ = S.is-section₀ aₛ a₁ ∙ A=) (let f₀ = S.is-section₀ fₛ f₁ ∙ {!S.PiStr=!})
--              → S.starTm g (appStrS Γ A A= B B= f fₛ f₁ a aₛ a₁) {!appStr₀!} g₁
--                 ≡ appStrS (∂₀S g) (S.star g A A= g₁)
--                                   (S.ft-star)
--                                   (S.star+ g B B= A= g₁)
--                                   (S.ft-star ∙ S.qq₀)
--                                   (S.starTm g f f₀ g₁) S.ssₛ (S.starTm₁ g {!S.PiStr=!} f fₛ f₁ g₁ ∙ {!!})
--                                   (S.starTm g a a₀ g₁) S.ssₛ (S.starTm₁ g A= a aₛ a₁ g₁)
-- appStrSNat = //-elimP (λ g → //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ f fₛ f₁ → //-elimP (λ a aₛ a₁ g₁ → {!refl!}))))))

appStrSynCCat : CCatwithapp synCCat PiStrSynCCat
CCatwithapp.appStr appStrSynCCat = appStrS
CCatwithapp.appStrₛ appStrSynCCat {Γ = Γ} {A = A} {B = B} {f = f} {a = a} = appStrₛS Γ A _ B _ f _ _ a _ _
CCatwithapp.appStr₁ appStrSynCCat {Γ = Γ} {A = A} {B = B} {f = f} {a = a} = appStr₁S Γ A _ B _ f _ _ a _ _
CCatwithapp.appStrNat appStrSynCCat {g = g} refl = {!appStrSNat g _ _ _ _ _ _ _ _ _ _ _ _!}

{- sig -}


sigStrS-// : (i : ℕ) (Γ : DCtx n) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (proj Γ)) (b : DMor (suc n) (suc (suc n))) (bₛ : S.is-section (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj Γ) (proj a) aₛ a₁)) → DMor n (suc n)
sigStrS-// i Γ a aₛ a₁ b bₛ b₁ = dmorTm Γ (uu i) UU (sig i (getTm a) (getTm b)) (SigUU (dTm refl a aₛ a₁) (dTm refl b bₛ b₁))

sigStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : _) (a'ₛ : _) (a₁ : _) (a'₁ : _) {b b' : DMor (suc n) (suc (suc n))} (rb : b ≃ b') (bₛ : _) (b'ₛ : _) (b₁ : _) (b'₁ : _)
          → proj {R = MorEquiv} (sigStrS-// i Γ a aₛ a₁ b bₛ b₁) ≡ proj (sigStrS-// i Γ' a' a'ₛ a'₁ b' b'ₛ b'₁)
sigStrS-eq i rΓ ra aₛ a'ₛ a₁ a'₁ rb bₛ b'ₛ b₁ b'₁ =
  dmorTm= rΓ UU UU UUCong (SigUU (dTm refl _ aₛ a₁) (dTm refl _ bₛ b₁)) (SigUU (dTm refl _ a'ₛ a'₁) (dTm refl _ b'ₛ b'₁))
    (SigUUCong (dTm refl _ aₛ a₁)
              (dTm= (box (unOb≃ rΓ ,, UUCong)) refl ra aₛ a'ₛ a₁ a'₁)
              (dTm= (box ((unOb≃ rΓ ,, ElCong (dTm= (box (unOb≃ rΓ ,, UUCong)) refl ra aₛ a'ₛ a₁ a'₁)) ,, UUCong)) refl rb bₛ b'ₛ b₁ b'₁))


sigStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁)) → MorS n (suc n)
sigStrS i = //-elim-Ctx (λ Γ → //-elim-Tm (λ a aₛ a₁ → //-elim-Tm (λ b bₛ b₁ → proj (sigStrS-// i Γ a aₛ a₁ b bₛ b₁))
                                                                 (λ rb bₛ b'ₛ b₁ b'₁ → proj= (sigStrS-eq i (ref Γ) (ref a) aₛ aₛ a₁ a₁ rb bₛ b'ₛ b₁ b'₁)))
                                         (λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (sigStrS-eq i (ref Γ) ra aₛ a'ₛ a₁ a'₁ (ref b) bₛ bₛ b₁ b₁'))))
                       (λ rΓ → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (sigStrS-eq i rΓ (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁'))))

sigStrₛS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁)) → S.is-section (sigStrS i Γ a aₛ a₁ b bₛ b₁)
sigStrₛS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → dmorTmₛ UU (SigUU (dTm refl a aₛ a₁) (dTm refl b bₛ b₁)))))

sigStr₁S : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁)) → ∂₁S (sigStrS i Γ a aₛ a₁ b bₛ b₁) ≡ UUStrS i Γ
sigStr₁S i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → refl)))

sigStrSynCCat : CCatwithsig synCCat UUStrSynCCat ElStrSynCCat

-- sigStrSNat : {i : ℕ} (g : MorS n m) (Γ : ObS m) (a : MorS m (suc m)) (aₛ : _) (a₁ : _) (b : MorS (suc m) (suc (suc m))) (bₛ : _) (b₁ : _) (g₁ : ∂₁S g ≡ Γ)
--             → S.starTm g (sigStrS i Γ a aₛ a₁ b bₛ b₁) (S.is-section₀ (sigStrₛS i Γ a aₛ a₁ b bₛ b₁) (sigStr₁S i Γ a aₛ a₁ b bₛ b₁) ∙ UUStr=S i Γ) g₁
--             ≡ sigStrS i (∂₀S g) (S.starTm g a a₀ g₁) {!starTmₛ!} (S.starTm₁ g (UUStr=S i Γ) a aₛ a₁ g₁ ∙ UUStrNatS g Γ g₁)
--                                (S.starTm+ g (ElStr=S i Γ a aₛ a₁) b b₀ g₁) {!starTmₛ!} (S.starTm+₁ g (UUStr=S i (ElStrS i Γ a aₛ a₁)) (ElStr=S i Γ a aₛ a₁) b bₛ b₁ g₁ ∙ UUStrNatS {!!} {!!} {!!})
-- sigStrSNat = {!λ i → //-elimP (λ g → //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ g₁ → refl))))!}

CCatwithsig.sigStr sigStrSynCCat = sigStrS
CCatwithsig.sigStrₛ sigStrSynCCat {Γ = Γ} {a = a} {b = b} = sigStrₛS _ Γ a _ _ b _ _
CCatwithsig.sigStr₁ sigStrSynCCat {Γ = Γ} {a = a} {b = b} = sigStr₁S _ Γ a _ _ b _ _
CCatwithsig.sigStrNat sigStrSynCCat = {!explicitify f!} where --sigStrSNat g Γ a aₛ a₁ b bₛ b₁ g₁
  f : {!!}
  f = {!!}

{- pair -}

pairStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : S.ft (proj B) ≡ proj A) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : S.∂₁ (proj a) ≡ proj A) (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : S.∂₁ (proj b) ≡ S.star (proj a) (proj B) B= a₁) → DMor n (suc n)
pairStrS-// Γ A A= B B= a aₛ a₁ b bₛ b₁ = dmorTm Γ (sig (getTy A) (getTy B))
                                                   (Sig (dTy A A=) (dTy+ A= B B=))
                                                   (pair (getTy A) (getTy B) (getTm a) (getTm b))
                                                   (Pair (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)) 


pairStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : S.ft (proj A) ≡ proj Γ) (A'= : S.ft (proj A') ≡ proj Γ') {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : S.ft (proj B) ≡ proj A) (B'= : S.ft (proj B') ≡ proj A') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : S.∂₁ (proj a) ≡ proj A) (a'₁ : S.∂₁ (proj a') ≡ proj A') {b b' : DMor n (suc n)} (rb : b ≃ b') (bₛ : S.is-section (proj b)) (b'ₛ : S.is-section (proj b')) (b₁ : S.∂₁ (proj b) ≡ S.star (proj a) (proj B) B= a₁) (b'₁ : S.∂₁ (proj b') ≡ S.star (proj a') (proj B') B'= a'₁) → proj {R = MorEquiv} (pairStrS-// Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ proj (pairStrS-// Γ' A' A'= B' B'= a' a'ₛ a'₁ b' b'ₛ b'₁)
pairStrS-eq rΓ {A} {A'} rA A= A'= {B} {B'} rB B= B'= {a} {a'} ra aₛ a'ₛ a₁ a'₁ {b} {b'} rb bₛ b'ₛ b₁ b'₁ =
            dmorTm= rΓ (Sig (dTy A A=) (dTy+ A= B B=))
                       (Sig (dTy A' A'=) (dTy+ A'= B' B'=))
                       (SigCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=))
                       (Pair (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁))
                       (Pair (dTy A' A'=) (dTy+ A'= B' B'=) (dTm A'= a' a'ₛ a'₁) (dTmSubst A'= B' B'= a' a'ₛ a'₁ b' b'ₛ b'₁))
                       (PairCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁) (dTmSubst= A= rB B= B'= ra aₛ a'ₛ a₁ a'₁ rb bₛ b'ₛ b₁ b'₁))

pairStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ S.star a B B= a₁) → MorS n (suc n)
pairStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → //-elim-Tm (λ a aₛ a₁ → //-elim-Tm (λ b bₛ b₁ → proj (pairStrS-// Γ A A= B B= a aₛ a₁ b bₛ b₁))
                                                                                                           (λ rb bₛ b'ₛ b₁ b'₁ → proj= (pairStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= (ref a) aₛ aₛ a₁ a₁ rb bₛ b'ₛ b₁ b'₁)))
                                                                                   (λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (pairStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= ra aₛ a'ₛ a₁ a'₁ (ref b) bₛ bₛ b₁ b₁'))))
                                                              (λ rB B= B'= → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (pairStrS-eq (ref Γ) (ref A) A= A= rB B= B'= (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁')))))
                                         (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (pairStrS-eq (ref Γ) rA A= A'= (ref B) B= B=' (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁'))))))
                       (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (pairStrS-eq rΓ (ref A) A= A=' (ref B) B= B=' (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁'))))))
           
pairStrₛS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ S.star a B B= a₁) → S.is-section (pairStrS Γ A A= B B= a aₛ a₁ b bₛ b₁)
pairStrₛS =  //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → dmorTmₛ (Sig (dTy A A=) (dTy+ A= B B=)) (Pair (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)))))))

pairStr₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ S.star a B B= a₁) → S.∂₁ (pairStrS Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ SigStrS Γ A A= B B=
pairStr₁S =  //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → refl)))))

pairStrSynCCat : CCatwithpair synCCat SigStrSynCCat
CCatwithpair.pairStr pairStrSynCCat = pairStrS
CCatwithpair.pairStrₛ pairStrSynCCat {Γ = Γ} {A = A} {B = B} {a = a} {b = b} = pairStrₛS Γ A _ B _ a _ _ b _ _
CCatwithpair.pairStr₁ pairStrSynCCat {Γ = Γ} {A = A} {B = B} {a = a} {b = b} = pairStr₁S Γ A _ B _ a _ _ b _ _
CCatwithpair.pairStrNat pairStrSynCCat = {!!} --g {B = B} {a = a} {b = b} p = ? -- pairStrNatS g B a _ _ b _ _ p


{- pr1 -}

pr1StrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : S.ft (proj B) ≡ proj A) (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj Γ) (proj A) A= (proj B) B=) → DMor n (suc n)
pr1StrS-// Γ A A= B B= u uₛ u₁ = dmorTm Γ (getTy A) (dTy A A=) (pr1 (getTy A) (getTy B) (getTm u))
                                                            (Pr1 (dTy A A=) (dTy+ A= B B=) (dTm refl u uₛ u₁))


pr1StrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : S.ft (proj A) ≡ proj Γ) (A'= : S.ft (proj A') ≡ proj Γ') {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : S.ft (proj B) ≡ (proj A)) (B'= : S.ft (proj B') ≡ proj A') {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj Γ) (proj A) A= (proj B) B=) (u'₁ : ∂₁S (proj u') ≡ SigStrS (proj Γ') (proj A') A'= (proj B') B'=) → proj {R = MorEquiv} (pr1StrS-// Γ A A= B B= u uₛ u₁) ≡ proj (pr1StrS-// Γ' A' A'= B' B'= u' u'ₛ u'₁)
pr1StrS-eq {Γ = Γ} {Γ'} rΓ {A} {A'} rA A= A'= {B} {B'} rB B= B'= {u} {u'} ru uₛ u'ₛ u₁ u'₁ =
              dmorTm= rΓ (dTy A A=) (dTy A' A'=) (dTy= rA A=) (Pr1 (dTy A A=) (dTy+ A= B B=) (dTm refl u uₛ u₁))
                                                              (Pr1 (dTy A' A'=) (dTy+ A'= B' B'=) (dTm refl u' u'ₛ u'₁))
                                                              (Pr1Cong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=) (dTm= (box (unOb≃ rΓ ,, SigCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=))) refl ru uₛ u'ₛ u₁ u'₁))


pr1StrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=) → MorS n (suc n)
pr1StrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → //-elim-Tm (λ u uₛ u₁ → proj (pr1StrS-// Γ A A= B B= u uₛ u₁))
                                                                                   (λ ru uₛ u'ₛ u₁ u'₁ → proj= (pr1StrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= ru uₛ u'ₛ u₁ u'₁)))
                                                              (λ rB B= B'= → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (pr1StrS-eq (ref Γ) (ref A) A= A= rB B= B'= (ref u) uₛ uₛ u₁ u₁'))))
                                         (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (pr1StrS-eq (ref Γ) rA A= A'= (ref B) B= B=' (ref u) uₛ uₛ u₁ u₁')))))
                       (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (pr1StrS-eq rΓ (ref A) A= A=' (ref B) B= B=' (ref u) uₛ uₛ u₁ u₁')))))

pr1StrₛS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=) → S.is-section (pr1StrS Γ A A= B B= u uₛ u₁)
pr1StrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → dmorTmₛ (dTy A A=) (Pr1 (dTy A A=) (dTy+ A= B B=) (dTm refl u uₛ u₁))))))

pr1Str₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=) → S.∂₁ (pr1StrS Γ A A= B B= u uₛ u₁) ≡ A
pr1Str₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → eq (box (CtxTy=Ctx A A=))))))


pr1StrSynCCat : CCatwithpr1 synCCat SigStrSynCCat
CCatwithpr1.pr1Str pr1StrSynCCat = pr1StrS
CCatwithpr1.pr1Strₛ pr1StrSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = pr1StrₛS Γ A _ B _ u _ _
CCatwithpr1.pr1Str₁ pr1StrSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = pr1Str₁S Γ A _ B _ u _ _
CCatwithpr1.pr1StrNat pr1StrSynCCat = {!!} 


{- pr2 -}

pr2StrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : S.ft (proj B) ≡ proj A) (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj Γ) (proj A) A= (proj B) B=) → DMor n (suc n)
pr2StrS-// Γ A A= B B= u uₛ u₁ = dmorTm Γ (substTy (getTy B) (pr1 (getTy A) (getTy B) (getTm u)))
                                          (SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (Pr1 (dTy A A=) (dTy+ A= B B=) (dTm refl u uₛ u₁))))
                                          (pr2 (getTy A) (getTy B) (getTm u))
                                          (Pr2 (dTy A A=) (dTy+ A= B B=) (dTm refl u uₛ u₁))


pr2StrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : S.ft (proj A) ≡ proj Γ) (A'= : S.ft (proj A') ≡ proj Γ') {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : S.ft (proj B) ≡ (proj A)) (B'= : S.ft (proj B') ≡ proj A') {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj Γ) (proj A) A= (proj B) B=) (u'₁ : ∂₁S (proj u') ≡ SigStrS (proj Γ') (proj A') A'= (proj B') B'=) → proj {R = MorEquiv} (pr2StrS-// Γ A A= B B= u uₛ u₁) ≡ proj (pr2StrS-// Γ' A' A'= B' B'= u' u'ₛ u'₁)
pr2StrS-eq {Γ = Γ} {Γ'} rΓ {A} {A'} rA A= A'= {B} {B'} rB B= B'= {u} {u'} ru uₛ u'ₛ u₁ u'₁ =
              dmorTm= rΓ (SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (Pr1 (dTy A A=) (dTy+ A= B B=) (dTm refl u uₛ u₁))))
                         (SubstTy (dTy+ A'= B' B'=) (idMor+ (der Γ') (Pr1 (dTy A' A'=) (dTy+ A'= B' B'=) (dTm refl u' u'ₛ u'₁))))
                         (SubstTyMorEq2 (der Γ) ((der Γ) , (dTy A A=)) (dTy+= A= rB B=) (idMor+= (der Γ) (Pr1Cong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=) (dTm= (box (unOb≃ rΓ ,, SigCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=))) refl ru uₛ u'ₛ u₁ u'₁))))
                         (Pr2 (dTy A A=) (dTy+ A= B B=) (dTm refl u uₛ u₁))
                         (Pr2 (dTy A' A'=) (dTy+ A'= B' B'=) (dTm refl u' u'ₛ u'₁))
                         (Pr2Cong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=) (dTm= (box (unOb≃ rΓ ,, SigCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=))) refl ru uₛ u'ₛ u₁ u'₁))


pr2StrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=) → MorS n (suc n)
pr2StrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → //-elim-Tm (λ u uₛ u₁ → proj (pr2StrS-// Γ A A= B B= u uₛ u₁))
                                                                                   (λ ru uₛ u'ₛ u₁ u'₁ → proj= (pr2StrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= ru uₛ u'ₛ u₁ u'₁)))
                                                              (λ rB B= B'= → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (pr2StrS-eq (ref Γ) (ref A) A= A= rB B= B'= (ref u) uₛ uₛ u₁ u₁'))))
                                         (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (pr2StrS-eq (ref Γ) rA A= A'= (ref B) B= B=' (ref u) uₛ uₛ u₁ u₁')))))
                       (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (pr2StrS-eq rΓ (ref A) A= A=' (ref B) B= B=' (ref u) uₛ uₛ u₁ u₁')))))

pr2StrₛS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=) → S.is-section (pr2StrS Γ A A= B B= u uₛ u₁)
pr2StrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → dmorTmₛ (SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (Pr1 (dTy A A=) (dTy+ A= B B=) (dTm refl u uₛ u₁)))) (Pr2 (dTy A A=) (dTy+ A= B B=) (dTm refl u uₛ u₁))))))

pr2Str₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=) → S.∂₁ (pr2StrS Γ A A= B B= u uₛ u₁) ≡ S.star (pr1StrS Γ A A= B B= u uₛ u₁) B B= (pr1Str₁S Γ A A= B B= u uₛ u₁)
pr2Str₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → refl))))


pr2StrSynCCat : CCatwithpr2 synCCat SigStrSynCCat pr1StrSynCCat
CCatwithpr2.pr2Str pr2StrSynCCat = pr2StrS
CCatwithpr2.pr2Strₛ pr2StrSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = pr2StrₛS Γ A _ B _ u _ _
CCatwithpr2.pr2Str₁ pr2StrSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = pr2Str₁S Γ A _ B _ u _ _
CCatwithpr2.pr2StrNat pr2StrSynCCat = {!!} 

{- nat -}

natStrS-// : (i : ℕ) (Γ : DCtx n) → DMor n (suc n)
natStrS-// i Γ = dmorTm Γ (uu i) UU (nat i) NatUU -- dmor X ((ctx X , uu i) , (der X , UU)) (idMor _ , nat i) (idMor+ (der X) NatUU)
 
natStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → proj {R = MorEquiv} (natStrS-// i Γ) ≡ proj (natStrS-// i Γ')
natStrS-eq i {Γ = Γ} {Γ'} rΓ = dmorTm= rΓ UU UU UUCong NatUU NatUU NatUUCong --eq ((rX , (rX ,, UUCong)) , (idMor+= (der X) NatUUCong))

natStrS : (i : ℕ) (Γ : ObS n) → MorS n (suc n)
natStrS i = //-elim-Ctx (λ Γ → proj (natStrS-// i Γ)) (λ rΓ → proj= (natStrS-eq i rΓ)) --//-rec (λ X → proj (natStrS-// i X)) (λ {X} {X'} rX → natStrS-eq i X X' rX)

natStrₛS : (i : ℕ) (Γ : ObS n) → S.is-section (natStrS i Γ)
natStrₛS i = //-elimP (λ Γ → dmorTmₛ UU NatUU) --//-elimP (λ X → natStrₛS-// i X)

natStr₁S : (i : ℕ) (Γ : ObS n) → ∂₁S (natStrS i Γ) ≡ UUStrS i Γ
natStr₁S i = //-elimP (λ Γ → refl)


natStrSynCCat : CCatwithnat synCCat UUStrSynCCat
CCatwithnat.natStr natStrSynCCat = natStrS
CCatwithnat.natStrₛ natStrSynCCat {Γ = Γ} = natStrₛS _ Γ
CCatwithnat.natStr₁ natStrSynCCat {Γ = Γ} = natStr₁S _ Γ
CCatwithnat.natStrNat natStrSynCCat = {!!} --g {X = X} p = natStrNatS _ g X p


{- zero -}

zeroStrS-// : (Γ : DCtx n) → DMor n (suc n)
zeroStrS-// Γ = dmorTm Γ nat Nat zero Zero

zeroStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → proj {R = MorEquiv} (zeroStrS-// Γ) ≡ proj (zeroStrS-// Γ')
zeroStrS-eq rΓ = dmorTm= rΓ Nat Nat NatCong Zero Zero ZeroCong

zeroStrS : (Γ : ObS n) → MorS n (suc n)
zeroStrS = //-rec (λ Γ → proj (zeroStrS-// Γ)) (λ rΓ → zeroStrS-eq rΓ)

zeroStrₛS : (Γ : ObS n) → S.is-section (zeroStrS Γ)
zeroStrₛS = //-elimP (λ Γ → dmorTmₛ Nat Zero)

zeroStr₁S : (Γ : ObS n) → ∂₁S (zeroStrS Γ) ≡ NatStrS Γ
zeroStr₁S = //-elimP (λ Γ → refl)

zeroStrSynCCat : CCatwithzero synCCat NatStrSynCCat
CCatwithzero.zeroStr zeroStrSynCCat = zeroStrS 
CCatwithzero.zeroStrₛ zeroStrSynCCat {Γ = Γ} = zeroStrₛS Γ
CCatwithzero.zeroStr₁ zeroStrSynCCat {Γ = Γ} = zeroStr₁S Γ
CCatwithzero.zeroStrNat zeroStrSynCCat = {!zeroStrNatS g A B B= p!}

module Szero = CCatwithzero zeroStrSynCCat

{- suc -}

sucStrS-// : (Γ : DCtx n) (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (proj Γ)) → DMor n (suc n)
sucStrS-// Γ u uₛ u₁ = dmorTm Γ nat Nat (suc (getTm u)) (Suc (dTm refl u uₛ u₁))

sucStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : _) (u'ₛ : _) (u₁ : _) (u'₁ : _) → proj {R = MorEquiv} (sucStrS-// Γ u uₛ u₁) ≡ proj (sucStrS-// Γ' u' u'ₛ u'₁)
sucStrS-eq rΓ ru uₛ u'ₛ u₁ u'₁ = dmorTm= rΓ Nat Nat NatCong (Suc (dTm refl _ uₛ u₁)) (Suc (dTm refl _ u'ₛ u'₁)) (SucCong (dTm= (box (unOb≃ rΓ ,, TyRefl Nat)) refl ru uₛ u'ₛ u₁ u'₁))

sucStrS : (Γ : ObS n) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ) → MorS n (suc n)
sucStrS = //-elim-Ctx (λ Γ → //-elim-Tm (λ u uₛ u₁ → proj (sucStrS-// Γ u uₛ u₁))
                                        (λ ru uₛ u'ₛ u₁ u'₁ → proj= (sucStrS-eq (ref Γ) ru uₛ u'ₛ u₁ u'₁)))
                      (λ rΓ → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (sucStrS-eq rΓ (ref u) uₛ uₛ u₁ u₁')))

sucStrₛS : (Γ : ObS n) (u : MorS n (suc n)) {uₛ : S.is-section u} {u₁ : ∂₁S u ≡ NatStrS Γ} → S.is-section (sucStrS Γ u uₛ u₁)
sucStrₛS = //-elimP (λ Γ → //-elimP (λ u {uₛ} {u₁} → dmorTmₛ Nat (Suc (dTm refl u uₛ u₁))))

sucStr₁S : (Γ : ObS n) (u : MorS n (suc n)) {uₛ : S.is-section u} {u₁ : ∂₁S u ≡ NatStrS Γ} → ∂₁S (sucStrS Γ u uₛ u₁) ≡ NatStrS Γ
sucStr₁S = //-elimP (λ Γ → //-elimP (λ u → refl))

sucStrSynCCat : CCatwithsuc synCCat NatStrSynCCat
CCatwithsuc.sucStr sucStrSynCCat = sucStrS
CCatwithsuc.sucStrₛ sucStrSynCCat {Γ = Γ} {u = u} = sucStrₛS Γ u
CCatwithsuc.sucStr₁ sucStrSynCCat {Γ = Γ} {u = u} = sucStr₁S Γ u
CCatwithsuc.sucStrNat sucStrSynCCat = {!NatStrNatS g A B B= p!}

module Ssuc = CCatwithsuc sucStrSynCCat

{- natelim -}




natelimStrS-// : (Γ : DCtx n) (P : DCtx (suc (suc n))) (P= : ftS (proj P) ≡ NatStrS (proj Γ))
                 (dO : DMor n (suc n)) (dOₛ : S.is-section (proj dO)) (dO₁ : ∂₁S (proj dO) ≡ S.star (zeroStrS (proj Γ)) (proj P) P= (zeroStr₁S (proj Γ)))
                 (dS : DMor (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section (proj dS)) (dS₁ : ∂₁S (proj dS) ≡ T-dS₁ sucStrSynCCat (proj Γ) (proj P) P=)
                 (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (proj Γ))
                 → DMor n (suc n)
natelimStrS-// Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁ = let fixSubstTyP = (! (weaken[]Ty _ _ last) ∙ ap weakenTy ([idMor]Ty _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty (getTy P)) (ap (λ z → z , suc (var last)) (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _)) ∙  ! (weakenTyInsert' _ _ _ _ ∙ refl))) in
               dmorTm Γ (substTy (getTy P) (getTm u)) (SubstTy (dTy P P=) (idMor+ (der Γ) (dTm refl u uₛ u₁)))
                        (natelim (getTy P) (getTm dO) (getTm dS) (getTm u))
                        (Natelim (dTy P P=)
                                 (dTm refl dO dOₛ dO₁)
                                 (congTmTy fixSubstTyP (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (eq (box (CtxSymm (CtxTy=Ctx P P=)))) dS dSₛ dS₁))
                                 (dTm refl u uₛ u₁))


natelimStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {P P' : DCtx (suc (suc n))} (rP : P ≃ P') (P= : ftS (proj P) ≡ NatStrS (proj Γ)) (P'= : ftS (proj P') ≡ NatStrS (proj Γ')) {dO dO' : DMor n (suc n)} (rdO : dO ≃ dO') (dOₛ : S.is-section (proj dO)) (dO'ₛ : S.is-section (proj dO')) (dO₁ : ∂₁S (proj dO) ≡ S.star (zeroStrS (proj Γ)) (proj P) P= (zeroStr₁S (proj Γ))) (dO'₁ : ∂₁S (proj dO') ≡ S.star (zeroStrS (proj Γ')) (proj P') P'= (zeroStr₁S (proj Γ')))
                   {dS dS' : DMor (suc (suc n)) (suc (suc (suc n)))} (rdS : dS ≃ dS') (dSₛ : S.is-section (proj dS))(dS'ₛ : S.is-section (proj dS'))
                   (dS₁ : ∂₁S (proj dS) ≡  T-dS₁ sucStrSynCCat (proj Γ) (proj P) P=)
                   (dS'₁ : ∂₁S (proj dS') ≡ T-dS₁ sucStrSynCCat (proj Γ') (proj P') P'=)
                   {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : ∂₁S (proj u) ≡ NatStrS (proj Γ)) (u'₁ : ∂₁S (proj u') ≡ NatStrS (proj Γ')) → proj {R = MorEquiv} (natelimStrS-// Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) ≡ proj (natelimStrS-// Γ' P' P'= dO' dO'ₛ dO'₁ dS' dS'ₛ dS'₁ u' u'ₛ u'₁)
natelimStrS-eq {Γ = Γ} {Γ'} rΓ {P} {P'} rP P= P'= {dO} {dO'} rdO dOₛ dO'ₛ dO₁ dO'₁ {dS} {dS'} rdS dSₛ dS'ₛ dS₁ dS'₁ {u} {u'} ru uₛ u'ₛ u₁ u'₁ =
                  let fixSubstTy X = (! (weaken[]Ty _ _ last) ∙ ap weakenTy ([idMor]Ty _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty (getTy X)) (ap (λ z → z , suc (var last)) (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _)) ∙  ! (weakenTyInsert' _ _ _ _ ∙ refl)))                      
                  in  
               dmorTm= rΓ (SubstTy (dTy P P=) (idMor+ (der Γ) (dTm refl u uₛ u₁)))
                          (SubstTy (dTy P' P'=) (idMor+ (der Γ') (dTm refl u' u'ₛ u'₁)))
                          (SubstTyMorEq2 (der Γ) (der Γ , Nat) (dTy= rP P=) (idMor+= (der Γ) (dTm= (box (unOb≃ rΓ ,, NatCong)) refl ru uₛ u'ₛ u₁ u'₁)))
                          (Natelim (dTy P P=)
                                   (dTm refl dO dOₛ dO₁)
                                   (congTmTy (fixSubstTy P) (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (eq (box (CtxSymm (CtxTy=Ctx P P=)))) dS dSₛ dS₁))
                                   (dTm refl u uₛ u₁))
                          (Natelim (dTy P' P'=) 
                                   (dTm refl dO' dO'ₛ dO'₁)
                                   (congTmTy (fixSubstTy P') (dTm {Γ = (((_ , _) , _) , ((der Γ' , Nat) , dTy P' P'=))} (eq (box (CtxSymm (CtxTy=Ctx P' P'=)))) dS' dS'ₛ dS'₁))
                                   (dTm refl u' u'ₛ u'₁))
                          (NatelimCong (dTy P P=) (dTy= rP P=)
                                       (dTm= (box (unOb≃ rΓ ,, SubstTyMorEq2 (der Γ) (der Γ , Nat) (dTy= rP P=) (idMor+= (der Γ) ZeroCong))) refl rdO dOₛ dO'ₛ dO₁ dO'₁)
                                       (congTmEqTy (fixSubstTy P) (dTm= {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (box (unOb≃ rP ,, SubstTyEq (SubstTyEq (SubstTyEq (dTy= rP P=) ((WeakMor _ (WeakMor _ (idMorDerivable (der Γ)))) , (VarLast Nat))) ((idMorDerivable (der Γ , Nat)) , (Suc (VarLast Nat)))) (ConvMor (WeakMor _ (WeakMor _ (idMorDerivable (der Γ)))) (CtxTy=Ctx P P=) (CtxRefl (der Γ)) , ConvTm (VarPrev Nat (VarLast Nat)) (CtxTy=Ctx P P=)))) (eq (box (CtxSymm (CtxTy=Ctx P P=)))) rdS dSₛ dS'ₛ dS₁ dS'₁))
                                       (dTm= (box (unOb≃ rΓ ,, NatCong)) refl ru uₛ u'ₛ u₁ u'₁))
               
natelimStrS : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
              (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : ∂₁S dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
              (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : ∂₁S dS ≡ T-dS₁ sucStrSynCCat Γ P P=)
              (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ)
              → MorS n (suc n)
natelimStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ P P= → //-elim-Tm (λ dO dOₛ dO₁ → //-elim-Tm (λ dS dSₛ dS₁ → //-elim-Tm (λ u uₛ u₁ → proj (natelimStrS-// Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁))
                                                                                                                       (λ ru uₛ u'ₛ u₁ u'₁ → proj= (natelimStrS-eq (ref Γ) (ref P) P= P= (ref dO) dOₛ dOₛ dO₁ dO₁ (ref dS) dSₛ dSₛ dS₁ dS₁ ru uₛ u'ₛ u₁ u'₁)))
                                                                                            (λ rdS dSₛ dS'ₛ dS₁ dS'₁ → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (natelimStrS-eq (ref Γ) (ref P) P= P= (ref dO) dOₛ dOₛ dO₁ dO₁ rdS dSₛ dS'ₛ dS₁ dS'₁ (ref u) uₛ uₛ u₁ u₁'))))
                                                                 (λ rdO dOₛ dO'ₛ dO₁ dO'₁ → //-elimP-Tm (λ dS dSₛ dS₁ dS₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (natelimStrS-eq (ref Γ) (ref P) P= P= rdO dOₛ dO'ₛ dO₁ dO'₁ (ref dS) dSₛ dSₛ dS₁ dS₁' (ref u) uₛ uₛ u₁ u₁')))))
                                            (λ rP P= P'= → //-elimP-Tm (λ dO dOₛ dO₁ dO₁' → //-elimP-Tm (λ dS dSₛ dS₁ dS₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (natelimStrS-eq (ref Γ) rP P= P'= (ref dO) dOₛ dOₛ dO₁ dO₁' (ref dS) dSₛ dSₛ dS₁ dS₁' (ref u) uₛ uₛ u₁ u₁'))))))
                          (λ rΓ → //-elimP-Ty (λ P P= P=' → //-elimP-Tm (λ dO dOₛ dO₁ dO₁' → //-elimP-Tm (λ dS dSₛ dS₁ dS₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (natelimStrS-eq rΓ (ref P) P= P=' (ref dO) dOₛ dOₛ dO₁ dO₁' (ref dS) dSₛ dSₛ dS₁ dS₁' (ref u) uₛ uₛ u₁ u₁'))))))


natelimStrₛS : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
               (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : ∂₁S dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
               (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : ∂₁S dS ≡ T-dS₁ sucStrSynCCat Γ P P=)
               (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ) → S.is-section (natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)
natelimStrₛS = let fixSubstTy X = (! (weaken[]Ty _ _ last) ∙ ap weakenTy ([idMor]Ty _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty (getTy X)) (ap (λ z → z , suc (var last)) (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _)) ∙  ! (weakenTyInsert' _ _ _ _ ∙ refl)))
               in
               //-elimP (λ Γ → //-elimP (λ P P= → //-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → //-elimP (λ u uₛ u₁ →  dmorTmₛ (SubstTy (dTy P P=) (idMor+ (der Γ) (dTm refl u uₛ u₁))) (Natelim (dTy P P=)
                                   (dTm refl dO dOₛ dO₁)
                                   (congTmTy (fixSubstTy P) (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (eq (box (CtxSymm (CtxTy=Ctx P P=)))) dS dSₛ dS₁))
                                   (dTm refl u uₛ u₁)))))))

natelimStr₁S : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
               (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : ∂₁S dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
               (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : ∂₁S dS ≡ T-dS₁ sucStrSynCCat Γ P P=)
               (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ) → S.∂₁ (natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) ≡ S.star u P P= u₁
natelimStr₁S = //-elimP (λ Γ → //-elimP (λ P P= → //-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → //-elimP (λ u uₛ u₁ → eq (box (CtxSymm (reflectOb (S.is-section₀ uₛ u₁)) ,, SubstTyMorEq (dTy P P=) (idMor+ (der Γ) (dTm refl u uₛ u₁)) (ConvMorEq (MorSymm (der (lhs u)) (der (rhs u)) (morTm=idMorTm' uₛ)) (reflectOb (S.is-section₀ uₛ u₁)) (reflectOb u₁)))))))))


natelimStrSynCCat : CCatwithnatelim synCCat NatStrSynCCat zeroStrSynCCat sucStrSynCCat
CCatwithnatelim.natelimStr natelimStrSynCCat = natelimStrS
CCatwithnatelim.natelimStrₛ natelimStrSynCCat {Γ = Γ} {P = P} {dO = dO} {dS = dS} {u = u} = natelimStrₛS Γ P _ dO _ _ dS _ _ u _ _
CCatwithnatelim.natelimStr₁ natelimStrSynCCat {Γ = Γ} {P = P} {dO = dO} {dS = dS} {u = u} = natelimStr₁S Γ P _ dO _ _ dS _ _ u _ _
CCatwithnatelim.natelimStrNat natelimStrSynCCat = {!!} 



-- CCatwithnatelim.natelimStr natelimStrSynCCat = {!natelimStrS!}

{- id -}

idStrS-// : (i : ℕ) (Γ : DCtx n) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (proj Γ)) (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj Γ) (proj a) aₛ a₁)  (v : DMor n (suc n)) (vₛ : S.is-section (proj v)) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj Γ) (proj a) aₛ a₁) → DMor n (suc n)
idStrS-// i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁ = dmorTm Γ (uu i) UU (id i (getTm a) (getTm u) (getTm v))
                                                           (IdUU (dTm refl a aₛ a₁) (dTm refl u uₛ u₁) (dTm refl v vₛ v₁)) 

idStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ UUStrS i (proj Γ)) (a'₁ : ∂₁S (proj a') ≡ UUStrS i (proj Γ')) {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj Γ) (proj a) aₛ a₁)  (u'₁ : ∂₁S (proj u') ≡ ElStrS i (proj Γ') (proj a') a'ₛ a'₁) {v v' : DMor n (suc n)} (rv : v ≃ v') (vₛ : S.is-section (proj v)) (v'ₛ : S.is-section (proj v')) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj Γ) (proj a) aₛ a₁) (v'₁ : ∂₁S (proj v') ≡ ElStrS i (proj Γ') (proj a') a'ₛ a'₁) → proj {R = MorEquiv} (idStrS-// i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ proj (idStrS-// i Γ' a' a'ₛ a'₁ u' u'ₛ u'₁ v' v'ₛ v'₁)
idStrS-eq i {Γ} {Γ'} rΓ {a} {a'} ra aₛ a'ₛ a₁ a'₁ {u} {u'} ru uₛ u'ₛ u₁ u'₁ {v} {v'} rv vₛ v'ₛ v₁ v'₁ =
          dmorTm= rΓ UU UU UUCong (IdUU (dTm refl a aₛ a₁) (dTm refl u uₛ u₁) (dTm refl v vₛ v₁))
                                  (IdUU (dTm refl a' a'ₛ a'₁) (dTm refl u' u'ₛ u'₁) (dTm refl v' v'ₛ v'₁))
                                  (IdUUCong (dTm= (box (unOb≃ rΓ ,, UUCong)) refl ra aₛ a'ₛ a₁ a'₁)
                                            (dTm= (box (unOb≃ rΓ ,, ElCong (dTm= (box (unOb≃ rΓ ,, UUCong)) refl ra aₛ a'ₛ a₁ a'₁))) refl ru uₛ u'ₛ u₁ u'₁)
                                            (dTm= (box (unOb≃ rΓ ,, ElCong (dTm= (box (unOb≃ rΓ ,, UUCong)) refl ra aₛ a'ₛ a₁ a'₁))) refl rv vₛ v'ₛ v₁ v'₁))

idStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)  (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁) → MorS n (suc n)
idStrS i = //-elim-Ctx (λ Γ → //-elim-Tm (λ a aₛ a₁ → //-elim-Tm (λ u uₛ u₁ → //-elim-Tm (λ v vₛ v₁ → proj (idStrS-// i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁))
                                                                                         (λ rv vₛ v'ₛ v₁ v'₁ → proj= (idStrS-eq i (ref Γ) (ref a) aₛ aₛ a₁ a₁ (ref u) uₛ uₛ u₁ u₁ rv vₛ v'ₛ v₁ v'₁)))
                                                                 (λ ru uₛ u'ₛ u₁ u'₁ → //-elimP-Tm (λ v vₛ v₁ v₁' → proj= (idStrS-eq i (ref Γ) (ref a) aₛ aₛ a₁ a₁ ru uₛ u'ₛ u₁ u'₁ (ref v) vₛ vₛ v₁ v₁'))))
                                         (λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ u uₛ u₁ u₁' → //-elimP-Tm (λ v vₛ v₁ v₁' → proj= (idStrS-eq i (ref Γ) ra aₛ a'ₛ a₁ a'₁ (ref u) uₛ uₛ u₁ u₁' (ref v) vₛ vₛ v₁ v₁')))))
                       (λ rΓ → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → //-elimP-Tm (λ v vₛ v₁ v₁' → proj= (idStrS-eq i rΓ (ref a) aₛ aₛ a₁ a₁' (ref u) uₛ uₛ u₁ u₁' (ref v) vₛ vₛ v₁ v₁')))))
                                       
                                                                                       

idStrₛS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)  (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁) → S.is-section (idStrS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁)
idStrₛS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → dmorTmₛ UU (IdUU (dTm refl a aₛ a₁) (dTm refl u uₛ u₁) (dTm refl v vₛ v₁))))))

idStr₁S : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)  (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁) → ∂₁S (idStrS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ UUStrS i Γ
idStr₁S i = //-elimP (λ Γ →  //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → refl))))

idStrSynCCat : CCatwithid synCCat UUStrSynCCat ElStrSynCCat
CCatwithid.idStr idStrSynCCat = idStrS
CCatwithid.idStrₛ idStrSynCCat {Γ = Γ} {a = a} {u = u} {v = v} = idStrₛS _ Γ a _ _ u _ _ v _ _
CCatwithid.idStr₁ idStrSynCCat {Γ = Γ} {a = a} {u = u} {v = v} = idStr₁S _ Γ a _ _ u _ _ v _ _
CCatwithid.idStrNat idStrSynCCat = {!!} -- g {a = a} {u = u} {v = v} p = idStrNatS _ g a _ _ u _ _ v _ _ p


{- refl -}

reflStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ (proj A)) → DMor n (suc n)
reflStrS-// Γ A A= a aₛ a₁ = dmorTm Γ (id (getTy A) (getTm a) (getTm a)) (Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= a aₛ a₁)) (refl (getTy A) (getTm a)) (Refl (dTy A A=) (dTm A= a aₛ a₁))

reflStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : S.ft (proj A) ≡ proj Γ) (A'= : S.ft (proj A') ≡ proj Γ') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ (proj A)) (a'₁ : ∂₁S (proj a') ≡ (proj A')) → proj {R = MorEquiv} (reflStrS-// Γ A A= a aₛ a₁) ≡ proj (reflStrS-// Γ' A' A'= a' a'ₛ a'₁)
reflStrS-eq rΓ {A} {A'} rA A= A'= {a} {a'} ra aₛ a'ₛ a₁ a'₁ = dmorTm= rΓ (Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= a aₛ a₁))
                                                                         (Id (dTy A' A'=) (dTm A'= a' a'ₛ a'₁) (dTm A'= a' a'ₛ a'₁))
                                                                         (IdCong (dTy= rA A=) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁))
                                                                         (Refl (dTy A A=) (dTm A= a aₛ a₁))
                                                                         (Refl (dTy A' A'=) (dTm A'= a' a'ₛ a'₁))
                                                                         (ReflCong (dTy= rA A=) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁))

reflStrS  : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) → MorS n (suc n)
reflStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Tm (λ a aₛ a₁ → proj (reflStrS-// Γ A A= a aₛ a₁))
                                                              (λ ra aₛ a'ₛ a₁ a'₁ → proj= (reflStrS-eq (ref Γ) (ref A) A= A= ra aₛ a'ₛ a₁ a'₁)))
                                         (λ rA A= A'= → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (reflStrS-eq (ref Γ) rA A= A'= (ref a) aₛ aₛ a₁ a₁'))))
                       (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (reflStrS-eq rΓ (ref A) A= A=' (ref a) aₛ aₛ a₁ a₁'))))
                       
reflStrₛS :  (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) → S.is-section (reflStrS Γ A A= a aₛ a₁)
reflStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → (//-elimP (λ a aₛ a₁ → dmorTmₛ (Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= a aₛ a₁)) (Refl (dTy A A=) (dTm A= a aₛ a₁))))))

reflStr₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) → ∂₁S (reflStrS Γ A A= a aₛ a₁) ≡ IdStrS Γ A A= a aₛ a₁ a aₛ a₁
reflStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → (//-elimP (λ a aₛ a₁ → refl))))


reflStrSynCCat : CCatwithrefl synCCat IdStrSynCCat
CCatwithrefl.reflStr reflStrSynCCat = reflStrS
CCatwithrefl.reflStrₛ reflStrSynCCat {Γ = Γ} {A = A} {a = a} = reflStrₛS Γ A _ a _ _
CCatwithrefl.reflStr₁ reflStrSynCCat {Γ = Γ} {A = A} {a = a} = reflStr₁S Γ A _ a _ _
CCatwithrefl.reflStrNat reflStrSynCCat = {!!} -- g {A = A} {u = u} p = reflStrNatS g A u _ _ p


{- jj -}


--Naturality of type formers


-- SigStrNatS-// : (g : DMor n m) (B : DCtx (suc (suc m))) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g)) → starS (proj g) (SigStrS (proj B)) (! (SigStr=S (proj B) ∙ p)) ≡ SigStrS (star+S (proj g) (proj B) p)
-- SigStrNatS-// (dmor (Γ , dΓ) (Δ , dΔ) δ dδ) (((_ , A) , B), ((_ , dA) , dB)) p = refl

-- SigStrNatS : (g : MorS n m) (B : ObS (suc (suc m))) (p : ftS (ftS B) ≡ ∂₁S g) → starS g (SigStrS B) (! (SigStr=S B ∙ p)) ≡ SigStrS (star+S g B p)
-- SigStrNatS = //-elimP (λ g → //-elimP (SigStrNatS-// g))


-- NatStrNatS-// : (g : DMor n m) (X : DCtx m) (p : proj X ≡ ∂₁S (proj g)) → starS (proj g) (NatStrS (proj X)) (! (NatStr=S (proj X) ∙ p)) ≡ NatStrS (∂₀S (proj g))
-- NatStrNatS-// g (Γ , dΓ) p = refl

-- NatStrNatS : (g : MorS n m) (X : ObS m) (p : X ≡ ∂₁S g) → starS g (NatStrS X) (! (NatStr=S X ∙ p)) ≡ NatStrS (∂₀S g)
-- NatStrNatS = //-elimP (λ g → //-elimP (NatStrNatS-// g))



-- IdStrNatS-// : (g : DMor n m) (A : DCtx (suc m)) (u : DMor m (suc m)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ (proj A))
--                                                  (v : DMor m (suc m)) (vₛ : S.is-section (proj v)) (v₁ : ∂₁S (proj v) ≡ (proj A)) (p : ftS (proj A) ≡ ∂₁S (proj g))
--   → starS (proj g) (IdStrS (proj A) (proj u) uₛ u₁ (proj v) vₛ v₁) (! (IdStr=S (proj A) (proj u) uₛ u₁ (proj v) vₛ v₁ ∙ p))
--     ≡ IdStrS (starS (proj g) (proj A) (! p))
--       (starTmS (proj g) (proj u) (is-section₀S (proj u) uₛ u₁ ∙ p)) (ssₛS (compS (proj u) (proj g) (! (is-section₀S (proj u) uₛ u₁ ∙ p))))
--       (starTm₁S (proj g) (proj u) uₛ (is-section₀S (proj u) uₛ u₁ ∙ p) u₁)
--       (starTmS (proj g) (proj v) (is-section₀S (proj v) vₛ v₁ ∙ p)) (ssₛS (compS (proj v) (proj g) (! (is-section₀S (proj v) vₛ v₁ ∙ p))))
--       (starTm₁S (proj g) (proj v) vₛ (is-section₀S (proj v) vₛ v₁ ∙ p) v₁)
-- IdStrNatS-// (dmor (Δ , dΔ) (Γ' , dΓ') g dg) ((Γ , A) , (dΓ , dA)) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , u) (_ , _)) uₛ u₁ (dmor (_ , _) ((_ , _) , (_ , _)) (_ , v) (_ , _)) vₛ v₁ p =
--   refl

-- IdStrNatS : (g : MorS n m) (A : ObS (suc m)) (u : MorS m (suc m)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ A) (v : MorS m (suc m)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ A) (p : ftS A ≡ ∂₁S g)
--   → starS g (IdStrS A u uₛ u₁ v vₛ v₁) (! (IdStr=S A u uₛ u₁ v vₛ v₁ ∙ p))
--     ≡ IdStrS (starS g A (! p))
--       (starTmS g u (is-section₀S u uₛ u₁ ∙ p)) (ssₛS (compS u g (! (is-section₀S u uₛ u₁ ∙ p))))
--       (starTm₁S g u uₛ (is-section₀S u uₛ u₁ ∙ p) u₁)
--       (starTmS g v (is-section₀S v vₛ v₁ ∙ p)) (ssₛS (compS v g (! (is-section₀S v vₛ v₁ ∙ p))))
--       (starTm₁S g v vₛ (is-section₀S v vₛ v₁ ∙ p) v₁)
-- IdStrNatS = //-elimP (λ g → //-elimP (λ A → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → IdStrNatS-// g A u uₛ u₁ v vₛ v₁))))

-- -- Naturality of term formers

-- uuStr₀S : ∀ {n} i X → _
-- uuStr₀S {n} i X = is-section₀S {n} (uuStrS i X) (uuStrₛS i X) (uuStr₁S i X) ∙ UUStr=S (suc i) X

-- uuStrNatS-// : (i : ℕ) {n m : ℕ} (g : DMor n m) (X : DCtx m) (p : proj X ≡ ∂₁S (proj g)) → starTmS (proj g) (uuStrS i (proj X)) (uuStr₀S i (proj X) ∙ p) ≡ uuStrS i (∂₀S (proj g))
-- uuStrNatS-// i g X p = refl

-- uuStrNatS : (i : ℕ) {n m : ℕ} (g : MorS n m) (X : ObS m) (p : X ≡ ∂₁S g)
--              → starTmS g (uuStrS i X) (uuStr₀S i X ∙ p) ≡ uuStrS i (∂₀S g)
-- uuStrNatS i = //-elimP (λ g → //-elimP (λ X p → uuStrNatS-// i g X p))


-- piStr₀S : ∀ {n} i a aₛ a₁ b bₛ b₁ → _
-- piStr₀S {n} i a aₛ a₁ b bₛ b₁ = is-section₀S {n} (piStrS i a aₛ a₁ b bₛ b₁) (piStrₛS i a aₛ a₁ b bₛ b₁) (piStr₁S i a aₛ a₁ b bₛ b₁) ∙ UUStr=S i (∂₀S a)

-- piStrNatS-// : (i : ℕ) {n m : ℕ} (g : DMor n m) (a : DMor m (suc m)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a)))
--                                                                      (b : DMor (suc m) (suc (suc m))) (bₛ : S.is-section (proj b)) (b₁ : ∂₁S (proj b)≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) (p : ∂₀S (proj a) ≡ ∂₁S (proj g))
--                                                                      (let b₀ = ap ftS (is-section₀S (proj b) bₛ b₁ ∙ (UUStr=S i (ElStrS i (proj a) aₛ a₁))) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)
--              → starTmS (proj g) (piStrS i (proj a) aₛ a₁ (proj b) bₛ b₁) (piStr₀S i (proj a) aₛ a₁ (proj b) bₛ b₁ ∙ p) ≡ piStrS i (starTmS (proj g) (proj a) p) (ssₛS (compS (proj a) (proj g) (! p))) (starTm₁S (proj g) (proj a) aₛ p a₁ ∙ UUStrNatS (proj g) (∂₀S (proj a)) p ∙ ap (UUStrS i) (! (ss₀S (compS (proj a) (proj g) (! p)) ∙ comp₀S (proj a) (proj g) (! p))))
--                                                                            (starTm+S (proj g) (proj b) b₀) (ssₛS (compS (proj b) (qqS (proj g) (∂₀S (proj b)) (! b₀)) (qq₁S (proj g) (∂₀S (proj b)) (! b₀))))
--                                                                            (starTm+₁S (proj g) (proj b) bₛ b₁ b₀ ∙ UUStrNatS (qqS (proj g) (ftS (UUStrS i (ElStrS i (proj a) aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p))) (ElStrS i (proj a) aₛ a₁) (! (qq₁S (proj g) (ftS (UUStrS i (ElStrS i (proj a) aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)) ∙ UUStr=S i (ElStrS i (proj a) aₛ a₁))) ∙ ap (UUStrS i) (qq₀S (proj g) (ftS (UUStrS i (ElStrS i (proj a) aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)) ∙ ap2-irr starS {a = proj g} refl (UUStr=S i (ElStrS i (proj a) aₛ a₁)) {b =  ! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)} {b' = ! (ElStr=S i (proj a) aₛ a₁ ∙ p)} ∙ (ElStrNatS (proj g) (proj a) aₛ a₁ p)))
-- piStrNatS-// i g@(dmor (_ , _) (_ , _) _ _) a@(dmor _ ((_ , _) , (_ , _)) (_ , _) (_ , _)) aₛ a₁ b@(dmor ((_ , _) , (_ , _)) (((_ , _) , _) , ((_ , _) , _)) ((_ , _) , _)  ((_ , _) , _)) bₛ b₁ p = refl

-- piStrNatS : (i : ℕ) {n m : ℕ} (g : MorS n m) (a : MorS m (suc m)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a))
--                                                                    (b : MorS (suc m) (suc (suc m))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁)) (p : ∂₀S a ≡ ∂₁S g)
--                                                                    (let b₀ = ap ftS (is-section₀S b bₛ b₁ ∙ (UUStr=S i (ElStrS i a aₛ a₁))) ∙ ElStr=S i a aₛ a₁ ∙ p)
--              →  starTmS g (piStrS i a aₛ a₁ b bₛ b₁) (piStr₀S i a aₛ a₁ b bₛ b₁ ∙ p) ≡ piStrS i (starTmS g a p) (ssₛS (compS a g (! p))) (starTm₁S g a aₛ p a₁ ∙ UUStrNatS g (∂₀S a) p ∙ ap (UUStrS i) (! (ss₀S (compS a g (! p)) ∙ comp₀S a g (! p))))
--                                                                            (starTm+S g b b₀) (ssₛS (compS b (qqS g (∂₀S b) (! b₀)) (qq₁S g (∂₀S b) (! b₀))))
--                                                                            (starTm+₁S g b bₛ b₁ b₀ ∙ UUStrNatS (qqS g (ftS (UUStrS i (ElStrS i a aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i a aₛ a₁)) ∙ ElStr=S i a aₛ a₁ ∙ p))) (ElStrS i a aₛ a₁) (! (qq₁S g (ftS (UUStrS i (ElStrS i a aₛ a₁))) (! (ap ftS (! (is-section₀S b bₛ b₁))  ∙ b₀)) ∙ UUStr=S i (ElStrS i a aₛ a₁))) ∙ ap (UUStrS i) (qq₀S g (ftS (UUStrS i (ElStrS i a aₛ a₁))) (! (ap ftS (! (is-section₀S b bₛ b₁))  ∙ b₀)) ∙ ap2-irr starS {a = g} refl (UUStr=S i (ElStrS i a aₛ a₁)) {b = ! (ap ftS (! (is-section₀S b bₛ b₁)) ∙ b₀)} {b' = ! (ElStr=S i a aₛ a₁ ∙ p)} ∙ (ElStrNatS g a aₛ a₁ p)))
-- piStrNatS i = //-elimP (λ g → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ p → piStrNatS-// i g a aₛ a₁ b bₛ b₁ p)))



-- lamStr₀S : ∀ {n} B u uₛ u₁ → _
-- lamStr₀S {n} B u uₛ u₁ = is-section₀S {n} (lamStrS B u uₛ u₁) (lamStrₛS B u uₛ u₁) (lamStr₁S B u uₛ u₁) ∙ PiStr=S B

-- -- CtxSubstRefl : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} {A : TyExpr m} → (⊢ Γ) → (Γ ⊢ δ ∷> Δ) → Derivable (Δ ⊢ A) → ⊢ (Γ , A [ δ ]Ty) == (Γ , A [ δ ]Ty)
-- -- CtxSubstRefl dΓ dδ dA = (CtxRefl dΓ ,, TyRefl (SubstTy dA dδ))

-- -- WeakSubstTmEq : {Γ : Ctx n} {Δ : Ctx m} {δ : Mor n m} {A : TyExpr m} {B : TyExpr (suc m)} {u v : TmExpr (suc m)} → (⊢ Γ) → Derivable (Δ ⊢ A) →  Derivable ((Δ , A) ⊢ u == v :> B) → (Γ ⊢ δ ∷> Δ) → Derivable ((Γ , A [ δ ]Ty) ⊢ u [ (weakenMor δ , var last) ]Tm == v [ (weakenMor δ , var last) ]Tm :> B [ (weakenMor δ , var last)  ]Ty)
-- -- WeakSubstTmEq {δ = δ} {A = A} dΓ dA du=v dδ = ConvTmEq (SubstTmEq du=v ((WeakMor (A [ δ ]Ty) dδ) , weakenDerLast dA dδ)) (CtxSubstRefl dΓ dδ dA)


-- up-to-rhsTyEq : {Γ : DCtx n} {A B : TyExpr n}  {δ : Mor n (suc n)} {w₁ : _} {w₂ : _} {w₃ : _} {w₄ : _} (Tyeq : A ≡ B) → proj {R = MorEquiv} (dmor Γ ((ctx Γ , A) , w₁) δ w₂) ≡ proj (dmor Γ ((ctx Γ , B) , w₃) δ w₄)
-- up-to-rhsTyEq {Γ = Γ} {δ = δ} TyEq = ap-irr2 (λ z p q → proj (dmor Γ ((ctx Γ , z) , p) δ q)) TyEq

-- lamStrNatS-// : {n m : ℕ} (g : DMor n m)(B : DCtx (suc (suc m))) (u : DMor (suc m) (suc (suc m))) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))
--               →  starTmS (proj g) (lamStrS (proj B) (proj u) uₛ u₁) (lamStr₀S (proj B) (proj u) uₛ u₁ ∙ p) ≡ lamStrS (star+S (proj g) (proj B) p) (starTm+S (proj g) (proj u) (ap ftS (is-section₀S (proj u) uₛ u₁) ∙ p)) (ssₛS (compS (proj u) (qqS (proj g) (∂₀S (proj u)) (! (ap ftS (is-section₀S (proj u) uₛ u₁) ∙ p))) (qq₁S (proj g) (∂₀S (proj u)) (! (ap ftS (is-section₀S (proj u) uₛ u₁) ∙ p))))) (starTm+₁S (proj g) (proj u) uₛ u₁ (ap ftS (is-section₀S (proj u) uₛ u₁) ∙ p))
-- lamStrNatS-// {n} {m} g@(dmor (Γg , dΓg) (Δg , dΔg) δ dδ) BB@(((Γ , A) , B) , ((dΓ , dA) , dB)) uu@(dmor ((Δu , Au) , (dΔu , dAu)) (((Δ'u , A'u) , Bu) , ((dΔ'u , dA'u) , dBu)) ((idu , lastu), u) (didu , du)) uₛ u₁ p = up-to-rhsTyEq (ap (_[_]Ty _) (idMor[]Mor δ)) 

-- --! (eq ((CtxRefl dΓg , (CtxRefl dΓg ,, congTyEq refl (ap (λ z → pi A B [ z ]Ty) (! (idMor[]Mor δ))) (TyRefl (SubstTy (Pi dA dB) (ConvMor dδ (CtxRefl dΓg) (CtxSymm (reflect p))) )))) , MorRefl (idMor+ dΓg (SubstTm (Lam dA dB (DMor-dTm uu uₛ u₁)) (ConvMor dδ (CtxRefl dΓg) (CtxSymm (reflect p))))))) 
              


-- lamStrNatS : {n m : ℕ} (g : MorS n m) (B : ObS (suc (suc m))) (u : MorS (suc m) (suc (suc m))) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ B) (p : ftS (ftS B) ≡ ∂₁S g)
--            → starTmS g (lamStrS B u uₛ u₁) (lamStr₀S B u uₛ u₁ ∙ p) ≡ lamStrS (star+S g B p) (starTm+S g u (ap ftS (is-section₀S u uₛ u₁) ∙ p)) (ssₛS  (compS u (qqS g (∂₀S u) (! (ap ftS (is-section₀S u uₛ u₁) ∙ p))) (qq₁S g (∂₀S u) (! (ap ftS (is-section₀S u uₛ u₁) ∙ p))))) (starTm+₁S g u uₛ u₁ (ap ftS (is-section₀S u uₛ u₁) ∙ p))
-- lamStrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ u uₛ u₁ → lamStrNatS-// g B u uₛ u₁)))


-- appStrNatS-// : (g : DMor n m) (B : DCtx (suc (suc m))) (f : DMor m (suc m)) (fₛ : S.is-section (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor m (suc m)) (as : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))  → ssS (compS (appStrS (proj B) (proj f) fₛ f₁ (proj a) as a₁) (proj g) (! (appStr₀S (proj B) (proj f) fₛ f₁ (proj a) as a₁ ∙ p))) ≡ appStrS (starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p))) (ssS (compS (proj f) (proj g) (! (is-section₀S {u = proj f} fₛ ∙ ap ftS f₁ ∙ (PiStr=S (proj B)) ∙ p)))) (ssₛS (compS (proj f) (proj g) (! (is-section₀S {u = proj f} fₛ ∙ ap ftS f₁ ∙ (PiStr=S (proj B)) ∙ p)))) (ss-comp-section₁S (proj g) (proj f) fₛ (! (is-section₀S {u = proj f} fₛ ∙ ap ftS f₁ ∙ (PiStr=S (proj B)) ∙ p)) ∙  ap2-irr starS {a = (proj g)} refl f₁ {b = ! (is-section₀S {u = proj f} fₛ ∙ ap ftS f₁ ∙ PiStr=S (proj B) ∙ p) ∙ is-section₀S {u = proj f} fₛ} ∙ (PiStrNatS (proj g) (proj B) p)) (ssS (compS (proj a) (proj g) (! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p)))) (ssₛS (compS (proj a) (proj g) (! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p)))) (ss-comp-section₁S (proj g) (proj a) as (! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p)) ∙ ! (ft-starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p)) ∙ qq₀S (proj g) (ftS (proj B)) (! p) ∙ ap2-irr starS {a = (proj g)} refl (! a₁) {b = ! p} {b' = ! (is-section₀S {u = proj a} as ∙ ap ftS a₁ ∙ p) ∙ is-section₀S {u = proj a} as}))
-- appStrNatS-// gg@(dmor (Δ , dΔ) (Γg , dΓg) δg dδg) (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γf' , piABf) , (dΓf' , dpiABf)) (δf , f) (dδf , df~)) fₛ f₁ aa@(dmor (Γa , dΓa) ((Γa' , Aa) , (dΓa' , dAa)) (δa , a) (dδa , da~)) as a₁ p =
--                             let ((_ , dΓf'=Γf) , dδf=id) = reflect fₛ
--                                 (dΓf'=Γ , _ , _ , dΓf'piABf=piAB , dΓpiABf=piAB) = reflect f₁
--                                 ((_ , dΓa'=Γa) , dδa=id) = reflect as
--                                 (dΓa'=Γ , _ , _ , dΓ'Aa=A , dΓAa=A) = reflect a₁
--                                 dΓ=Γg = reflect p

--                                 dδaΓ : Γa ⊢ δa ∷> Γ
--                                 dδaΓ = ConvMor dδa (CtxRefl dΓa) dΓa'=Γ

--                                 dδa=idΓ : Γa ⊢ δa == idMor _ ∷> Γ
--                                 dδa=idΓ = ConvMorEq (congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor δa) refl dδa=id) (CtxRefl dΓa) dΓa'=Γ
--                                 dδf=idΓf' : Γf' ⊢ δf == idMor _ ∷> Γf'
--                                 dδf=idΓf' = ConvMorEq (congMorEq refl refl (weakenMorInsert _ _ _ ∙ idMor[]Mor δf) refl dδf=id) (CtxSymm dΓf'=Γf) (CtxRefl dΓf')

--                                 da[] : Derivable (Γ ⊢ a :> A [ idMor _ ]Ty)
--                                 da[] = ConvTm2 da~ (CtxTran (CtxSymm dΓa'=Γa) dΓa'=Γ) (SubstTyFullEq dA dδaΓ dΓAa=A dδa=idΓ)

--                                 dδgΓ : Δ ⊢ δg ∷> Γ
--                                 dδgΓ = ConvMor dδg (CtxRefl dΔ) (CtxSymm dΓ=Γg)
--                                 dAΓg : Derivable (Γg ⊢ A)
--                                 dAΓg = ConvTy dA dΓ=Γg
--                                 dBΓg : Derivable ((Γg , A) ⊢ B)
--                                 dBΓg = ConvTy dB (dΓ=Γg ,, (TyRefl dA))
--                                 dfΓg : Derivable (Γg ⊢ f :> pi A B)
--                                 dfΓg = ConvTm2 df~ (CtxTran (CtxSymm dΓf'=Γf) (CtxTran dΓf'=Γ dΓ=Γg)) (ConvTyEq (congTyEq refl ([idMor]Ty (pi A B)) (SubstTyFullEq (Pi (ConvTy dA (CtxSymm dΓf'=Γ)) (ConvTy dB (CtxSymm dΓf'=Γ ,, TyRefl dA))) (ConvMor dδf (CtxSymm dΓf'=Γf) (CtxRefl dΓf')) dΓf'piABf=piAB dδf=idΓf')) dΓf'=Γf)
--                                 daΓg : Derivable (Γg ⊢ a :> A)
--                                 daΓg = ConvTm2 da[] dΓ=Γg (TySymm (congTyRefl dA (! ([idMor]Ty A))))
--                             in
--                             eq ((CtxRefl dΔ , (CtxRefl dΔ ,, congTyRefl (SubstTy (SubstTy dB ((idMorDerivable dΓ) , da[])) (SubstMor (idMorDerivable dΓ) (ConvMor dδg (CtxRefl dΔ) (CtxSymm dΓ=Γg)))) ([]Ty-assoc _ _ B ∙ ! ([]Ty-assoc _ _ B ∙ ap (_[_]Ty B) (ap (λ z → (z , a [ δg ]Tm)) {b = idMor _ [ idMor _ [ δg ]Mor ]Mor} (weakenMorInsert _ _ (a [ δg ]Tm) ∙ [idMor]Mor δg ∙ ! (idMor[]Mor _ ∙ idMor[]Mor δg)) ∙ ap (λ z → (_ , z)) (ap (_[_]Tm a) (! (idMor[]Mor δg)))))))) , ((MorRefl (idMorDerivable dΔ)) , TmRefl (Conv (SubstTy (SubstTy dB ((idMorDerivable dΓ) , da[])) dδgΓ) (SubstTm (App {f = f} {a = a} dAΓg dBΓg dfΓg daΓg) dδg) (congTyRefl (SubstTy (SubstTy dB ((idMorDerivable dΓ) , da[])) dδgΓ) (! ([idMor]Ty _ ∙ ap (_[_]Ty _) (idMor[]Mor δg)))))))


-- appStrNatS : (g : MorS n m) (B : ObS (suc (suc m))) (f : MorS m (suc m)) (fₛ : S.is-section f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS m (suc m)) (as : S.is-section a) (a₁ : ∂₁S a ≡ ftS B) (p : ftS (ftS B) ≡ ∂₁S g)              → ssS (compS (appStrS B f fₛ f₁ a as a₁) g (! (appStr₀S B f fₛ f₁ a as a₁ ∙ p))) ≡ appStrS (starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p))) (ssS (compS f g (! (is-section₀S fₛ ∙ ap ftS f₁ ∙ (PiStr=S B) ∙ p)))) (ssₛS (compS f g (! (is-section₀S fₛ ∙ ap ftS f₁ ∙ (PiStr=S B) ∙ p)))) (ss-comp-section₁S g f fₛ (! (is-section₀S fₛ ∙ ap ftS f₁ ∙ (PiStr=S B) ∙ p)) ∙ ap2-irr starS {a = g} refl f₁  ∙ (PiStrNatS g B p)) (ssS (compS a g (! (is-section₀S as ∙ ap ftS a₁ ∙ p)))) (ssₛS (compS a g (! (is-section₀S as ∙ ap ftS a₁ ∙ p)))) (ss-comp-section₁S g a as (! (is-section₀S as ∙ ap ftS a₁ ∙ p)) ∙ ! (ft-starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p)) ∙ qq₀S g (ftS B) (! p) ∙ ap2-irr starS {a = g} refl (! a₁)))
-- appStrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ f fₛ f₁ → //-elimP (λ a as a₁ → appStrNatS-// g B f fₛ f₁ a as a₁))))


-- appStr₀S : ∀ {n} B f fₛ f₁ a aₛ a₁ → _
-- appStr₀S {n} B f fₛ f₁ a aₛ a₁ = is-section₀S {n} (appStrS B f fₛ f₁ a aₛ a₁) (appStrₛS B f fₛ f₁ a aₛ a₁) (appStr₁S B f fₛ f₁ a aₛ a₁) ∙ ft-starS a B a₁ ∙ is-section₀S a aₛ a₁

-- appStrNatS-// : {n m : ℕ} (g : DMor n m) (B : DCtx (suc (suc m))) (f : DMor m (suc m)) (fₛ : S.is-section (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj B)) (a : DMor m (suc m)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))
--                 (let a₀ = is-section₀S (proj a) aₛ a₁ ∙ p) (let f₀ = is-section₀S (proj f) fₛ f₁ ∙ PiStr=S (proj B) ∙ p)
--              → starTmS (proj g) (appStrS (proj B) (proj f) fₛ f₁ (proj a) aₛ a₁) (appStr₀S (proj B) (proj f) fₛ f₁ (proj a) aₛ a₁ ∙ p)
--                 ≡ appStrS (star+S (proj g) (proj B) p)
--                          (starTmS (proj g) (proj f) f₀) (ssₛS (compS (proj f) (proj g) (! f₀))) (starTm₁S (proj g) (proj f) fₛ f₀ f₁ ∙ PiStrNatS (proj g) (proj B) p)
--                          (starTmS (proj g) (proj a) a₀) (ssₛS (compS (proj a) (proj g) (! a₀))) (starTm₁S (proj g) (proj a) aₛ a₀ a₁ ∙ ! (ft-starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p)) ∙ qq₀S (proj g) (ftS (proj B)) (! p)))
-- appStrNatS-// g@(dmor (Δ , dΔ) (Γg , dΓg) δ dδ) (((Γ , A) , B), ((dΓ , dA) , dB)) ff@(dmor (Γf , dΓf) ((Γ'f , piABf) , (dΓ'f , dpiABf)) (δf , f) (dδf , df~)) fs f₁ aa@(dmor (Γa , dΓa) ((Γ'a , Aa) , (dΓ'a , dAa)) (δa , a) (dδa , da~)) as a₁ p = up-to-rhsTyEq (ap (_[_]Ty _) (idMor[]Mor δ) ∙ ! (substCommutes[]Ty _ _ _))


-- appStrNatS : {n m : ℕ} (g : MorS n m) (B : ObS (suc (suc m))) (f : MorS m (suc m)) (fₛ : S.is-section f) (f₁ : ∂₁S f ≡ PiStrS B) (a : MorS m (suc m)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ ftS B) (p : ftS (ftS B) ≡ ∂₁S g)
--                 (let a₀ = is-section₀S a aₛ a₁ ∙ p) (let f₀ = is-section₀S f fₛ f₁ ∙ PiStr=S B ∙ p)
--              → starTmS g (appStrS B f fₛ f₁ a aₛ a₁) (appStr₀S B f fₛ f₁ a aₛ a₁ ∙ p)
--                 ≡ appStrS (star+S g B p)
--                          (starTmS g f f₀) (ssₛS (compS f g (! f₀))) (starTm₁S g f fₛ f₀ f₁ ∙ PiStrNatS g B p)
--                          (starTmS g a a₀) (ssₛS (compS a g (! a₀))) (starTm₁S g a aₛ a₀ a₁ ∙ ! (ft-starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p)) ∙ qq₀S g (ftS B) (! p)))
-- appStrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ f fₛ f₁ → //-elimP (λ a aₛ a₁ p → appStrNatS-// g B f fₛ f₁ a aₛ a₁ p))))



-- sigStr₀S : ∀ {n} i a aₛ a₁ b bₛ b₁ → _
-- sigStr₀S {n} i a aₛ a₁ b bₛ b₁ = is-section₀S {n} (sigStrS i a aₛ a₁ b bₛ b₁) (sigStrₛS i a aₛ a₁ b bₛ b₁) (sigStr₁S i a aₛ a₁ b bₛ b₁) ∙ UUStr=S i (∂₀S a)

-- sigStrNatS-// : (i : ℕ) {n m : ℕ} (g : DMor n m) (a : DMor m (suc m)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a)))
--                                                                      (b : DMor (suc m) (suc (suc m))) (bₛ : S.is-section (proj b)) (b₁ : ∂₁S (proj b)≡ UUStrS i (ElStrS i (proj a) aₛ a₁)) (p : ∂₀S (proj a) ≡ ∂₁S (proj g))
--                                                                      (let b₀ = ap ftS (is-section₀S (proj b) bₛ b₁ ∙ (UUStr=S i (ElStrS i (proj a) aₛ a₁))) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)
--              → starTmS (proj g) (sigStrS i (proj a) aₛ a₁ (proj b) bₛ b₁) (sigStr₀S i (proj a) aₛ a₁ (proj b) bₛ b₁ ∙ p) ≡ sigStrS i (starTmS (proj g) (proj a) p) (ssₛS (compS (proj a) (proj g) (! p))) (starTm₁S (proj g) (proj a) aₛ p a₁ ∙ UUStrNatS (proj g) (∂₀S (proj a)) p ∙ ap (UUStrS i) (! (ss₀S (compS (proj a) (proj g) (! p)) ∙ comp₀S (proj a) (proj g) (! p))))
--                                                                            (starTm+S (proj g) (proj b) b₀) (ssₛS (compS (proj b) (qqS (proj g) (∂₀S (proj b)) (! b₀)) (qq₁S (proj g) (∂₀S (proj b)) (! b₀))))
--                                                                            (starTm+₁S (proj g) (proj b) bₛ b₁ b₀ ∙ UUStrNatS (qqS (proj g) (ftS (UUStrS i (ElStrS i (proj a) aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p))) (ElStrS i (proj a) aₛ a₁) (! (qq₁S (proj g) (ftS (UUStrS i (ElStrS i (proj a) aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)) ∙ UUStr=S i (ElStrS i (proj a) aₛ a₁))) ∙ ap (UUStrS i) (qq₀S (proj g) (ftS (UUStrS i (ElStrS i (proj a) aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)) ∙ ap2-irr starS {a = proj g} refl (UUStr=S i (ElStrS i (proj a) aₛ a₁)) {b =  ! (ap ftS (UUStr=S i (ElStrS i (proj a) aₛ a₁)) ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)} {b' = ! (ElStr=S i (proj a) aₛ a₁ ∙ p)} ∙ (ElStrNatS (proj g) (proj a) aₛ a₁ p)))
-- sigStrNatS-// i (dmor (_ , _) (_ , _) _ _) (dmor _ ((_ , _) , (_ , _)) (_ , _) (_ , _)) aₛ a₁ (dmor ((_ , _) , (_ , _)) (((_ , _) , _) , ((_ , _) , _)) ((_ , _) , _)  ((_ , _) , _)) bₛ b₁ p = refl

-- sigStrNatS : (i : ℕ) {n m : ℕ} (g : MorS n m) (a : MorS m (suc m)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a))
--                                                                    (b : MorS (suc m) (suc (suc m))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i a aₛ a₁)) (p : ∂₀S a ≡ ∂₁S g)
--                                                                    (let b₀ = ap ftS (is-section₀S b bₛ b₁ ∙ (UUStr=S i (ElStrS i a aₛ a₁))) ∙ ElStr=S i a aₛ a₁ ∙ p)
--              →  starTmS g (sigStrS i a aₛ a₁ b bₛ b₁) (sigStr₀S i a aₛ a₁ b bₛ b₁ ∙ p) ≡ sigStrS i (starTmS g a p) (ssₛS (compS a g (! p))) (starTm₁S g a aₛ p a₁ ∙ UUStrNatS g (∂₀S a) p ∙ ap (UUStrS i) (! (ss₀S (compS a g (! p)) ∙ comp₀S a g (! p))))
--                                                                            (starTm+S g b b₀) (ssₛS (compS b (qqS g (∂₀S b) (! b₀)) (qq₁S g (∂₀S b) (! b₀))))
--                                                                            (starTm+₁S g b bₛ b₁ b₀ ∙ UUStrNatS (qqS g (ftS (UUStrS i (ElStrS i a aₛ a₁))) (! (ap ftS (UUStr=S i (ElStrS i a aₛ a₁)) ∙ ElStr=S i a aₛ a₁ ∙ p))) (ElStrS i a aₛ a₁) (! (qq₁S g (ftS (UUStrS i (ElStrS i a aₛ a₁))) (! (ap ftS (! (is-section₀S b bₛ b₁))  ∙ b₀)) ∙ UUStr=S i (ElStrS i a aₛ a₁))) ∙ ap (UUStrS i) (qq₀S g (ftS (UUStrS i (ElStrS i a aₛ a₁))) (! (ap ftS (! (is-section₀S b bₛ b₁))  ∙ b₀)) ∙ ap2-irr starS {a = g} refl (UUStr=S i (ElStrS i a aₛ a₁)) {b = ! (ap ftS (! (is-section₀S b bₛ b₁)) ∙ b₀)} {b' = ! (ElStr=S i a aₛ a₁ ∙ p)} ∙ (ElStrNatS g a aₛ a₁ p)))
-- sigStrNatS i = //-elimP (λ g → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ p → sigStrNatS-// i g a aₛ a₁ b bₛ b₁ p)))


-- pairStr₀S : ∀ {n} B a aₛ a₁ b bₛ b₁ → _
-- pairStr₀S {n} B a aₛ a₁ b bₛ b₁ = is-section₀S {n} (pairStrS B a aₛ a₁ b bₛ b₁) (pairStrₛS B a aₛ a₁ b bₛ b₁) (pairStr₁S B a aₛ a₁ b bₛ b₁) ∙ SigStr=S B

-- pairStrNatS-// : {n m : ℕ} (g : DMor n m) (B : DCtx (suc (suc m))) (a : DMor m (suc m)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ ftS (proj B)) (b : DMor m (suc m)) (bₛ : S.is-section (proj b)) (b₁ : ∂₁S (proj b) ≡ starS (proj a) (proj B) a₁) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))
--                  (let a₀ = is-section₀S (proj a) aₛ a₁ ∙ p) (let b₀ = is-section₀S (proj b) bₛ b₁ ∙ ft-starS (proj a) (proj B) a₁ ∙ a₀)
--              → starTmS (proj g) (pairStrS (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁) (pairStr₀S (proj B) (proj a) aₛ a₁ (proj b) bₛ b₁ ∙ p) ≡ pairStrS (star+S (proj g) (proj B) p) (starTmS (proj g) (proj a) a₀) (ssₛS (compS (proj a) (proj g) (! a₀))) (starTm₁S (proj g) (proj a) aₛ a₀ a₁ ∙ ! (ft-starS (qqS (proj g) (ftS (proj B)) (! p)) (proj B) (qq₁S (proj g) (ftS (proj B)) (! p)) ∙ qq₀S (proj g) (ftS (proj B)) (! p))) (starTmS (proj g) (proj b) b₀) (ssₛS (compS (proj b) (proj g) (! b₀))) (starTm₁S (proj g) (proj b) bₛ b₀ b₁ ∙ starstar synCCat {g = proj g} {a = proj a} aₛ {B = proj B} {a₁ = a₁} {g₁ = ! (ft-starS (proj a) (proj B) a₁ ∙ a₀)} a₀ p {B' = ftS (proj B)} refl)
-- pairStrNatS-// (dmor (_ , _) (_ , _) δ _) (((_ , _) , _), ((_ , _) , _)) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) aₛ a₁ (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) bₛ b₁ p = up-to-rhsTyEq (ap (_[_]Ty _) (idMor[]Mor δ))

-- pairStrNatS : {n m : ℕ} (g : MorS n m) (B : ObS (suc (suc m))) (a : MorS m (suc m)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ ftS B) (b : MorS m (suc m)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ starS a B a₁) (p : ftS (ftS B) ≡ ∂₁S g)
--                  (let a₀ = is-section₀S a aₛ a₁ ∙ p) (let b₀ = is-section₀S b bₛ b₁ ∙ ft-starS a B a₁ ∙ a₀)
--              → starTmS g (pairStrS B a aₛ a₁ b bₛ b₁) (pairStr₀S B a aₛ a₁ b bₛ b₁ ∙ p) ≡ pairStrS (star+S g B p) (starTmS g a a₀) (ssₛS (compS a g (! a₀))) (starTm₁S g a aₛ a₀ a₁ ∙ ! (ft-starS (qqS g (ftS B) (! p)) B (qq₁S g (ftS B) (! p)) ∙ qq₀S g (ftS B) (! p))) (starTmS g b b₀) (ssₛS (compS b g (! b₀))) (starTm₁S g b bₛ b₀ b₁ ∙ starstar synCCat {g = g} {a = a} aₛ {B = B} {a₁ = a₁} {g₁ = ! (ft-starS a B a₁ ∙ a₀)} a₀ p {B' = ftS B} refl)
-- pairStrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ p → pairStrNatS-// g B a aₛ a₁ b bₛ b₁ p))))

-- pr1Str₀S : ∀ {n} B u uₛ u₁ → _
-- pr1Str₀S {n} B u uₛ u₁ = is-section₀S {n} (pr1StrS B u uₛ u₁) (pr1StrₛS B u uₛ u₁) (pr1Str₁S B u uₛ u₁)

-- pr1StrNatS-// : {n m : ℕ} (g : DMor n m) (B : DCtx (suc (suc m))) (u : DMor m (suc m)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))
--                 (let u₀ = is-section₀S (proj u) uₛ u₁ ∙ SigStr=S (proj B) ∙ p)
--              → starTmS (proj g) (pr1StrS (proj B) (proj u) uₛ u₁) (pr1Str₀S (proj B) (proj u) uₛ u₁ ∙ p) ≡ pr1StrS (star+S (proj g) (proj B) p) (starTmS (proj g) (proj u) u₀) (ssₛS (compS (proj u) (proj g) (! u₀))) (starTm₁S (proj g) (proj u) uₛ u₀ u₁ ∙ SigStrNatS (proj g) (proj B) p)
-- pr1StrNatS-// (dmor (_ , _) (_ , _) δ _) (((_ , _) , _), ((_ , _) , _)) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) uₛ u₁ p = up-to-rhsTyEq (ap (_[_]Ty _) (idMor[]Mor δ))


-- pr1StrNatS : {n m : ℕ} (g : MorS n m) (B : ObS (suc (suc m))) (u : MorS m (suc m)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS B) (p : ftS (ftS B) ≡ ∂₁S g)
--                 (let u₀ = is-section₀S u uₛ u₁ ∙ SigStr=S B ∙ p)
--              → starTmS g (pr1StrS B u uₛ u₁) (pr1Str₀S B u uₛ u₁ ∙ p) ≡ pr1StrS (star+S g B p) (starTmS g u u₀) (ssₛS (compS u g (! u₀))) (starTm₁S g u uₛ u₀ u₁ ∙ SigStrNatS g B p)
-- pr1StrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ u uₛ u₁ p → pr1StrNatS-// g B u uₛ u₁ p)))



-- pr2Str₀S : ∀ {n} B u uₛ u₁ → _
-- pr2Str₀S {n} B u uₛ u₁ = is-section₀S {n} (pr2StrS B u uₛ u₁) (pr2StrₛS B u uₛ u₁) (pr2Str₁S B u uₛ u₁) ∙ ft-starS (pr1StrS B u uₛ u₁) B (pr1Str₁S B u uₛ u₁) ∙ pr1Str₀S B u uₛ u₁

-- pr2StrNatS-// : {n m : ℕ} (g : DMor n m) (B : DCtx (suc (suc m))) (u : DMor m (suc m)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj B)) (p : ftS (ftS (proj B)) ≡ ∂₁S (proj g))
--                 (let u₀ = is-section₀S (proj u) uₛ u₁ ∙ SigStr=S (proj B) ∙ p)
--              → starTmS (proj g) (pr2StrS (proj B) (proj u) uₛ u₁) (pr2Str₀S (proj B) (proj u) uₛ u₁ ∙ p) ≡ pr2StrS (star+S (proj g) (proj B) p) (starTmS (proj g) (proj u) u₀) (ssₛS (compS (proj u) (proj g) (! u₀))) (starTm₁S (proj g) (proj u) uₛ u₀ u₁ ∙ SigStrNatS (proj g) (proj B) p)
-- pr2StrNatS-// (dmor (_ , _) (_ , _) δ _) (((_ , A) , B), ((_ , _) , _)) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , u) (_ , _)) uₛ u₁ p = up-to-rhsTyEq ((ap (_[_]Ty _) (idMor[]Mor δ) ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty _) (ap (λ z → (z , (pr1 A B u) [ δ ]Tm)) (idMor[]Mor δ))) ∙ ! ([]Ty-assoc _ _ _ ∙ (ap (_[_]Ty _) (ap (λ z → (z  , (pr1 A B u) [ δ ]Tm)) (weakenMorInsert _ _ _ ∙ [idMor]Mor δ)))))


-- pr2StrNatS : {n m : ℕ} (g : MorS n m) (B : ObS (suc (suc m))) (u : MorS m (suc m)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS B) (p : ftS (ftS B) ≡ ∂₁S g)
--                 (let u₀ = is-section₀S u uₛ u₁ ∙ SigStr=S B ∙ p)
--              → starTmS g (pr2StrS B u uₛ u₁) (pr2Str₀S B u uₛ u₁ ∙ p) ≡ pr2StrS (star+S g B p) (starTmS g u u₀) (ssₛS (compS u g (! u₀))) (starTm₁S g u uₛ u₀ u₁ ∙ SigStrNatS g B p)
-- pr2StrNatS = //-elimP (λ g → //-elimP (λ B → //-elimP (λ u uₛ u₁ p → pr2StrNatS-// g B u uₛ u₁ p)))


-- natStr₀S : ∀ {n} i X → _
-- natStr₀S {n} i X = is-section₀S {n} (natStrS i X) (natStrₛS i X) (natStr₁S i X) ∙ UUStr=S i X

-- natStrNatS-// : (i : ℕ) {n m : ℕ} (g : DMor n m) (X : DCtx m) (p : proj X ≡ ∂₁S (proj g))
--              → starTmS (proj g) (natStrS i (proj X)) (natStr₀S i (proj X) ∙ p) ≡ natStrS i (∂₀S (proj g))
-- natStrNatS-// i (dmor (_ , _) (_ , _) _ _) (_ , _) p = refl

-- natStrNatS : (i : ℕ) {n m : ℕ} (g : MorS n m) (X : ObS m) (p : X ≡ ∂₁S g)
--              → starTmS g (natStrS i X) (natStr₀S i X ∙ p) ≡ natStrS i (∂₀S g)
-- natStrNatS i = //-elimP (λ g → //-elimP (λ X p → natStrNatS-// i g X p))


-- zeroStr₀S : ∀ {n} X → _
-- zeroStr₀S {n} X = is-section₀S {n} (zeroStrS X) (zeroStrₛS X) (zeroStr₁S X) ∙ NatStr=S X

-- zeroStrNatS-// : {n m : ℕ} (g : DMor n m) (X : DCtx m) (p : proj X ≡ ∂₁S (proj g))
--              → starTmS (proj g) (zeroStrS (proj X)) (zeroStr₀S (proj X) ∙ p) ≡ zeroStrS (∂₀S (proj g))
-- zeroStrNatS-// (dmor (_ , _) (_ , _) _ _) (_ , _) p = refl

-- zeroStrNatS : {n m : ℕ} (g : MorS n m) (X : ObS m) (p : X ≡ ∂₁S g)
--              → starTmS g (zeroStrS X) (zeroStr₀S X ∙ p) ≡ zeroStrS (∂₀S g)
-- zeroStrNatS = //-elimP (λ g → //-elimP (λ X p → zeroStrNatS-// g X p))


-- sucStr₀S : ∀ {n} u uₛ u₁ → _
-- sucStr₀S {n} u uₛ u₁ = is-section₀S {n} (sucStrS u uₛ u₁) (sucStrₛS u uₛ u₁) (sucStr₁S u uₛ u₁) ∙ NatStr=S (∂₀S u)

-- sucStrNatS-// : {n m : ℕ} (g : DMor n m) (u : DMor m (suc m)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (∂₀S (proj u))) (p : ∂₀S (proj u) ≡ ∂₁S (proj g))
--              → starTmS (proj g) (sucStrS (proj u) uₛ u₁) (sucStr₀S (proj u) uₛ u₁ ∙ p) ≡ sucStrS (starTmS (proj g) (proj u) p) (ssₛS (compS (proj u) (proj g) (! p))) (starTm₁S (proj g) (proj u) uₛ p u₁ ∙ NatStrNatS (proj g) (∂₀S (proj u)) p ∙ ap NatStrS (! (ss₀S (compS (proj u) (proj g) (! p)) ∙ comp₀S (proj u) (proj g) (! p))))
-- sucStrNatS-// (dmor (_ , _) (_ , _) _ _) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) uₛ u₁ p = refl


-- sucStrNatS : {n m : ℕ} (g : MorS n m) (u : MorS m (suc m)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS (∂₀S u)) (p : ∂₀S u ≡ ∂₁S g)
--              → starTmS g (sucStrS u uₛ u₁) (sucStr₀S u uₛ u₁ ∙ p) ≡ sucStrS (starTmS g u p) (ssₛS (compS u g (! p))) (starTm₁S g u uₛ p u₁ ∙ NatStrNatS g (∂₀S u) p ∙ ap NatStrS (! (ss₀S (compS u g (! p)) ∙ comp₀S u g (! p))))
-- sucStrNatS = //-elimP (λ g → //-elimP (λ u uₛ u₁ p → sucStrNatS-// g u uₛ u₁ p))



-- NatStrSynCCat : CCatwithNat synCCat

-- CCatwithNat.NatStr NatStrSynCCat = NatStrS
-- CCatwithNat.NatStr= NatStrSynCCat = NatStr=S _
-- CCatwithNat.NatStrNat NatStrSynCCat g {X = X} p = NatStrNatS g X p


-- zeroStrSynCCat : CCatwithzero synCCat NatStrSynCCat

-- CCatwithzero.zeroStr zeroStrSynCCat = zeroStrS
-- CCatwithzero.zeroStrₛ zeroStrSynCCat {X = X} = zeroStrₛS X
-- CCatwithzero.zeroStr₁ zeroStrSynCCat {X = X} = zeroStr₁S X
-- CCatwithzero.zeroStrNat zeroStrSynCCat g {X = X} p = zeroStrNatS g X p

-- sucStrSynCCat : CCatwithsuc synCCat NatStrSynCCat

-- CCatwithsuc.sucStr sucStrSynCCat = sucStrS
-- CCatwithsuc.sucStrₛ sucStrSynCCat {u = u} = sucStrₛS u _ _
-- CCatwithsuc.sucStr₁ sucStrSynCCat {u = u} = sucStr₁S u _ _
-- CCatwithsuc.sucStrNat sucStrSynCCat g {u = u} p = sucStrNatS g u _ _ p

-- open CCatwithnatelim
-- natelimStrSynCCat : CCatwithnatelim synCCat NatStrSynCCat zeroStrSynCCat sucStrSynCCat



-- natelimStrS-// : (X : DCtx n) (P : DCtx (suc (suc n))) (P= : ftS (proj P) ≡ NatStrS (proj X)) (dO : DMor n (suc n)) (dOₛ : S.is-section (proj dO)) (dO₁ : ∂₁S (proj dO) ≡ starS (zeroStrS (proj X)) (proj P) (zeroStr₁S (proj X) ∙ ! P=)) (dS : DMor (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section (proj dS))
--                    (dS₁ : T-dS₁ natelimStrSynCCat (proj X) (proj P) P= (proj dS))
--                         (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ ftS (proj P)) → DMor n (suc n)
-- natelimStrS-// (Γ , dΓ) (((ΓP , natP) , P) , ((dΓP , dnatP) , dP)) P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁ =
--          let (dΓP=Γ , _ , _ , ΓPdnatP=nat , _) = reflect P= in
--          dmor (Γ , dΓ) ((Γ , substTy P (getTm u)) , (dΓ , ConvTy (SubstTy dP (idMor+ dΓP (DMor-dTm u uₛ u₁))) dΓP=Γ)) (idMor _ , natelim P (getTm dO) (getTm dS) (getTm u)) (idMor+ dΓ (Natelim (ConvTy dP (dΓP=Γ ,, ΓPdnatP=nat))  (DMor-dTm dO dOₛ dO₁) (ConvTm (congTmTy ([]Ty-assoc _ _ _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty P)  (Mor+= (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _) refl) ∙ ! (ap weakenTy (weakenTyInsert' (prev last) P (weakenMor (idMor _) , suc (var last)) (var last)) ∙ weaken[]Ty P (weakenMor (idMor _) , suc (var last)) last)) (DMor-dTm dS dSₛ dS₁)) ((dΓP=Γ ,, ΓPdnatP=nat) ,, TyRefl dP))  (ConvTm (Conv dnatP (DMor-dTm u uₛ u₁) ΓPdnatP=nat) dΓP=Γ)))


-- natelimStrS-eq : (X X' : DCtx n) (rX : X ≃ X') (P P' : DCtx (suc (suc n))) (rP : P ≃ P') (P= : ftS (proj P) ≡ NatStrS (proj X)) (P'= : ftS (proj P') ≡ NatStrS (proj X'))(dO dO' : DMor n (suc n)) (rdO : dO ≃ dO') (dOₛ : S.is-section (proj dO)) (dO'ₛ : S.is-section (proj dO')) (dO₁ : ∂₁S (proj dO) ≡ starS (zeroStrS (proj X)) (proj P) (zeroStr₁S (proj X) ∙ ! P=)) (dO'₁ : ∂₁S (proj dO') ≡ starS (zeroStrS (proj X')) (proj P') (zeroStr₁S (proj X') ∙ ! P'=))
--                    (dS dS' : DMor (suc (suc n)) (suc (suc (suc n)))) (rdS : dS ≃ dS') (dSₛ : S.is-section (proj dS))(dS'ₛ : S.is-section (proj dS'))
--                    (dS₁ : T-dS₁ natelimStrSynCCat (proj X) (proj P) P= (proj dS))
--                    (dS'₁ : T-dS₁ natelimStrSynCCat (proj X') (proj P') P'= (proj dS'))
--                    (u u' : DMor n (suc n)) (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : ∂₁S (proj u) ≡ ftS (proj P)) (u'₁ : ∂₁S (proj u') ≡ ftS (proj P')) → proj {R = MorEquiv} (natelimStrS-// X P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) ≡ proj (natelimStrS-// X' P' P'= dO' dO'ₛ dO'₁ dS' dS'ₛ dS'₁ u' u'ₛ u'₁)
-- natelimStrS-eq (Γ , dΓ) (Γ' , dΓ') dΓ=Γ' (((ΓP , natP) , P) , ((dΓP , dnatP) , dP)) (((ΓP' , natP') , P') , ((dΓP' , dnatP') , dP')) ((dΓP=ΓP' , _ , _ , ΓPdnatP=natP' , _) , _ , _ , ΓPnatPdP=P' , _) P= P'= dO dO' rdO dOₛ dO'ₛ dO₁ dO'₁ dS dS' rdS dSₛ dS'ₛ dS₁ dS'₁ u u' ru uₛ u'ₛ u₁ u'₁ =
--                let (dΓP=Γ , _ , _ , ΓPdnatP=nat , _) = reflect P= in                 
--                eq ((dΓ=Γ' , (dΓ=Γ' ,, SubstTyMorEq2 {Δ = (Γ , nat)} dΓ (dΓ , Nat) (ConvTyEq ΓPnatPdP=P' (dΓP=Γ ,, ΓPdnatP=nat)) (idMor+= dΓ (ConvTmEq (ConvEq dnatP (DMor-dTm= (dΓP=ΓP' ,, ΓPdnatP=natP') u u' ru uₛ u'ₛ u₁ u'₁) ΓPdnatP=nat) dΓP=Γ)))) , idMor+= dΓ (NatelimCong (ConvTy dP (dΓP=Γ ,, ΓPdnatP=nat)) (ConvTyEq ΓPnatPdP=P' (dΓP=Γ ,, ΓPdnatP=nat)) (DMor-dTm= (dΓ=Γ' ,, SubstTyEq (ConvTyEq ΓPnatPdP=P' (dΓP=Γ ,, ΓPdnatP=nat)) (idMor+ dΓ Zero)) dO dO' rdO dOₛ dO'ₛ dO₁ dO'₁) (ConvTmEq (congTmEqTy ([]Ty-assoc _ _ _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty P)  (Mor+= (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _) refl) ∙ ! (ap weakenTy (weakenTyInsert' (prev last) P (weakenMor (idMor _) , suc (var last)) (var last)) ∙ weaken[]Ty P (weakenMor (idMor _) , suc (var last)) last)) (DMor-dTm= (((dΓP=ΓP' ,, ΓPdnatP=natP') ,, ΓPnatPdP=P') ,, SubstTyEq (SubstTyEq (SubstTyEq ΓPnatPdP=P' (WeakMor+ dnatP (WeakMor _ (idMorDerivable dΓP)))) (idMor+ (dΓP , dnatP) (ConvTm (Conv Nat (Suc (VarLast Nat)) (congTyEq refl (ap weakenTy (! ([idMor]Ty _)) ∙ weaken[]Ty _ _ _) (WeakTyEq _ (TySymm ΓPdnatP=nat)))) (CtxRefl dΓP ,, TySymm ΓPdnatP=nat)))) ((WeakMor _ (WeakMor _ (idMorDerivable dΓP))) , (congTmTy (ap weakenTy (ap weakenTy (! ([idMor]Ty _)) ∙ weaken[]Ty _ _ _) ∙ weaken[]Ty _ _ _) (VarPrev (WeakTy _ dnatP) (VarLast dnatP))))) dS dS' rdS dSₛ dS'ₛ dS₁ dS'₁)) ((dΓP=Γ ,, ΓPdnatP=nat) ,, TyRefl dP)) (ConvTmEq (ConvEq dnatP (DMor-dTm= (dΓP=ΓP' ,, ΓPdnatP=natP') u u' ru uₛ u'ₛ u₁ u'₁) ΓPdnatP=nat) dΓP=Γ)))



-- natelimStrS : (X : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS X) (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : ∂₁S dO ≡ starS (zeroStrS X) P (zeroStr₁S X ∙ ! P=))
--                    (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS)
--                    (dS₁ : T-dS₁ natelimStrSynCCat X P P= dS)                
--                    (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ftS P) → MorS n (suc n)
-- natelimStrS = let thing1 : (X : DCtx n) (P : DCtx (suc (suc n))) (P= : ftS (proj P) ≡ NatStrS (proj X)) (dO : DMor n (suc n)) (dOₛ : S.is-section (proj dO)) (dO₁ : ∂₁S (proj dO) ≡ starS (zeroStrS (proj X)) (proj P) (zeroStr₁S (proj X) ∙ ! P=))
--                    (dS : DMor (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section (proj dS))
--                    (dS₁ : T-dS₁ natelimStrSynCCat (proj X) (proj P) P= (proj dS)) {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) → PathOver (λ z → ∂₁S z ≡ ftS (proj P) → MorS n (suc n)) (eqR {a = u} {b = u'} ru) (λ u₁ → proj (natelimStrS-// X P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)) (λ u'₁ → proj (natelimStrS-// X P P= dO dOₛ dO₁ dS dSₛ dS₁ u' u'ₛ u'₁))
--                   thing1 X P P= dO dOₛ dO₁ dS dSₛ dS₁ {u} {u'} ru uₛ u'ₛ = PathOver-Prop→Cst (λ u₁ u'₁ → natelimStrS-eq X X (ref X) P P (ref P) P= P= dO dO (ref dO) dOₛ dOₛ dO₁ dO₁ dS dS (ref dS) dSₛ dSₛ dS₁ dS₁ u u' ru uₛ u'ₛ u₁ u'₁)
--                   thing2 : (X : DCtx n) (P : DCtx (suc (suc n))) (P= : ftS (proj P) ≡ NatStrS (proj X)) (dO : DMor n (suc n)) (dOₛ : S.is-section (proj dO)) (dO₁ : ∂₁S (proj dO) ≡ starS (zeroStrS (proj X)) (proj P) (zeroStr₁S (proj X) ∙ ! P=)) {dS dS' : DMor (suc (suc n)) (suc (suc (suc n)))} (rdS : dS ≃ dS') (dSₛ : S.is-section (proj dS)) (dS'ₛ : S.is-section (proj dS')) → PathOver (λ z → T-dS₁ natelimStrSynCCat (proj X) (proj P) P= z → (u : MorS n (suc n)) → S.is-section u → ∂₁S u ≡ ftS (proj P) → MorS n (suc n)) (eqR {a = dS} {b = dS'} rdS) (λ dS₁ → //-elim-PiP2 (λ u uₛ u₁ → proj (natelimStrS-// X P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)) (thing1 X P P= dO dOₛ dO₁ dS dSₛ dS₁)) (λ dS'₁ → //-elim-PiP2 (λ u uₛ u₁ →  proj (natelimStrS-// X P P= dO dOₛ dO₁ dS' dS'ₛ dS'₁ u uₛ u₁)) (thing1 X P P= dO dOₛ dO₁ dS' dS'ₛ dS'₁))
--                   thing2 X P P= dO dOₛ dO₁ {dS} {dS'} rdS dSₛ dS'ₛ = PathOver-Prop→Cst (λ dS₁ dS'₁ → funext (//-elimP (λ u → funextP (λ uₛ → funextP (λ u₁ → natelimStrS-eq X X (ref X) P P (ref P) P= P= dO dO (ref dO) dOₛ dOₛ dO₁ dO₁ dS dS' rdS dSₛ dS'ₛ dS₁ dS'₁ u u (ref u) uₛ uₛ u₁ u₁)))))
--                   thing3 : (X : DCtx n) (P : DCtx (suc (suc n))) (P= : ftS (proj P) ≡ NatStrS (proj X)) {dO dO' : DMor n (suc n)} (rdO : dO ≃ dO') (dOₛ : S.is-section (proj dO)) (dO'ₛ : S.is-section (proj dO')) → PathOver (λ z → ∂₁S z ≡ starS (zeroStrS (proj X)) (proj P) (zeroStr₁S (proj X) ∙ ! P=) → (dS : MorS (suc (suc n)) (suc (suc (suc n)))) → S.is-section dS → T-dS₁ natelimStrSynCCat (proj X) (proj P) P= dS → (u : MorS n (suc n)) → S.is-section u → ∂₁S u ≡ ftS (proj P) → MorS n (suc n)) (eqR {a = dO} {b = dO'} rdO) (λ dO₁ → //-elim-PiP2 (λ dS dSₛ dS₁ → //-elim-PiP2 (λ u uₛ u₁ → proj (natelimStrS-// X P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)) (thing1 X P P= dO dOₛ dO₁ dS dSₛ dS₁)) (thing2 X P P= dO dOₛ dO₁)) (λ dO'₁ → //-elim-PiP2 (λ dS dSₛ dS₁ → //-elim-PiP2 (λ u uₛ u₁ → proj (natelimStrS-// X P P= dO' dO'ₛ dO'₁ dS dSₛ dS₁ u uₛ u₁)) (thing1 X P P= dO' dO'ₛ dO'₁ dS dSₛ dS₁)) (thing2 X P P= dO' dO'ₛ dO'₁))
--                   thing3 X P P= {dO} {dO'} rdO dOₛ dO'ₛ = PathOver-Prop→Cst (λ dO₁ dO'₁ → funext (//-elimP (λ dS → funextP (λ dSₛ → funextP (λ dS₁ → funext (//-elimP (λ u → funextP (λ uₛ → funextP (λ u₁ → natelimStrS-eq X X (ref X) P P (ref P) P= P= dO dO' rdO dOₛ dO'ₛ dO₁ dO'₁ dS dS (ref dS) dSₛ dSₛ dS₁ dS₁ u u (ref u) uₛ uₛ u₁ u₁)))))))))
--                   thing4 : (X : DCtx n) {P P' : DCtx (suc (suc n))} (rP : P ≃ P') (P= : ftS (proj P) ≡ NatStrS (proj X)) (P'= : ftS (proj P') ≡ NatStrS (proj X)) → PathOver (uncurrify (λ x z → (dO : MorS n (suc n)) → S.is-section dO → ∂₁S dO ≡ starS (zeroStrS (proj X)) x (zeroStr₁S (proj X) ∙ ! z) → (dS : MorS (suc (suc n)) (suc (suc (suc n)))) → S.is-section dS → T-dS₁ natelimStrSynCCat (proj X) x z dS → (u : MorS n (suc n)) → S.is-section u → ∂₁S u ≡ ftS x → MorS n (suc n))) (Σ= {b = P=} {b' = P'=} (eqR {a = P} {b = P'} rP)) (//-elim-PiP2 (λ dO dOₛ dO₁ → //-elim-PiP2 (λ dS dSₛ dS₁ → //-elim-PiP2 (λ u uₛ u₁ → proj (natelimStrS-// X P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)) (thing1 X P P= dO dOₛ dO₁ dS dSₛ dS₁)) (thing2 X P P= dO dOₛ dO₁)) (thing3 X P P=)) (//-elim-PiP2 (λ dO dOₛ dO₁ → //-elim-PiP2 (λ dS dSₛ dS₁ → //-elim-PiP2 (λ u uₛ u₁ → proj (natelimStrS-// X P' P'= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)) (thing1 X P' P'= dO dOₛ dO₁ dS dSₛ dS₁)) (thing2 X P' P'= dO dOₛ dO₁)) (thing3 X P' P'=))
--                   thing4 X {P} {P'} rP P= P'= = PathOver-CstPi (//-elimP (λ dO → PathOver-CstPropPi (λ dOₛ → PathOver-Prop→ (λ dO₁ dO₁' → PathOver-CstPi (//-elimP (λ dS → PathOver-CstPropPi (λ dSₛ → PathOver-Prop→ (λ dS₁ dS₁' → PathOver-CstPi (//-elimP (λ u → PathOver-CstPropPi (λ uₛ → PathOver-Prop→Cst (λ u₁ u₁' → natelimStrS-eq X X (ref X) P P' rP P= P'= dO dO (ref dO) dOₛ dOₛ dO₁ dO₁' dS dS (ref dS) dSₛ dSₛ dS₁ dS₁' u u (ref u) uₛ uₛ u₁ u₁'))))))))))))
--                   thing5 : {X X' : DCtx n} (rX : X ≃ X') (P : ObS (suc (suc n))) → PathOver (λ x → (P= : ftS P ≡ NatStrS x) (dO : MorS n (suc n)) → S.is-section dO → ∂₁S dO ≡ starS (zeroStrS x) P (zeroStr₁S x ∙ ! P=) → (dS : MorS (suc (suc n)) (suc (suc (suc n)))) → S.is-section dS → T-dS₁ natelimStrSynCCat x P P= dS → (u : MorS n (suc n)) → S.is-section u → ∂₁S u ≡ ftS P → MorS n (suc n)) (eqR {a = X} {b = X'} rX) (//-elim-PiP3 (λ P P= → //-elim-PiP2 (λ dO dOₛ dO₁ → //-elim-PiP2 (λ dS dSₛ dS₁ → //-elim-PiP2 (λ u uₛ u₁ → proj (natelimStrS-// X P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)) (thing1 X P P= dO dOₛ dO₁ dS dSₛ dS₁)) (thing2 X P P= dO dOₛ dO₁)) (thing3 X P P=)) (thing4 X) P) (//-elim-PiP3 (λ P P= → //-elim-PiP2 (λ dO dOₛ dO₁ → //-elim-PiP2 (λ dS dSₛ dS₁ → //-elim-PiP2 (λ u uₛ u₁ → proj (natelimStrS-// X' P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)) (thing1 X' P P= dO dOₛ dO₁ dS dSₛ dS₁)) (thing2 X' P P= dO dOₛ dO₁)) (thing3 X' P P=)) (thing4 X') P)
--                   thing5 {X} {X'} rX = //-elimP (λ P → PathOver-PropPi (λ P= P=' → PathOver-CstPi (//-elimP (λ dO → PathOver-CstPropPi (λ dOₛ → PathOver-Prop→ (λ dO₁ dO₁' → PathOver-CstPi (//-elimP (λ dS → PathOver-CstPropPi (λ dSₛ → PathOver-Prop→ (λ dS₁ dS₁' → PathOver-CstPi (//-elimP (λ u → PathOver-CstPropPi (λ uₛ → PathOver-Prop→Cst (λ u₁ u₁' → natelimStrS-eq X X' rX P P (ref P) P= P=' dO dO (ref dO) dOₛ dOₛ dO₁ dO₁' dS dS (ref dS) dSₛ dSₛ dS₁ dS₁' u u (ref u) uₛ uₛ u₁' u₁'))))))))))))))
--                   in
--               //-elim-PiS (λ X → //-elim-PiP3 (λ P P= → //-elim-PiP2 (λ dO dOₛ dO₁ → //-elim-PiP2 (λ dS dSₛ dS₁ → //-elim-PiP2 (λ u uₛ u₁ → proj (natelimStrS-// X P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁))
--                           (thing1 X P P= dO dOₛ dO₁ dS dSₛ dS₁))
--                           (thing2 X P P= dO dOₛ dO₁))
--                           (thing3 X P P=))
--                           (thing4 X))
--                           {!thing5!}


-- idStr₀S : ∀ {n} i a aₛ a₁ u uₛ u₁ v vₛ v₁ → _
-- idStr₀S {n} i a aₛ a₁ u uₛ u₁ v vₛ v₁ = is-section₀S {n} (idStrS i a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStrₛS i a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStr₁S i a aₛ a₁ u uₛ u₁ v vₛ v₁) ∙ UUStr=S i (∂₀S a)

-- idStrNatS-// : (i : ℕ) {n m : ℕ} (g : DMor n m) (a : DMor m (suc m)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (∂₀S (proj a))) (u : DMor m (suc m)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj a) aₛ a₁)
--                                                 (v : DMor m (suc m)) (vₛ : S.is-section (proj v)) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj a) aₛ a₁) (p : ∂₀S (proj a) ≡ ∂₁S (proj g))
--                                                 (let u₀ = is-section₀S (proj u) uₛ u₁ ∙ ElStr=S i (proj a) aₛ a₁ ∙ p) (let v₀ = is-section₀S (proj v) vₛ v₁ ∙ ElStr=S i (proj a) aₛ a₁ ∙ p)
--              → starTmS (proj g) (idStrS i (proj a) aₛ a₁ (proj u) uₛ u₁ (proj v) vₛ v₁) (idStr₀S i (proj a) aₛ a₁ (proj u) uₛ u₁ (proj v) vₛ v₁ ∙ p) ≡ idStrS i (starTmS (proj g) (proj a) p) (ssₛS (compS (proj a) (proj g) (! p))) (starTm₁S (proj g) (proj a) aₛ p a₁ ∙ UUStrNatS (proj g) (∂₀S (proj a)) p ∙ ap (UUStrS i) (! (ss₀S (compS (proj a) (proj g) (! p)) ∙ comp₀S (proj a) (proj g) (! p))))
--                                                                                    (starTmS (proj g) (proj u) u₀) (ssₛS (compS (proj u) (proj g) (! u₀))) (starTm₁S (proj g) (proj u) uₛ u₀ u₁ ∙ ElStrNatS (proj g) (proj a) aₛ a₁ p) (starTmS (proj g) (proj v) v₀) (ssₛS (compS (proj v) (proj g) (! v₀))) (starTm₁S (proj g) (proj v) vₛ v₀ v₁ ∙ ElStrNatS (proj g) (proj a) aₛ a₁ p)
-- idStrNatS-// i (dmor (_ , _) (_ , _) _ _) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) aₛ a₁ (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) uₛ u₁ (dmor (_ , _) ((_ , _) , (_ , _)) (_ , _) (_ , _)) vₛ v₁ p = refl

-- idStrNatS : (i : ℕ) {n m : ℕ} (g : MorS n m) (a : MorS m (suc m)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i (∂₀S a)) (u : MorS m (suc m)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i a aₛ a₁)
--                                                 (v : MorS m (suc m)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i a aₛ a₁) (p : ∂₀S a ≡ ∂₁S g)
--                                                 (let u₀ = is-section₀S u uₛ u₁ ∙ ElStr=S i a aₛ a₁ ∙ p) (let v₀ = is-section₀S v vₛ v₁ ∙ ElStr=S i a aₛ a₁ ∙ p)
--              → starTmS g (idStrS i a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStr₀S i a aₛ a₁ u uₛ u₁ v vₛ v₁ ∙ p) ≡ idStrS i (starTmS g a p) (ssₛS (compS a g (! p))) (starTm₁S g a aₛ p a₁ ∙ UUStrNatS g (∂₀S a) p ∙ ap (UUStrS i) (! (ss₀S (compS a g (! p)) ∙ comp₀S a g (! p))))
--                                                                                    (starTmS g u u₀) (ssₛS (compS u g (! u₀))) (starTm₁S g u uₛ u₀ u₁ ∙ ElStrNatS g a aₛ a₁ p) (starTmS g v v₀) (ssₛS (compS v g (! v₀))) (starTm₁S g v vₛ v₀ v₁ ∙ ElStrNatS g a aₛ a₁ p)
-- idStrNatS i = //-elimP (λ g → //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ p → idStrNatS-// i g a aₛ a₁ u uₛ u₁ v vₛ v₁ p))))




-- reflStr₀S : ∀ {n} A u uₛ u₁ → _
-- reflStr₀S {n} A u uₛ u₁ = is-section₀S {n} (reflStrS A u uₛ u₁) (reflStrₛS A u uₛ u₁) (reflStr₁S A u uₛ u₁) ∙ IdStr=S A u uₛ u₁ u uₛ u₁

-- reflStrNatS-// : {n m : ℕ} (g : DMor n m) (A : DCtx (suc m)) (u : DMor m (suc m)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ (proj A)) (p : ftS (proj A) ≡ ∂₁S (proj g))
--                  (let u₀ = is-section₀S (proj u) uₛ u₁ ∙ p)
--              → starTmS (proj g) (reflStrS (proj A) (proj u) uₛ u₁) (reflStr₀S (proj A) (proj u) uₛ u₁ ∙ p) ≡ reflStrS (starS (proj g) (proj A) (! p)) (starTmS (proj g) (proj u) u₀) (ssₛS (compS (proj u) (proj g) (! u₀))) (starTm₁S (proj g) (proj u) uₛ u₀ u₁)
-- reflStrNatS-// (dmor (_ , _) (_ , _) δ _) ((_ , A) , (_ , _)) (dmor (_ , _) ((_ , _) , (_ , _)) (_ , u) (_ , _)) uₛ u₁ p = up-to-rhsTyEq (ap (_[_]Ty (id A u u)) (idMor[]Mor δ))

-- reflStrNatS : {n m : ℕ} (g : MorS n m) (A : ObS (suc m)) (u : MorS m (suc m)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ A) (p : ftS A ≡ ∂₁S g)
--                  (let u₀ = is-section₀S u uₛ u₁ ∙ p)
--              → starTmS g (reflStrS A u uₛ u₁) (reflStr₀S A u uₛ u₁ ∙ p) ≡ reflStrS (starS g A (! p)) (starTmS g u u₀) (ssₛS (compS u g (! u₀))) (starTm₁S g u uₛ u₀ u₁)
-- reflStrNatS = //-elimP (λ g → //-elimP (λ A → //-elimP (λ u uₛ u₁ p → reflStrNatS-// g A u uₛ u₁ p)))

{- equality structure -}

betaPiStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS (suc n) (suc (suc n))) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ B) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
            → appStrS Γ A A= B B= (lamStrS Γ A A= B B= u uₛ u₁) (lamStrₛS Γ A A= B B= u uₛ u₁) (lamStr₁S Γ A A= B B= u uₛ u₁) a aₛ a₁ ≡ S.starTm a u (S.is-section₀ uₛ u₁ ∙ B=) a₁
betaPiStrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → //-elimP (λ a aₛ a₁ → eq (box
             (CtxSymm (CtxTran (reflectOb (S.is-section₀ aₛ a₁)) (reflectOb A=)))
             (CtxSymm (CtxTran (reflectOb (S.is-section₀ aₛ a₁)) (reflectOb A=)) ,, SubstTyMorEq2 (der Γ) (der Γ , dTy A A=)
                                                                                                  (dTy+= A= (sym (reflect u₁)) B=)
                                                                                                  (MorTran (der Γ) (der Γ , dTy A A=)
                                                                                                           (MorSymm (der Γ) (der Γ , (dTy A A=)) (morTm=idMorTm A= a aₛ a₁))
                                                                                                           (congMorEq refl refl (idMor[]Mor _) refl
                                                                                                                      (SubstMorEq (MorSymm (der Γ , dTy A A=) (der Γ , dTy A A=)
                                                                                                                                           (getMor=idMor (combine A= B B=) u uₛ u₁)) (dMor A= a aₛ a₁)))))
             (idMor+= (der Γ) (TmTran (SubstTm (dTm+ A= B= u uₛ u₁) (idMor+ (der Γ) (dTm A= a aₛ a₁)))
                                      (BetaPi (dTy A A=) (dTy+ A= B B=) (dTm+ A= B= u uₛ u₁) (dTm A= a aₛ a₁))
                                      (SubstTmMorEq (dTm+ A= B= u uₛ u₁) (idMor+ (der Γ) (dTm A= a aₛ a₁)) (MorSymm (der Γ) (der Γ , dTy A A=) (morTm=idMorTm A= a aₛ a₁)))))))))))



betaSig1StrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ S.star a B B= a₁) → pr1StrS Γ A A= B B= (pairStrS Γ A A= B B= a aₛ a₁ b bₛ b₁) (pairStrₛS Γ A A= B B= a aₛ a₁ b bₛ b₁) (pairStr₁S Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ a
betaSig1StrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ →
             eq (box (CtxSymm (CtxTran (reflectOb (S.is-section₀ aₛ a₁)) (reflectOb A=) ))
                     (CtxTran (CtxTy=Ctx A A=) (CtxSymm (reflectOb a₁)))
                     (MorTran (der Γ) (der Γ , dTy A A=) (idMor+= (der Γ) (BetaSig1 (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)))
                                                         (MorSymm (der Γ) (der Γ , dTy A A=) (morTm=idMorTm A= a aₛ a₁)))))))))

betaSig2StrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ S.star a B B= a₁) → pr2StrS Γ A A= B B= (pairStrS Γ A A= B B= a aₛ a₁ b bₛ b₁) (pairStrₛS Γ A A= B B= a aₛ a₁ b bₛ b₁) (pairStr₁S Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ b
betaSig2StrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → eq (box
                        (CtxSymm (CtxTran (reflectOb (S.is-section₀ bₛ b₁)) (CtxTran (reflectOb (S.is-section₀ aₛ a₁)) (reflectOb A=))))
                        (CtxTran (CtxRefl (der Γ) ,, SubstTyMorEq (dTy+ A= B B=)
                                                                  (idMor+ (der Γ) (Pr1 (dTy A A=) (dTy+ A= B B=) (Pair (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁))))
                                                                  (MorTran (der Γ) (der Γ , dTy A A=) (idMor+= (der Γ) (BetaSig1 (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)))
                                                                                                      (MorSymm (der Γ) (der Γ , dTy A A=) (morTm=idMorTm A= a aₛ a₁))))
                                 (CtxTran (CtxSymm (CtxTran (reflectOb (S.is-section₀ aₛ a₁)) (reflectOb A=)) ,, TyRefl (SubstTy (dTy+ A= B B=) (dMor A= a aₛ a₁)))
                                          (CtxSymm (reflectOb b₁)))) 
                        (MorTran (der Γ) (der Γ , SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (Pr1 (dTy A A=) (dTy+ A= B B=)
                                                                                              (Pair (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)))))
                                 (idMor+= (der Γ) (ConvEq (SubstTy (dTy+ A= B B=)
                                                          (idMor+ (der Γ) (dTm A= a aₛ a₁)))
                                                          (BetaSig2 (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁))
                                                          (SubstTyMorEq (dTy+ A= B B=) (idMor+ (der Γ) (dTm A= a aₛ a₁))
                                                                                       (idMor+= (der Γ) (TmSymm (BetaSig1 (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)))))))
                                 (MorSymm (der Γ) (der Γ , SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (Pr1 (dTy A A=) (dTy+ A= B B=) (Pair (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)))))
                                          (ConvMorEq (morTm=idMorTm {Γ = Γ} (eq (box (CtxTran (reflectOb (S.is-section₀ aₛ a₁)) (reflectOb A=)))) b bₛ b₁)
                                                     (CtxRefl (der Γ)) (CtxRefl (der Γ) ,, SubstTyMorEq (dTy+ A= B B=) (dMor A= a aₛ a₁)
                                                                                                        (MorTran (der Γ) (der Γ , dTy A A=)
                                                                                                                 (morTm=idMorTm A= a aₛ a₁)
                                                                                                                 (idMor+= (der Γ) (TmSymm (BetaSig1 (dTy A A=)
                                                                                                                                                    (dTy+ A= B B=)
                                                                                                                                                    (dTm A= a aₛ a₁)
                                                                                                                                                    (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)))))))))))))))

betaNatelimZeroS : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
               (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : S.∂₁ dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
               (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : S.∂₁ dS ≡ T-dS₁ sucStrSynCCat Γ P P=) →
               natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ (zeroStrS Γ) (zeroStrₛS Γ) (zeroStr₁S Γ)  ≡ dO               
betaNatelimZeroS = let fixSubstTy X = (! (weaken[]Ty _ _ last) ∙ ap weakenTy ([idMor]Ty _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty (getTy X)) (ap (λ z → z , suc (var last)) (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _)) ∙  ! (weakenTyInsert' _ _ _ _ ∙ refl)))                      
                  in
                  //-elimP (λ Γ → //-elimP (λ P P= → (//-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → eq (box
                           (CtxSymm (reflectOb (S.is-section₀ dOₛ dO₁)))
                           (CtxSymm (reflectOb dO₁))
                           (MorTran (der Γ) (der Γ , SubstTy (dTy P P=) (idMor+ (der Γ) Zero)) (idMor+= (der Γ) (BetaNatZero (dTy P P=) (dTm refl dO dOₛ dO₁) (congTmTy (fixSubstTy P) (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (eq (box (CtxSymm (CtxTy=Ctx P P=)))) dS dSₛ dS₁)))) (MorSymm (der Γ) (der Γ , SubstTy (dTy P P=) (idMor+ (der Γ) Zero)) (morTm=idMorTm refl dO dOₛ dO₁)))))))))


betaNatelimSucS : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
               (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : S.∂₁ dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
               (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : S.∂₁ dS ≡ T-dS₁ sucStrSynCCat Γ P P=)
               (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ) →
               natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ (sucStrS Γ u uₛ u₁) (sucStrₛS Γ u) (sucStr₁S Γ u) ≡ S.starTm (natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) (S.starTm (qqS u P (u₁ ∙ ! P=)) dS (S.is-section₀ dSₛ dS₁ ∙ S.ft-star ∙ S.pp₀) (qq₁S u P (u₁ ∙ ! P=))) (S.ss₀ ∙ S.comp₀ ∙ S.qq₀) (natelimStr₁S Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)
betaNatelimSucS = let fixSubstTy X = (! (weaken[]Ty _ _ last) ∙ ap weakenTy ([idMor]Ty _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty (getTy X)) (ap (λ z → z , suc (var last)) (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _)) ∙  ! (weakenTyInsert' _ _ _ _ ∙ refl)))                      
                  in
                //-elimP (λ Γ → //-elimP (λ P P= → (//-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → //-elimP (λ u uₛ u₁ → eq (box
                  (CtxRefl (der Γ))
                  {!!}
                  (MorTran (der Γ) (der Γ , SubstTy (dTy P P=) (idMor+ (der Γ) (Suc (dTm refl u uₛ u₁)))) (idMor+= (der Γ) (BetaNatSuc (dTy P P=) (dTm refl dO dOₛ dO₁) (congTmTy (fixSubstTy P) (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (eq (box (CtxSymm (CtxTy=Ctx P P=)))) dS dSₛ dS₁)) (dTm refl u uₛ u₁))) (idMor+= (der Γ) (congTmEq refl (! ([]Tm-assoc _ _ _)) refl ?))))))))))


eluuStrS : (i : ℕ) (Γ : ObS n) → ElStrS (suc i) Γ (uuStrS i Γ) (uuStrₛS i Γ) (uuStr₁S i Γ) ≡ UUStrS i Γ
eluuStrS i = //-elimP (λ Γ → eq (box (CtxRefl (der Γ) ,, ElUU=)))

elpiStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁))
            → ElStrS i Γ (piStrS i Γ a aₛ a₁ b bₛ b₁) (piStrₛS i Γ a aₛ a₁ b bₛ b₁) (piStr₁S i Γ a aₛ a₁ b bₛ b₁) ≡ PiStrS Γ (ElStrS i Γ a aₛ a₁) (ElStr=S i Γ a aₛ a₁) (ElStrS i (ElStrS i Γ a aₛ a₁) b bₛ b₁) (ElStr=S i (ElStrS i Γ a aₛ a₁) b bₛ b₁)
elpiStrS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → eq (box (CtxRefl (der Γ) ,, ElPi= (dTm refl a aₛ a₁) (dTm refl b bₛ b₁))))))

elsigStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁))
            → ElStrS i Γ (sigStrS i Γ a aₛ a₁ b bₛ b₁) (sigStrₛS i Γ a aₛ a₁ b bₛ b₁) (sigStr₁S i Γ a aₛ a₁ b bₛ b₁) ≡ SigStrS Γ (ElStrS i Γ a aₛ a₁) (ElStr=S i Γ a aₛ a₁) (ElStrS i (ElStrS i Γ a aₛ a₁) b bₛ b₁) (ElStr=S i (ElStrS i Γ a aₛ a₁) b bₛ b₁)
elsigStrS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → eq (box (CtxRefl (der Γ) ,, ElSig= (dTm refl a aₛ a₁) (dTm refl b bₛ b₁))))))

elnatStrS : (i : ℕ) (Γ : ObS n) → ElStrS i Γ (natStrS i Γ) (natStrₛS i Γ) (natStr₁S i Γ) ≡ NatStrS Γ
elnatStrS i = //-elimP (λ Γ → eq (box (CtxRefl (der Γ) ,, ElNat=)))

elidStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)
                   (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁) → ElStrS i Γ (idStrS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStrₛS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStr₁S i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ IdStrS Γ (ElStrS i Γ a aₛ a₁) (ElStr=S i Γ a aₛ a₁) u uₛ u₁ v vₛ v₁
elidStrS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → eq (box (CtxRefl (der Γ) ,, ElId= (dTm refl a aₛ a₁) (dTm refl u uₛ u₁) (dTm refl v vₛ v₁)))))))

open StructuredCCat

strSynCCat : StructuredCCat

ccat strSynCCat = synCCat

ccatUU strSynCCat = UUStrSynCCat
ccatEl strSynCCat = ElStrSynCCat
ccatPi strSynCCat = PiStrSynCCat
ccatSig strSynCCat = SigStrSynCCat
ccatNat strSynCCat = NatStrSynCCat
ccatId strSynCCat = IdStrSynCCat
ccatuu strSynCCat = uuStrSynCCat
ccatpi strSynCCat = piStrSynCCat
ccatlam strSynCCat = lamStrSynCCat
ccatapp strSynCCat = appStrSynCCat
ccatsig strSynCCat = sigStrSynCCat
ccatpair strSynCCat = pairStrSynCCat
ccatpr1 strSynCCat = pr1StrSynCCat
ccatpr2 strSynCCat = pr2StrSynCCat
ccatnat strSynCCat = natStrSynCCat
ccatzero strSynCCat = zeroStrSynCCat
ccatsuc strSynCCat = sucStrSynCCat
ccatnatelim strSynCCat = natelimStrSynCCat
ccatid strSynCCat = idStrSynCCat
ccatrefl strSynCCat = reflStrSynCCat


betaPiStr strSynCCat {Γ = Γ} {A = A} {B = B} {u = u} {a = a} = betaPiStrS Γ A _ B _ u _ _ a _ _
betaSig1Str strSynCCat {Γ = Γ} {A = A} {B = B} {a = a} {b = b} = betaSig1StrS Γ A _ B _ a _ _ b _ _
betaSig2Str strSynCCat {Γ = Γ} {A = A} {B = B}  {a = a} {b = b} = betaSig2StrS Γ A _ B _ a _ _ b _ _
betaNatelimZero strSynCCat {Γ = Γ} {P = P} {dO = dO} {dS = dS} = betaNatelimZeroS Γ P _ dO _ _ dS _ _
betaNatelimSuc strSynCCat {Γ = Γ} {P = P} {dO = dO} {dS = dS} {u = u} = betaNatelimSucS Γ P _ dO _ _ dS _ _ u _ _
eluuStr strSynCCat {Γ = Γ} = eluuStrS _ Γ
elpiStr strSynCCat {Γ = Γ} {a = a} {b = b} = elpiStrS _ Γ a _ _ b _ _
elsigStr strSynCCat {Γ = Γ} {a = a} {b = b} = elsigStrS _ Γ a _ _ b _ _
elnatStr strSynCCat {Γ = Γ} = elnatStrS _ Γ
elidStr strSynCCat {Γ = Γ} {a = a} {u = u} {v = v} = elidStrS _ Γ a _ _ u _ _ v _ _
 
