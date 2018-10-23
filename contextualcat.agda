{-# OPTIONS --rewriting --irrelevant-projections #-}

open import common hiding (_,_)

variable
  {n m k l} : ℕ

ap-irr : {A C : Set} {B : A → Set} (f : (a : A) .(b : B a) → C) {a a' : A} (p : a ≡ a') {b : B a} {b' : B a'} → f a b ≡ f a' b'
ap-irr f refl = refl

ap-irr2 : {A C D : Set} {B : A → C → Set} (f : (a : A) (c : C) .(b : B a c) → D) {a a' : A} (p : a ≡ a') {c c' : C} (q : c ≡ c') {b : B a c} {b' : B a' c'} → f a c b ≡ f a' c' b'
ap-irr2 f refl refl = refl

{- Definition of contextual categories as algebras of an essentially algebraic theory -}

record CCat : Set₁ where
  field
    -- objects
    Ob : ℕ → Set
    -- morphisms
    Mor : ℕ → ℕ → Set
    -- domain and codomain
    ∂₀ : Mor n m → Ob n
    ∂₁ : Mor n m → Ob m
    -- identity morphism
    id : Ob n → Mor n n
    id₀ : {X : Ob n} → ∂₀ (id X) ≡ X
    id₁ : {X : Ob n} → ∂₁ (id X) ≡ X
    -- composition
    comp : (g : Mor m k) (f : Mor n m) .(_ : ∂₁ f ≡ ∂₀ g) → Mor n k
    comp₀ : {g : Mor m k} {f : Mor n m} .{p : ∂₁ f ≡ ∂₀ g} → ∂₀ (comp g f p) ≡ ∂₀ f
    comp₁ : {g : Mor m k} {f : Mor n m} .{p : ∂₁ f ≡ ∂₀ g} → ∂₁ (comp g f p) ≡ ∂₁ g
    -- father and projection
    ft  : Ob (suc n) → Ob n
    pp  : (X : Ob (suc n)) → Mor (suc n) n
    pp₀ : {X : Ob (suc n)} → ∂₀ (pp X) ≡ X
    pp₁ : {X : Ob (suc n)} → ∂₁ (pp X) ≡ ft X
    -- star and q
    star : (f : Mor m n) (X : Ob (suc n)) .(_ : ∂₁ f ≡ ft X) → Ob (suc m)
    qq   : (f : Mor m n) (X : Ob (suc n)) .(_ : ∂₁ f ≡ ft X) → Mor (suc m) (suc n)
    qq₀  : {f : Mor m n} {X : Ob (suc n)} .{p : ∂₁ f ≡ ft X} → ∂₀ (qq f X p) ≡ star f X p
    qq₁  : {f : Mor m n} {X : Ob (suc n)} .{p : ∂₁ f ≡ ft X} → ∂₁ (qq f X p) ≡ X
    -- s
    ss  : (f : Mor m (suc n)) → Mor m (suc m)
    ss₀ : {f : Mor m (suc n)} → ∂₀ (ss f) ≡ ∂₀ f
    ss₁ : {f : Mor m (suc n)} → ∂₁ (ss f) ≡ star (comp (pp (∂₁ f)) f (! pp₀)) (∂₁ f) (comp₁ ∙ pp₁)
    -- terminal object
    pt : Ob 0
    pt-unique : (x : Ob 0) → x ≡ pt
    ptmor : Ob n → Mor n 0
    ptmor₀ : {X : Ob n} → ∂₀ (ptmor X) ≡ X
    ptmor₁ : {X : Ob n} → ∂₁ (ptmor X) ≡ pt
    ptmor-unique : (X : Ob n) (f : Mor n 0) (p : ∂₀ f ≡ X) (q : ∂₁ f ≡ pt) → f ≡ ptmor X
    -- identity laws and associativity
    id-right : {f : Mor n m} → comp (id (∂₁ f)) f (! id₀) ≡ f
    id-left  : {f : Mor n m} {X : Ob n} {p : ∂₁ (id X) ≡ ∂₀ f} → comp f (id X) p ≡ f
    assoc : {h : Mor k l} {g : Mor m k} {f : Mor n m} {p : ∂₁ f ≡ ∂₀ g} {q : ∂₁ g ≡ ∂₀ h} → comp (comp h g q) f (p ∙ ! comp₀) ≡ comp h (comp g f p) (comp₁ ∙ q)
    -- properties of star and q
    ft-star : {f : Mor m n} {X : Ob (suc n)} .{p : ∂₁ f ≡ ft X} → ft (star f X p) ≡ ∂₀ f
    pp-qq   : {f : Mor m n} {X : Ob (suc n)} .{p : ∂₁ f ≡ ft X} → comp (pp X) (qq f X p) (qq₁ ∙ ! pp₀) ≡ comp f (pp (star f X p)) (pp₁ ∙ ft-star)
    star-id : {X : Ob (suc n)} → star (id (ft X)) X id₁ ≡ X
    qq-id : {X : Ob (suc n)} → qq (id (ft X)) X id₁ ≡ id X
    star-comp : {m n k : ℕ} {g : Mor m k} {f : Mor n m} .{p : ∂₁ f ≡ ∂₀ g} {X : Ob (suc k)} .(q : ∂₁ g ≡ ft X) → star (comp g f p) X (comp₁ ∙ q) ≡ star f (star g X q) (p ∙ ! ft-star)
    --qq-comp
    -- properties of s
    ss-pp : {m n : ℕ} {f : Mor m (suc n)} → comp (pp (star (comp (pp (∂₁ f)) f (! pp₀)) (∂₁ f) (comp₁ ∙ pp₁))) (ss f) (ss₁ ∙ ! pp₀) ≡ id (∂₀ f)
    ss-qq : {m n : ℕ} {f : Mor m (suc n)} → f ≡ comp (qq (comp (pp (∂₁ f)) f (! pp₀)) (∂₁ f) (comp₁ ∙ pp₁)) (ss f) (ss₁ ∙ ! qq₀)
    ss-comp : {m n k : ℕ} {U : Ob (suc k)} {g : Mor n k} {g₁ : ∂₁ g ≡ ft U} {f : Mor m (suc n)} {f₁ : ∂₁ f ≡ star g U g₁} {-g₀ : ∂₀ g ≡ ft (∂₁ f)-} → ss f ≡ ss (comp (qq g U g₁) f (! (qq₀ ∙ ! f₁)))

{- Some properties and structures on a contextual category -}

module M (C : CCat) where

  open CCat C

  {- [Ty X n] represents types in a context iterated n times from X -}

  ft^ : (m : ℕ) → Ob (m + n) → Ob n
  ft^ 0 X = X
  ft^ (suc m) X = ft^ m (ft X)

  record TyPred {m : ℕ} (X : Ob m) (n : ℕ) : Set where
    constructor _,_
    field
      toCtx : Ob (n + m)
      .toCtxEq : ft^ n toCtx ≡ X
  open TyPred public

  Ty : {m : ℕ} (X : Ob m) (n : ℕ) → Set
  Ty X n = TyPred X (suc n)

  pair-irr : {m : ℕ} {X : Ob m} {n : ℕ} {a a' : Ob (n + m)} {b : ft^ n a ≡ X} {b' : ft^ n a' ≡ X} → a ≡ a' → (a , b) ≡ (a' , b')
  pair-irr refl = refl

  ft' : {n : ℕ} {X : Ob n} → TyPred X (suc m) → TyPred X m
  ft' (Y , p) = (ft Y , p)

  {- Definition of the iterated star and qq operations -}

  star^ : (f : Mor m k) → TyPred (∂₁ f) n → TyPred (∂₀ f) n
  qq^   : {m n k : ℕ} (f : Mor m k) (X : TyPred (∂₁ f) n) → Mor (n + m) (n + k)
  .qq^₀ : {m n k : ℕ} {f : Mor m k} {X : TyPred (∂₁ f) n} → ∂₀ (qq^ f X) ≡ toCtx (star^ f X)
  .qq^₁ : {m n k : ℕ} {f : Mor m k} {X : TyPred (∂₁ f) n} → ∂₁ (qq^ f X) ≡ toCtx X

  star^ {n = 0}   f (X , p) = ∂₀ f , refl
  star^ {n = suc n} f (X , p) = (star (qq^ f (ft' (X , p))) X qq^₁) , (ap (ft^ n) (ft-star ∙ qq^₀) ∙ toCtxEq (star^ f (ft' (X , p))))

  qq^ {n = 0} f (X , p) = f
  qq^ {n = suc n} f (X , p) = qq (qq^ f (ft' (X , p))) X (qq^₁ {X = ft' (X , p)})

  qq^₀ {n = 0} = refl
  qq^₀ {n = suc n} = qq₀

  qq^₁ {n = 0} {X = X} = ! (toCtxEq X)
  qq^₁ {n = suc n} = qq₁

  --

  .ft-star^ : {n m k : ℕ} {f : Mor m k} (X : Ty (∂₁ f) n) .(p : ft^ (suc n) (toCtx X) ≡ ∂₁ f) → ft' (star^ f X) ≡ star^ f (ft' X)
  ft-star^ {zero}  _ _ = pair-irr ft-star
  ft-star^ {suc n} _ _ = pair-irr (ft-star ∙ qq₀)
  
  {- Identity laws for the iterated star and qq operations -}

  .star^-id : {m n : ℕ} {X : Ob (n + m)} → toCtx (star^ {n = n} (id (ft^ n X)) (X , ! id₁)) ≡ X
  .qq^-id   : {m n : ℕ} {X : Ob (n + m)} → qq^ (id (ft^ n X)) (X , ! id₁) ≡ id X

  star^-id {n = 0} = id₀
  star^-id {n = suc n} = ap-irr (λ x y → star x _ y) (qq^-id {n = n} {X = ft _}) ∙ star-id

  qq^-id {n = 0} = refl
  qq^-id {n = suc n} = ap-irr (λ x y → qq x _ y) (qq^-id {n = n}) ∙ qq-id

  {- Composition laws for the iterated star and qq operations -}
  -- TODO

  {- [Tm X n] represents terms in a context iterated n times from X -}

  record Tm {k : ℕ} (X : Ob k) (n : ℕ) : Set where
    field
      getTy : Ty X n
      morTm : Mor (n + k) (suc (n + k))
      .morTm₀ : ∂₀ morTm ≡ toCtx (ft' getTy)
      .morTm₁ : ∂₁ morTm ≡ toCtx getTy
      .eqTm : comp (pp (toCtx getTy)) morTm (morTm₁ ∙ ! pp₀) ≡ id (toCtx (ft' getTy))
  open Tm public

  star^tm : (f : Mor m k) → Tm (∂₁ f) n → Tm (∂₀ f) n
  getTy (star^tm f s) = star^ f (getTy s)
  morTm (star^tm f s) = ss (comp (morTm s) (qq^ f (ft' (getTy s))) (qq^₁ {f = f} ∙ ! (morTm₀ s)))
  morTm₀ (star^tm f s) = (ss₀ ∙ (comp₀ ∙ qq^₀ {f = f})) ∙ ! (ap toCtx (ft-star^ (getTy s) (toCtxEq (getTy s))))
  morTm₁ (star^tm f s) = ss₁ ∙ ap-irr2 star (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ (ap-irr (λ x y → comp x (qq^ f _) y) (ap-irr (λ x y → comp (pp x) _ y) (comp₁ ∙ morTm₁ s) ∙ (eqTm s ∙ ap id (! (qq^₁ {f = f})))) ∙ id-right)) (comp₁ ∙ morTm₁ s)
  eqTm (star^tm f s) =
    ap-irr (λ x y → comp x (morTm (star^tm f s)) y)
     (ap pp (ap-irr2 star (! (! (assoc {q = ! (pp₀ ∙ comp₁)})
                              ∙ (ap-irr (λ x y → comp x (qq^ f (ft (toCtx (getTy s)) , toCtxEq (getTy s))) y)
                                 (ap-irr (λ x y → comp x (morTm s) y)
                                  (ap pp (comp₁ ∙ morTm₁ s))
                                 ∙ (eqTm s ∙ ap id (! (qq^₁ {f = f}))))
                                 ∙ id-right)))
                          (! (comp₁ ∙ morTm₁ s))))
     ∙ (ss-pp {f = comp (morTm s) (qq^ f (ft' (getTy s))) (qq^₁ {f = f} ∙ ! (morTm₀ s))}
       ∙ ap id (comp₀ ∙ (qq^₀ {f = f} ∙ ! (ft-star ∙ qq^₀ {f = f}))))

  star^tm-with-eqs : {m n k : ℕ} (f : Mor m k) {X : Ob k} (p : ∂₁ f ≡ X) {Y : Ob m} (q : ∂₀ f ≡ Y) → Tm X n → Tm Y n
  star^tm-with-eqs f refl refl = star^tm f

  {- Variables -}

  trim : {n : ℕ} (k : ℕ) (X : Ob n) → Ob (n - k)
  trim zero X = X
  trim {zero} (suc k) X = X -- or pt…
  trim {suc n} (suc k) X = trim k (ft X)

  last-var : {n : ℕ} (X : Ob (suc n)) → Tm X 0
  toCtx (getTy (last-var X)) = star (pp X) X pp₁
  toCtxEq (getTy (last-var X)) = ft-star ∙ pp₀
  morTm (last-var X) = ss (id X)
  morTm₀ (last-var X) = ss₀ ∙ (id₀ ∙ ! (ft-star ∙ pp₀))
  morTm₁ (last-var X) = ss₁ ∙ ap-irr2 star (id-left ∙ ap pp id₁) id₁
  eqTm (last-var X) = ap-irr (λ x y → comp x (ss (id X)) y) (ap pp (ap-irr2 star (! (id-left ∙ ap pp id₁)) (! id₁))) ∙ (ss-pp {f = id X} ∙ ap id (id₀ ∙ ! (ft-star ∙ pp₀)))

  var-unweakened : {n : ℕ} (k : ℕ) (X : Ob n) → Maybe (Tm (trim k X) 0)
  var-unweakened {zero} _ X = Nothing
  var-unweakened {suc n} zero X = Just (last-var X)
  var-unweakened {suc n} (suc k) X = var-unweakened {n} k (ft X)

  weaken : {n : ℕ} (k : ℕ) {X : Ob n} → Tm (trim k X) 0 → Tm X 0
  weaken 0 x = x
  weaken {0} (suc k) x = x
  weaken {suc n} (suc k) {X} x = star^tm-with-eqs (pp X) pp₁ pp₀ (weaken k x)

  var : {n : ℕ} (k : ℕ) (X : Ob n) → Maybe (Tm X 0)
  var k X with var-unweakened k X
  var k X | Nothing = Nothing
  var k X | Just x = Just (weaken k x)

  substCTy : {n m : ℕ} (X : Ob n) (A : Ty X (suc m)) (u : Tm X m) .(p : getTy u ≡ ft' A) → Ty X m
  substCTy {m = m} X A u p = (star (morTm u) (toCtx A) (morTm₁ u ∙ ap toCtx p) , (ap (ft^ m) (ft-star ∙ morTm₀ u) ∙ (ap (λ z → ft^ m (toCtx (ft' z))) p ∙ toCtxEq A)))
  -- toCtx (substCTy {m = m} X A u p) = star (morTm u) (toCtx A) (morTm₁ u ∙ ap toCtx p)
  -- toCtxEq (substCTy {m = m} X A u p) = ap (ft^ m) (ft-star ∙ morTm₀ u) ∙ (ap (λ z → ft^ m (toCtx (ft' z))) {!p!} ∙ toCtxEq A)

  .ft-substCTy : {n m : ℕ} (X : Ob n) (A : Ty X (suc m)) (u : Tm X m) (p : getTy u ≡ ft' A) → ft (toCtx (substCTy X A u p)) ≡ ft (ft (toCtx A))
  ft-substCTy X A u p = ft-star ∙ (morTm₀ u ∙ ap ft (ap toCtx p))

  substCTm : (X : Ob n) (v : Tm X (suc m)) (u : Tm X m) .(p : getTy u ≡ ft' (getTy v)) → Tm X m
  substCTm X v u p = record {
  {-getTy (substCTm X v u p)-} getTy = substCTy X (getTy v) u p;
  {-morTm (substCTm X v u p)-} morTm = ss (comp (morTm v) (morTm u) (morTm₁ u ∙ (ap toCtx p ∙ ! (morTm₀ v))));
  {-morTm₀ (substCTm X v u p)-} morTm₀ = ss₀ ∙ (comp₀ ∙ (morTm₀ u ∙ (ap toCtx (ap ft' p) ∙ ! (ft-substCTy X (getTy v) u p))));
  {-morTm₁ (substCTm X v u p)-} morTm₁ = ss₁ ∙ (star-comp pp₁ ∙ (star-comp (morTm₁ v ∙ ! (ft-star ∙ (pp₀ ∙ (comp₁ ∙ morTm₁ v)))) ∙ ap-irr (star (morTm u)) (! (star-comp {p = morTm₁ v ∙ ! (pp₀ ∙ (comp₁ ∙ morTm₁ v))} pp₁) ∙ (ap-irr2 star (ap-irr2 comp (ap pp (comp₁ ∙ morTm₁ v)) refl ∙ eqTm v) (comp₁ ∙ morTm₁ v) ∙ star-id) ) ));
  {-eqTm (substCTm X v u p)-} eqTm = ap-irr2 comp (ap pp (ap-irr2 star (! (! (assoc {q = morTm₁ v ∙ ! (pp₀ ∙ (comp₁ ∙ morTm₁ v))}) ∙ (ap-irr2 comp (ap-irr2 comp (ap pp (comp₁ {p = morTm₁ u ∙ ! (morTm₀ v ∙ ! (ap toCtx p))} ∙ morTm₁ v)) refl ∙ (eqTm v ∙ ap id (! (morTm₁ u ∙ ap toCtx p)))) refl ∙ id-right))) (! (comp₁ ∙ morTm₁ v)))) refl ∙ (ss-pp {f = comp (morTm v) (morTm u) _} ∙ ap id (comp₀ ∙ (morTm₀ u ∙ ! (ft-substCTy X (getTy v) u p ∙ ! (ap ft (ap toCtx p))))))}

{- Contextual categories with structure corresponding to the type theory we are interested in -}

record StructuredCCat : Set₁ where
  field
    cat : CCat

  open CCat cat public renaming (Mor to CMor)
  open M cat public

  field
    -- Additional structure on contextual categories
    PiStr : {n : ℕ} (X : Ob n) (A : Ty X 0) (B : Ty X 1) .(_ : ft' B ≡ A) → Ty X 0
    lamStr : (X : Ob n) (A : Ty X 0) (B : Ty X 1) (u : Tm X 1) .(_ : ft' B ≡ A) .(_ : getTy u ≡ B) → Tm X 0
    appStr : (X : Ob n) (A : Ty X 0) (B : Ty X 1) (f : Tm X 0) (a : Tm X 0) .(p : ft' B ≡ A) .(_ : getTy f ≡ PiStr X A B p) .(_ : getTy a ≡ A) → Tm X 0
    UUStr : (X : Ob n) → Ty X 0
    ElStr : (X : Ob n) (v : Tm X 0) .(_ : getTy v ≡ UUStr X) → Ty X 0

    -- Naturality
    PiStrNat : {n m : ℕ} (f : CMor n m) (let X = ∂₀ f) (let Y = ∂₁ f) (A : Ty Y 0) (B : Ty Y 1) (p : ft' B ≡ A)
              → star^ f (PiStr Y A B p) ≡ PiStr X (star^ f A) (star^ f B) (ft-star^ B (toCtxEq B) ∙ ap (star^ f) p)
    lamStrNat : {n m : ℕ} (f : CMor n m) (let X = ∂₀ f) (let Y = ∂₁ f) (A : Ty Y 0) (B : Ty Y 1) (u : Tm Y 1) (p : ft' B ≡ A) (q : getTy u ≡ B)
              → star^tm f (lamStr Y A B u p q) ≡ lamStr X (star^ f A) (star^ f B) (star^tm f u) (ft-star^ B (toCtxEq B) ∙ ap (star^ f) p) (ap (star^ f) q)
    appStrNat : {n m : ℕ} (f : CMor n m) (let X = ∂₀ f) (let Y = ∂₁ f) (A : Ty Y 0) (B : Ty Y 1) (g : Tm Y 0) (a : Tm Y 0) (p : ft' B ≡ A) (q : getTy g ≡ PiStr Y A B p) (r : getTy a ≡ A)
              → star^tm f (appStr Y A B g a p q r) ≡ appStr X (star^ f A) (star^ f B) (star^tm f g) (star^tm f a)
                                                            (ft-star^ B (toCtxEq B) ∙ ap (star^ f) p)
                                                            (ap (star^ f) q ∙ PiStrNat f A B p) (ap (star^ f) r)
    UUStrNat : {n m : ℕ} (f : CMor n m) (let X = ∂₀ f) (let Y = ∂₁ f) → star^ f (UUStr Y) ≡ UUStr X
    ElStrNat : {n m : ℕ} (f : CMor n m) (let X = ∂₀ f) (let Y = ∂₁ f) (v : Tm Y 0) (p : getTy v ≡ UUStr Y) → star^ f (ElStr Y v p) ≡ ElStr X (star^tm f v) (ap (star^ f) p ∙ UUStrNat f)


    -- Typing
    lamStrTy : {X : Ob n} {A : Ty X 0} {B : Ty X 1} {u : Tm X 1} .{p : ft' B ≡ A} .{q : getTy u ≡ B} → getTy (lamStr X A B u p q) ≡ PiStr X A B p
    appStrTy : {n : ℕ} {X : Ob n} {A : Ty X 0} {B : Ty X 1} {u : Tm X 1} {f : Tm X 0} {a : Tm X 0} .{p : ft' B ≡ A} .{q : getTy f ≡ PiStr X A B p} .{r : getTy a ≡ A}
             → getTy (appStr X A B f a p q r) ≡ substCTy X B a (r ∙ ! p)
    betaStr : {n : ℕ} (X : Ob n) (A : Ty X 0) (B : Ty X 1) (u : Tm X 1) (a : Tm X 0) .(p : ft' B ≡ A) .(q : getTy u ≡ B) .(r : getTy a ≡ A)
            → appStr X A B (lamStr X A B u p q) a p lamStrTy r ≡ substCTm X u a (r ∙ ! (ap ft' q ∙ p))
