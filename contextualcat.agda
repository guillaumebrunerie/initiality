{-# OPTIONS --rewriting --allow-unsolved-metas --prop #-}

open import common hiding (_,_)

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
    comp : (g : Mor m k) (f : Mor n m) (_ : ∂₁ f ≡ ∂₀ g) → Mor n k
    comp₀ : {g : Mor m k} {f : Mor n m} {p : ∂₁ f ≡ ∂₀ g} → ∂₀ (comp g f p) ≡ ∂₀ f
    comp₁ : {g : Mor m k} {f : Mor n m} {p : ∂₁ f ≡ ∂₀ g} → ∂₁ (comp g f p) ≡ ∂₁ g
    -- father and projection
    ft  : Ob (suc n) → Ob n
    pp  : (X : Ob (suc n)) → Mor (suc n) n
    pp₀ : {X : Ob (suc n)} → ∂₀ (pp X) ≡ X
    pp₁ : {X : Ob (suc n)} → ∂₁ (pp X) ≡ ft X
    -- star and q
    star : (f : Mor m n) (X : Ob (suc n)) (_ : ∂₁ f ≡ ft X) → Ob (suc m)
    qq   : (f : Mor m n) (X : Ob (suc n)) (_ : ∂₁ f ≡ ft X) → Mor (suc m) (suc n)
    qq₀  : {f : Mor m n} {X : Ob (suc n)} {p : ∂₁ f ≡ ft X} → ∂₀ (qq f X p) ≡ star f X p
    qq₁  : {f : Mor m n} {X : Ob (suc n)} {p : ∂₁ f ≡ ft X} → ∂₁ (qq f X p) ≡ X
    -- s
    ss  : (f : Mor m (suc n)) → Mor m (suc m)
    ss₀ : {f : Mor m (suc n)} → ∂₀ (ss f) ≡ ∂₀ f
    ss₁ : {f : Mor m (suc n)} → ∂₁ (ss f) ≡ star (comp (pp (∂₁ f)) f (! pp₀)) (∂₁ f) (comp₁ ∙ pp₁)
    -- terminal object
    pt : Ob 0
    pt-unique : (X : Ob 0) → X ≡ pt
    ptmor : Ob n → Mor n 0
    ptmor₀ : {X : Ob n} → ∂₀ (ptmor X) ≡ X
    ptmor₁ : {X : Ob n} → ∂₁ (ptmor X) ≡ pt
    ptmor-unique : (X : Ob n) (f : Mor n 0) (p : ∂₀ f ≡ X) (q : ∂₁ f ≡ pt) → f ≡ ptmor X
    -- identity laws and associativity
    id-right : {f : Mor n m} → comp (id (∂₁ f)) f (! id₀) ≡ f
    id-left  : {f : Mor n m} → comp f (id (∂₀ f)) id₁ ≡ f
    assoc : {h : Mor k l} {g : Mor m k} {f : Mor n m} {p : ∂₁ f ≡ ∂₀ g} {q : ∂₁ g ≡ ∂₀ h} → comp (comp h g q) f (p ∙ ! comp₀) ≡ comp h (comp g f p) (comp₁ ∙ q)
    -- properties of star and q
    ft-star : {f : Mor m n} {X : Ob (suc n)} {p : ∂₁ f ≡ ft X} → ft (star f X p) ≡ ∂₀ f
    pp-qq   : {f : Mor m n} {X : Ob (suc n)} {p : ∂₁ f ≡ ft X} → comp (pp X) (qq f X p) (qq₁ ∙ ! pp₀) ≡ comp f (pp (star f X p)) (pp₁ ∙ ft-star)
    star-id : {X : Ob (suc n)} → star (id (ft X)) X id₁ ≡ X
    qq-id : {X : Ob (suc n)} → qq (id (ft X)) X id₁ ≡ id X
    star-comp : {m n k : ℕ} {g : Mor m k} {f : Mor n m} {p : ∂₁ f ≡ ∂₀ g} {X : Ob (suc k)} (q : ∂₁ g ≡ ft X) → star (comp g f p) X (comp₁ ∙ q) ≡ star f (star g X q) (p ∙ ! ft-star)
 --   qq-comp : {m n k : ℕ} {g : Mor m k} {f : Mor n m} {p : ∂₁ f ≡ ∂₀ g} {X : Ob (suc k)} (q : ∂₁ g ≡ ft X) → qq (comp g f p) X (comp₁ ∙ q) ≡ comp (qq g X q) (qq f (star g X q) (p ∙ ! ft-star)) (qq₁ ∙ ! qq₀)
    -- properties of s
    ss-pp : {m n : ℕ} {f : Mor m (suc n)} → comp (pp (star (comp (pp (∂₁ f)) f (! pp₀)) (∂₁ f) (comp₁ ∙ pp₁))) (ss f) (ss₁ ∙ ! pp₀) ≡ id (∂₀ f)
    ss-qq : {m n : ℕ} {f : Mor m (suc n)} → f ≡ comp (qq (comp (pp (∂₁ f)) f (! pp₀)) (∂₁ f) (comp₁ ∙ pp₁)) (ss f) (ss₁ ∙ ! qq₀)
    ss-comp : {m n k : ℕ} {U : Ob (suc k)} {g : Mor n k} {g₁ : ∂₁ g ≡ ft U} {f : Mor m (suc n)} {f₁ : ∂₁ f ≡ star g U g₁} {-g₀ : ∂₀ g ≡ ft (∂₁ f)-} → ss f ≡ ss (comp (qq g U g₁) f (! (qq₀ ∙ ! f₁)))

-- {- Some properties and structures on a contextual category -}

-- module M (C : CCat) where

--   open CCat C

--   id-left' : {f : Mor n m} {X : Ob n} {p : ∂₁ (id X) ≡ ∂₀ f} → comp f (id X) p ≡ f
--   id-left' {f = f} {X} {p} = ap-irr (comp f) (ap id (! id₁ ∙ p)) ∙ id-left

--   {- [Ty X n] represents types in a context iterated n times from X -}

--   ft^ : (m : ℕ) → Ob (m + n) → Ob n
--   ft^ 0 X = X
--   ft^ (suc m) X = ft^ m (ft X)

--   record TyPred {m : ℕ} (X : Ob m) (n : ℕ) : Set where
--     constructor _,_
--     field
--       toCtx : Ob (n + m)
--       toCtxEq : ft^ n toCtx ≡ X
--   open TyPred public

--   Ty : {m : ℕ} (X : Ob m) (n : ℕ) → Set
--   Ty X n = TyPred X (suc n)

--   ft' : {n : ℕ} {X : Ob n} → TyPred X (suc m) → TyPred X m
--   ft' (Y , p) = (ft Y , p)

--   {- Definition of the iterated star and qq operations -}

--   star^-with-eqs : {m n k : ℕ} (f : Mor m k) {X : Ob k} (p : ∂₁ f ≡ X) {Y : Ob m} (q : ∂₀ f ≡ Y) → TyPred X n → TyPred Y n
--   qq^-with-eqs    : {m n k : ℕ} (f : Mor m k) {X : Ob k} (p : ∂₁ f ≡ X) (Z : TyPred X n) → Mor (n + m) (n + k)
--   qq^₀-with-eqs  : {m n k : ℕ} {f : Mor m k} {X : Ob k} {p : ∂₁ f ≡ X} {Y : Ob m} {q : ∂₀ f ≡ Y} {Z : TyPred X n} → ∂₀ (qq^-with-eqs f p Z) ≡ toCtx (star^-with-eqs f p q Z)
--   qq^₁-with-eqs  : {m n k : ℕ} {f : Mor m k} {X : Ob k} {p : ∂₁ f ≡ X} {Z : TyPred X n} → ∂₁ (qq^-with-eqs f p Z) ≡ toCtx Z

--   toCtx (star^-with-eqs {n = zero} f p {Y = Y} q (X , r)) = Y
--   toCtxEq (star^-with-eqs {n = zero} f p q (X , r)) = refl
--   toCtx (star^-with-eqs {n = suc n} f p q (X , r)) = star (qq^-with-eqs f p (ft' (X , r))) X qq^₁-with-eqs
--   toCtxEq (star^-with-eqs {n = suc n} f p q (X , r)) = ap (ft^ n) (ft-star ∙ qq^₀-with-eqs) ∙ toCtxEq (star^-with-eqs f p q (ft' (X , r)))

--   qq^-with-eqs {n = 0} f p (X , r) = f
--   qq^-with-eqs {n = suc n} f p (X , r) = qq (qq^-with-eqs f p (ft' (X , r))) X (qq^₁-with-eqs {Z = ft' (X , r)})

--   qq^₀-with-eqs {n = 0} {q = q} = q
--   qq^₀-with-eqs {n = suc n} = qq₀

--   qq^₁-with-eqs {n = 0} {p = p} {Z = Z} = p ∙ ! (toCtxEq Z)
--   qq^₁-with-eqs {n = suc n}     = qq₁

--   star^ : (f : Mor m k) → TyPred (∂₁ f) n → TyPred (∂₀ f) n
--   star^ f = star^-with-eqs f refl refl

--   qq^   : {m n k : ℕ} (f : Mor m k) (X : TyPred (∂₁ f) n) → Mor (n + m) (n + k)
--   qq^ f = qq^-with-eqs f refl

--   qq^₀ : {m n k : ℕ} {f : Mor m k} {X : TyPred (∂₁ f) n} → ∂₀ (qq^ f X) ≡ toCtx (star^ f X)
--   qq^₀ {f = f} {X = X} = qq^₀-with-eqs {f = f} {p = refl} {q = refl} {Z = X}

--   qq^₁ : {m n k : ℕ} {f : Mor m k} {X : TyPred (∂₁ f) n} → ∂₁ (qq^ f X) ≡ toCtx X
--   qq^₁ {f = f} {X = X} = qq^₁-with-eqs {f = f} {p = refl} {Z = X}

--   --

--   ft-star^ : {n m k : ℕ} {f : Mor m k} (X : Ty (∂₁ f) n) (p : ft^ (suc n) (toCtx X) ≡ ∂₁ f) → ft' (star^ f X) ≡ star^ f (ft' X)
--   ft-star^ {zero}  _ _ = ap-irr _,_ ft-star
--   ft-star^ {suc n} _ _ = ap-irr _,_ (ft-star ∙ qq₀)
  
--   {- Identity laws for the iterated star and qq operations -}

--   star^-id : {m n : ℕ} {X : Ob (n + m)} → toCtx (star^ {n = n} (id (ft^ n X)) (X , ! id₁)) ≡ X
--   qq^-id   : {m n : ℕ} {X : Ob (n + m)} → qq^ (id (ft^ n X)) (X , ! id₁) ≡ id X

--   star^-id {n = 0} = id₀
--   star^-id {n = suc n} = ap-irr (λ x y → star x _ y) (qq^-id {n = n} {X = ft _}) ∙ star-id

--   qq^-id {n = 0} = refl
--   qq^-id {n = suc n} = ap-irr (λ x y → qq x _ y) (qq^-id {n = n}) ∙ qq-id

--   {- Composition laws for the iterated star and qq operations -}
--   -- TODO

--   {- [Tm X n] represents terms in a context iterated n times from X -}

--   record Tm {k : ℕ} (X : Ob k) (n : ℕ) : Set where
--     field
--       getTy : Ty X n
--       morTm : Mor (n + k) (suc (n + k))
--       morTm₀ : ∂₀ morTm ≡ toCtx (ft' getTy)
--       morTm₁ : ∂₁ morTm ≡ toCtx getTy
--       eqTm : comp (pp (toCtx getTy)) morTm (morTm₁ ∙ ! pp₀) ≡ id (toCtx (ft' getTy))
--   open Tm public

--   star^tm : (f : Mor m k) → Tm (∂₁ f) n → Tm (∂₀ f) n
--   getTy (star^tm f s) = star^ f (getTy s)
--   morTm (star^tm f s) = ss (comp (morTm s) (qq^ f (ft' (getTy s))) (qq^₁ {f = f} ∙ ! (morTm₀ s)))
--   morTm₀ (star^tm f s) = (ss₀ ∙ (comp₀ ∙ qq^₀ {f = f})) ∙ ! (ap toCtx (ft-star^ (getTy s) (toCtxEq (getTy s))))
--   morTm₁ (star^tm f s) = ss₁ ∙ ap2-irr star (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ (ap-irr (λ x y → comp x (qq^ f _) y) (ap-irr (λ x y → comp (pp x) _ y) (comp₁ ∙ morTm₁ s) ∙ (eqTm s ∙ ap id (! (qq^₁ {f = f})))) ∙ id-right)) (comp₁ ∙ morTm₁ s)
--   eqTm (star^tm f s) =
--     ap-irr (λ x y → comp x (morTm (star^tm f s)) y)
--      (ap pp (ap2-irr star (! (! (assoc {q = ! (pp₀ ∙ comp₁)})
--                               ∙ (ap-irr (λ x y → comp x (qq^ f (ft (toCtx (getTy s)) , toCtxEq (getTy s))) y)
--                                  (ap-irr (λ x y → comp x (morTm s) y)
--                                   (ap pp (comp₁ ∙ morTm₁ s))
--                                  ∙ (eqTm s ∙ ap id (! (qq^₁ {f = f}))))
--                                  ∙ id-right)))
--                           (! (comp₁ ∙ morTm₁ s))))
--      ∙ (ss-pp {f = comp (morTm s) (qq^ f (ft' (getTy s))) (qq^₁ {f = f} ∙ ! (morTm₀ s))}
--        ∙ ap id (comp₀ ∙ (qq^₀ {f = f} ∙ ! (ft-star ∙ qq^₀ {f = f}))))

--   postulate
--     star^tm-with-eqs : {m n k : ℕ} (f : Mor m k) {X : Ob k} (p : ∂₁ f ≡ X) {Y : Ob m} (q : ∂₀ f ≡ Y) → Tm X n → Tm Y n
-- --  star^tm-with-eqs = {!!} -- f reflR reflR = star^tm f

--   {- Variables -}

--   trim : {n : ℕ} (k : Fin n) (X : Ob n) → Ob (n -F k)
--   trim last X = X
--   trim (prev k) X = trim k (ft X)

--   last-ty : (X : Ob (suc n)) → Ty X 0
--   toCtx (last-ty X) = star (pp X) X pp₁
--   toCtxEq (last-ty X) = ft-star ∙ pp₀

--   last-var : (X : Ob (suc n)) → Tm X 0
--   getTy (last-var X) = last-ty X
--   morTm (last-var X) = ss (id X)
--   morTm₀ (last-var X) = ss₀ ∙ (id₀ ∙ ! (ft-star ∙ pp₀))
--   morTm₁ (last-var X) = ss₁ ∙ ap2-irr star (id-left' ∙ ap pp id₁) id₁
--   eqTm (last-var X) = ap-irr (λ x y → comp x (ss (id X)) y) (ap pp (ap2-irr star (! (id-left' ∙ ap pp id₁)) (! id₁))) ∙ (ss-pp {f = id X} ∙ ap id (id₀ ∙ ! (ft-star ∙ pp₀)))

--   var-unweakened : {n : ℕ} (k : Fin n) (X : Ob n) → Tm (trim k X) 0
--   var-unweakened last X = last-var X
--   var-unweakened (prev k) X = var-unweakened k (ft X)

--   weakenCTy : {X : Ob (suc n)} → Ty (ft X) 0 → Ty X 0
--   toCtx (weakenCTy {X = X} (A-ctx , A-eq)) = toCtx (star^ (pp X) (A-ctx , (A-eq ∙ ! pp₁)))
--   toCtxEq (weakenCTy A) = ft-star ∙ pp₀

--   weakenCTm : {X : Ob (suc n)} → Tm (ft X) 0 → Tm X 0
--   getTy (weakenCTm u) = weakenCTy (getTy u)
--   morTm (weakenCTm {X = X} u) = ss (comp (morTm u) (pp X) (pp₁ ∙ ! (toCtxEq (ft' (getTy u))) ∙ ! (morTm₀ u)))
--   morTm₀ (weakenCTm u) = ss₀ ∙ comp₀ ∙ pp₀ ∙ ! (toCtxEq (ft' (weakenCTy (getTy u))))
--   morTm₁ (weakenCTm u) = ss₁ ∙ ap2-irr star (! (assoc {q = morTm₁ u ∙ ! (pp₀ ∙ comp₁ ∙ morTm₁ u)}) ∙ ap2-irr comp (ap2-irr comp (ap pp (comp₁ ∙ morTm₁ u)) refl ∙ eqTm u ∙ ap id (toCtxEq (getTy u) ∙ ! pp₁)) refl ∙ id-right) (comp₁ ∙ morTm₁ u)
--   eqTm (weakenCTm {X = X} u) =
--     ap2-irr comp (ap pp (! (ap2-irr star (! (assoc {q = morTm₁ u ∙ ! (pp₀ ∙ comp₁ ∙ morTm₁ u)}) ∙ ap2-irr comp (ap2-irr comp (ap pp (comp₁ ∙ morTm₁ u)) refl ∙ eqTm u ∙ ap id (toCtxEq (getTy u) ∙ ! pp₁)) refl ∙ id-right) (comp₁ ∙ morTm₁ u)))) refl
--     ∙ ss-pp {f = comp (morTm u) (pp X) (pp₁ ∙ ! (toCtxEq (ft' (getTy u))) ∙ ! (morTm₀ u))}
--     ∙ ap id (comp₀ ∙ pp₀ ∙ ! (ft-star ∙ pp₀))

--   weakenCTm^ : (k : Fin n) {X : Ob n} → Tm (trim k X) 0 → Tm X 0
--   weakenCTm^ last x = x
--   weakenCTm^ (prev k) {X} x = weakenCTm (weakenCTm^ k x)

--   varC : (k : Fin n) (X : Ob n) → Tm X 0
--   varC k X = weakenCTm^ k (var-unweakened k X)

--   substCTy : (X : Ob n) (A : Ty X (suc m)) (u : Tm X m) (p : getTy u ≡ ft' A) → Ty X m
--   toCtx (substCTy X A u p) = star (morTm u) (toCtx A) (morTm₁ u ∙ ap toCtx p)
--   toCtxEq (substCTy {m = m} X A u p) = ap (ft^ m) (ft-star ∙ morTm₀ u) ∙ (ap (λ z → ft^ m (toCtx (ft' z))) p ∙ toCtxEq A)

--   ft-substCTy : (X : Ob n) (A : Ty X (suc m)) (u : Tm X m) (p : getTy u ≡ ft' A) → ft (toCtx (substCTy X A u p)) ≡ ft (ft (toCtx A))
--   ft-substCTy X A u p = ft-star ∙ (morTm₀ u ∙ ap ft (ap toCtx p))

--   substCTm : (X : Ob n) (v : Tm X (suc m)) (u : Tm X m) (p : getTy u ≡ ft' (getTy v)) → Tm X m
--   getTy (substCTm X v u p) = substCTy X (getTy v) u p
--   morTm (substCTm X v u p) = ss (comp (morTm v) (morTm u) (morTm₁ u ∙ (ap toCtx p ∙ ! (morTm₀ v))))
--   morTm₀ (substCTm X v u p) = ss₀ ∙ (comp₀ ∙ (morTm₀ u ∙ (ap toCtx (ap ft' p) ∙ ! (ft-substCTy X (getTy v) u p))))
--   morTm₁ (substCTm X v u p) = ss₁ ∙ (star-comp pp₁ ∙ (star-comp (morTm₁ v ∙ ! (ft-star ∙ (pp₀ ∙ (comp₁ ∙ morTm₁ v)))) ∙ ap-irr (star (morTm u)) (! (star-comp {p = morTm₁ v ∙ ! (pp₀ ∙ (comp₁ ∙ morTm₁ v))} pp₁) ∙ (ap2-irr star (ap2-irr comp (ap pp (comp₁ ∙ morTm₁ v)) refl ∙ eqTm v) (comp₁ ∙ morTm₁ v) ∙ star-id) ) ))
--   eqTm (substCTm X v u p) = ap2-irr comp (ap pp (ap2-irr star (! (! (assoc {q = morTm₁ v ∙ ! (pp₀ ∙ (comp₁ ∙ morTm₁ v))}) ∙ (ap2-irr comp (ap2-irr comp (ap pp (comp₁ {p = morTm₁ u ∙ ! (morTm₀ v ∙ ! (ap toCtx p))} ∙ morTm₁ v)) refl ∙ (eqTm v ∙ ap id (! (morTm₁ u ∙ ap toCtx p)))) refl ∙ id-right))) (! (comp₁ ∙ morTm₁ v)))) refl ∙ (ss-pp {f = comp (morTm v) (morTm u) _} ∙ ap id (comp₀ ∙ (morTm₀ u ∙ ! (ft-substCTy X (getTy v) u p ∙ ! (ap ft (ap toCtx p))))))

{- Contextual categories with structure corresponding to the type theory we are interested in -}

record StructuredCCat : Set₁ where
  field
    ccat : CCat

  open CCat ccat renaming (Mor to MorC)
  -- open M ccat

  is-section : (u : MorC n (suc n)) → Prop
  is-section u = comp (pp (∂₁ u)) u (! pp₀) ≡ id (∂₀ u)

  is-section₀ : {u : MorC n (suc n)} (us : is-section u) → ∂₀ u ≡ ft (∂₁ u)
  is-section₀ us = ! id₁ ∙ ap ∂₁ (! us) ∙ comp₁ ∙ pp₁

  field
    -- Additional structure on contextual categories
    PiStr  : (B : Ob (suc (suc n))) → Ob (suc n)
    PiStr= : {B : Ob (suc (suc n))} → ft (PiStr B) ≡ ft (ft B)

    lamStr  : (u : MorC (suc n) (suc (suc n))) (us : is-section u) → MorC n (suc n)
    lamStrs : {u : MorC (suc n) (suc (suc n))} {us : is-section u} → is-section (lamStr u us)
    lamStr₁ : {u : MorC (suc n) (suc (suc n))} {us : is-section u} → ∂₁ (lamStr u us) ≡ PiStr (∂₁ u)

  lamStr₀ : {u : MorC (suc n) (suc (suc n))} (us : is-section u) → ∂₀ (lamStr u us) ≡ ft (∂₀ u)
  lamStr₀ us = is-section₀ lamStrs ∙ ap ft lamStr₁ ∙ PiStr= ∙ ap ft (! (is-section₀ us)) 

  field
    appStr  : (B : Ob (suc (suc n))) (f : MorC n (suc n)) (fs : is-section f) (f₁ : ∂₁ f ≡ PiStr B) (a : MorC n (suc n)) (as : is-section a) (a₁ : ∂₁ a ≡ ft B) → MorC n (suc n)
    appStrs : {B : Ob (suc (suc n))} {f : MorC n (suc n)} {fs : is-section f} {f₁ : ∂₁ f ≡ PiStr B} {a : MorC n (suc n)} {as : is-section a} {a₁ : ∂₁ a ≡ ft B} → is-section (appStr B f fs f₁ a as a₁)
    appStr₁ : {B : Ob (suc (suc n))} {f : MorC n (suc n)} {fs : is-section f} {f₁ : ∂₁ f ≡ PiStr B} {a : MorC n (suc n)} {as : is-section a} {a₁ : ∂₁ a ≡ ft B} → ∂₁ (appStr B f fs f₁ a as a₁) ≡ star a B a₁

  appStr₀ : {B : Ob (suc (suc n))} {f : MorC n (suc n)} {fs : is-section f} {f₁ : ∂₁ f ≡ PiStr B} {a : MorC n (suc n)} (as : is-section a) (a₁ : ∂₁ a ≡ ft B) → ∂₀ (appStr B f fs f₁ a as a₁) ≡ ft (ft B)
  appStr₀ as a₁ = is-section₀ appStrs ∙ ap ft appStr₁ ∙ ft-star ∙ is-section₀ as ∙ ap ft a₁

  field
    UUStr  : (X : Ob n) → Ob (suc n)
    UUStr= : {X : Ob n} → ft (UUStr X) ≡ X

    ElStr  : (u : MorC n (suc n)) (us : is-section u) (u₁ : ∂₁ u ≡ UUStr (∂₀ u)) → Ob (suc n)
    ElStr= : {u : MorC n (suc n)} {us : is-section u} {u₁ : ∂₁ u ≡ UUStr (∂₀ u)} → ft (ElStr u us u₁) ≡ ∂₀ u

    -- Naturality
    PiStrNat  : {n m : ℕ} (g : MorC n m) {B : Ob (suc (suc m))} {p : ft (ft B) ≡ ∂₁ g}
              → star g (PiStr B) (! (PiStr= ∙ p)) ≡ PiStr (star (qq g (ft B) (! p)) B qq₁)
    lamStrNat : {n m : ℕ} (g : MorC n m) {u : MorC (suc m) (suc (suc m))} {us : is-section u} {p : ft (∂₀ u) ≡ ∂₁ g}
              → ss (comp (lamStr u us) g (! (lamStr₀ us ∙ p))) ≡ lamStr (ss (comp u (qq g (∂₀ u) (! p)) qq₁)) (ap2-irr comp (ap pp (ss₁ ∙ refl)) refl ∙ ss-pp ∙ ap id (comp₀ ∙ qq₀ ∙ ! (ss₀ ∙ comp₀ ∙ qq₀)))
    appStrNat : {n m : ℕ} (g : MorC n m) {B : Ob (suc (suc m))} {f : MorC m (suc m)} {fs : is-section f} {f₁ : ∂₁ f ≡ PiStr B} {a : MorC m (suc m)} {as : is-section a} {a₁ : ∂₁ a ≡ ft B} {p : ft (ft B) ≡ ∂₁ g}
              → ss (comp (appStr B f fs f₁ a as a₁) g (! (appStr₀ as a₁ ∙ p))) ≡ appStr (star (qq g (ft B) (! p)) B qq₁) (ss (comp f g (! p ∙ ! (is-section₀ fs ∙ ap ft f₁ ∙ PiStr=)))) {!!} (ss₁ ∙ {!!}) (ss (comp a g (! p ∙ ! (is-section₀ as ∙ ap ft a₁)))) {!!} (ss₁ ∙ {!!})
    UUStrNat : {n m : ℕ} (g : MorC n m) {X : Ob m} {p : X ≡ ∂₁ g}
             → star g (UUStr X) (! p ∙ ! UUStr=) ≡ UUStr (∂₀ g)
    ElStrNat : {n m : ℕ} (g : MorC n m) {u : MorC m (suc m)} {us : is-section u} {u₁ : ∂₁ u ≡ UUStr (∂₀ u)} {p : ∂₀ u ≡ ∂₁ g}
             → star g (ElStr u us u₁) (! p ∙ ! ElStr=) ≡ ElStr (ss (comp u g (! p))) {!!} {!!}


    betaStr : {u : MorC (suc n) (suc (suc n))} {us : is-section u} {a : MorC n (suc n)} {as : is-section a} {a₁ : ∂₁ a ≡ ft (∂₁ u)}
            → appStr (∂₁ u) (lamStr u us) lamStrs lamStr₁ a as a₁ ≡ ss (comp u a (a₁ ∙ ! (is-section₀ us)))

-- open StructuredCCat

-- record CCatMor (C D : CCat) : Set where
--   open CCat
--   field
--     Ob→ : Ob C n → Ob D n
--     Mor→ : Mor C n m → Mor D n m
--     ∂₀→ : {X : Mor C n m} → Ob→ (∂₀ C X) ≡ ∂₀ D (Mor→ X)
--     ∂₁→ : {X : Mor C n m} → Ob→ (∂₁ C X) ≡ ∂₁ D (Mor→ X)
--     id→ : {X : Ob C n} → Mor→ (id C X) ≡ id D (Ob→ X)
--     comp→ : {n m k : ℕ} {g : Mor C m k} {f : Mor C n m} {p : ∂₁ C f ≡ ∂₀ C g} → Mor→ (comp C g f p) ≡ comp D (Mor→ g) (Mor→ f) (! ∂₁→ ∙ (ap Ob→ p ∙ ∂₀→))
--     ft→ : {X : Ob C (suc n)} → Ob→ (ft C X) ≡ ft D (Ob→ X)
--     pp→ : {X : Ob C (suc n)} → Mor→ (pp C X) ≡ pp D (Ob→ X)
--     star→ : {n m : ℕ} {f : Mor C m n} {X : Ob C (suc n)} {p : ∂₁ C f ≡ ft C X} → Ob→ (star C f X p) ≡ star D (Mor→ f) (Ob→ X) (! ∂₁→ ∙ (ap Ob→ p ∙ ft→))
--     qq→ : {n m : ℕ} {f : Mor C m n} {X : Ob C (suc n)} {p : ∂₁ C f ≡ ft C X} → Mor→ (qq C f X p) ≡ qq D (Mor→ f) (Ob→ X) (! ∂₁→ ∙ (ap Ob→ p ∙ ft→))
--     ss→ : {f : Mor C m (suc n)} → Mor→ (ss C f) ≡ ss D (Mor→ f)
--     pt→ : Ob→ (pt C) ≡ pt D
--     ptmor→ : {X : Ob C n} → Mor→ (ptmor C X) ≡ ptmor D (Ob→ X)


-- module TyTm→ {C D : CCat} (f : CCatMor C D) where

--   open CCatMor f
--   open CCat
--   open M
  
--   ft^→ : (m : ℕ) {X : Ob C (m + n)} → Ob→ (ft^ C m X) ≡ ft^ D m (Ob→ X)
--   ft^→ zero = refl
--   ft^→ (suc m) = ft^→ m ∙ ap (ft^ D m) ft→

--   Ty→ : {X : Ob C m} → Ty C X n → Ty D (Ob→ X) n
--   toCtx (Ty→ ty) = Ob→ (toCtx ty)
--   toCtxEq (Ty→ {n = n} ty) = ! (ft^→ (suc n)) ∙ ap Ob→ (toCtxEq ty)

--   ft'→ : {X : Ob C n} (ty : Ty C X (suc m)) → Ty→ (ft' C ty) ≡ ft' D (Ty→ ty)
--   ft'→ ty = ap-irr _,_ ft→

--   Tm→ : {X : Ob C m} → Tm C X n → Tm D (Ob→ X) n
--   getTy (Tm→ tm) = Ty→ (getTy tm)
--   morTm (Tm→ tm) = Mor→ (morTm tm)
--   morTm₀ (Tm→ tm) = ! ∂₀→ ∙ (ap Ob→ (morTm₀ tm) ∙ ft→)
--   morTm₁ (Tm→ tm) = ! ∂₁→ ∙ ap Ob→ (morTm₁ tm)
--   eqTm (Tm→ tm) = ap-irr (λ x z → comp D x (Mor→ (morTm tm)) z) (! pp→) ∙ (! comp→ ∙ (ap Mor→ (eqTm tm) ∙ (id→ ∙ ap (id D) ft→)))


-- record StructuredCCatMor (C D : StructuredCCat) : Set where
--   field
--     ccat→ : CCatMor (ccat C) (ccat D)

--   open CCatMor ccat→
--   open CCat (ccat C) renaming (Ob to ObC; Mor to MorC)
--   open M (ccat C) renaming (Ty to TyC; Tm to TmC; ft' to ft'C)
--   open M (ccat D) renaming (Ty to TyD)

--   open TyTm→ ccat→

--   field
--     PiStr→ : (X : ObC n) (A : TyC X 0) (B : TyC X 1) (p : ft'C B ≡ A)
--            → Ty→ (PiStr C X A B p) ≡ PiStr D (Ob→ X) (Ty→ A) (Ty→ B) (! (ft'→ B) ∙ ap Ty→ p)
--     lamStr→ : (X : ObC n) (A : TyC X 0) (B : TyC X 1) (u : TmC X 1) (p : ft'C B ≡ A) (q : getTy u ≡ B)
--            → Tm→ (lamStr C X A B u p q) ≡ lamStr D (Ob→ X) (Ty→ A) (Ty→ B) (Tm→ u) (! (ft'→ B) ∙ ap Ty→ p) (ap Ty→ q)
--     appStr→ : (X : ObC n) (A : TyC X 0) (B : TyC X 1) (f : TmC X 0) (a : TmC X 0) (p : ft'C B ≡ A) (q : getTy f ≡ PiStr C X A B p) (r : getTy a ≡ A)
--            → Tm→ (appStr C X A B f a p q r) ≡ appStr D (Ob→ X) (Ty→ A) (Ty→ B) (Tm→ f) (Tm→ a) (! (ft'→ B) ∙ ap Ty→ p) (ap Ty→ q ∙ PiStr→ X A B p) (ap Ty→ r)
--     UUStr→ : (X : ObC n) → Ty→ (UUStr C X) ≡ UUStr D (Ob→ X)
--     ElStr→ : (X : ObC n) (v : TmC X 0) (p : getTy v ≡ UUStr C X)
--            → Ty→ (ElStr C X v p) ≡ ElStr D (Ob→ X) (Tm→ v) (ap Ty→ p ∙ UUStr→ X)
