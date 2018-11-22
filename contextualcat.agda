{-# OPTIONS --rewriting --prop --without-K --allow-unsolved-metas #-}

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
    qq-comp : {m n k : ℕ} {g : Mor m k} {f : Mor n m} {p : ∂₁ f ≡ ∂₀ g} {X : Ob (suc k)} (q : ∂₁ g ≡ ft X) → qq (comp g f p) X (comp₁ ∙ q) ≡ comp (qq g X q) (qq f (star g X q) (p ∙ ! ft-star)) (qq₁ ∙ ! qq₀)
    -- properties of s
    ss-pp : {m n : ℕ} {f : Mor m (suc n)} → comp (pp (star (comp (pp (∂₁ f)) f (! pp₀)) (∂₁ f) (comp₁ ∙ pp₁))) (ss f) (ss₁ ∙ ! pp₀) ≡ id (∂₀ f)
    ss-qq : {m n : ℕ} {f : Mor m (suc n)} → f ≡ comp (qq (comp (pp (∂₁ f)) f (! pp₀)) (∂₁ f) (comp₁ ∙ pp₁)) (ss f) (ss₁ ∙ ! qq₀)
    ss-comp : {m n k : ℕ} {U : Ob (suc k)} {g : Mor n k} {g₁ : ∂₁ g ≡ ft U} {f : Mor m (suc n)} {f₁ : ∂₁ f ≡ star g U g₁} → ss f ≡ ss (comp (qq g U g₁) f (! (qq₀ ∙ ! f₁)))

  {- Sections of [pp] -}

  is-section : (u : Mor n (suc n)) → Prop
  is-section u = comp (pp (∂₁ u)) u (! pp₀) ≡ id (∂₀ u)

  is-section₀ : {u : Mor n (suc n)} (us : is-section u) → ∂₀ u ≡ ft (∂₁ u)
  is-section₀ us = ! id₁ ∙ ap ∂₁ (! us) ∙ comp₁ ∙ pp₁

  ss-is-section : {f : Mor m (suc n)} → is-section (ss f)
  ss-is-section = ap2-irr comp (ap pp ss₁) refl ∙ ss-pp ∙ ap id (! ss₀)

  ss-comp-section₁ : {g : Mor m n} {f : Mor n (suc n)} (fs : is-section f) {p : ∂₁ g ≡ ∂₀ f} → ∂₁ (ss (comp f g p)) ≡ star g (∂₁ f) (p ∙ is-section₀ fs)
  ss-comp-section₁ fs {p} = ss₁ ∙ ap2-irr star (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ fs ∙ ap id (! p)) refl ∙ id-right ) comp₁

  ss-of-section : (u : Mor n (suc n)) (us : is-section u) → ss u ≡ u
  ss-of-section u us = ! (ss-qq ∙ ap2-irr comp (ap2-irr qq us refl {b' = id₁ ∙ is-section₀ us} ∙ ap2-irr qq (ap id (! (ap ft ss₁ ∙ ft-star ∙ comp₀))) (! (ss₁ ∙ ap2-irr star (us ∙ ap id (is-section₀ us)) refl ∙ star-id)) ∙ qq-id) refl ∙ id-right)


{- Terms and types -}
module M (C : CCat) where

  open CCat C

  record Ty {n : ℕ} (Γ : Ob n) : Set where
    constructor _,ft_
    field
      Ty-Ctx   : Ob (suc n)
      Ty-ft    : ft Ty-Ctx ≡ Γ
  open Ty public

  Ty= : {Γ : Ob n} {A B : Ty Γ} (p : Ty-Ctx A ≡ Ty-Ctx B) → A ≡ B
  Ty= {Γ = Γ} {record { Ty-Ctx = A ; Ty-ft = ftA}} {record { Ty-Ctx = B ; Ty-ft = ftB}} p = ap-irr _,ft_ p

  Ob-Ty : (Γ : Ob (suc n)) → Ty (ft Γ)
  Ty-Ctx (Ob-Ty Γ) = Γ
  Ty-ft (Ob-Ty Γ) = refl

  record CtxMor {n m : ℕ} (Γ : Ob n) (Δ : Ob m) : Set where
    constructor _,Mor_,_
    field
      Mor-Mor : Mor n m
      Mor₀    : ∂₀ Mor-Mor ≡ Γ
      Mor₁    : ∂₁ Mor-Mor ≡ Δ
  open CtxMor public
  
  record Tm {n : ℕ} (Γ : Ob n) (A : Ty Γ) : Set where
    field
      Tm-Mor : Mor n (suc n)
      Tmₛ    : is-section Tm-Mor
      Tm₁    : ∂₁ Tm-Mor ≡ Ty-Ctx A
    Tm₀ :  ∂₀ Tm-Mor ≡ Γ
    Tm₀ = is-section₀ Tmₛ ∙ ap ft Tm₁ ∙ Ty-ft A     
  open Tm public

  ppCtx : {Γ : Ob n} (A : Ty Γ) → CtxMor (Ty-Ctx A) Γ
  Mor-Mor (ppCtx A) = pp (Ty-Ctx A)
  Mor₀ (ppCtx A) = pp₀
  Mor₁ (ppCtx A) = pp₁ ∙ Ty-ft A

  ptmorCtx : (Γ : Ob n) (Y : Ob zero) → CtxMor Γ Y
  Mor-Mor (ptmorCtx Γ Y) = ptmor Γ
  Mor₀ (ptmorCtx Γ Y) = ptmor₀
  Mor₁ (ptmorCtx Γ Y) = ptmor₁ ∙ ! (pt-unique Y)

  compCtx : {Γ : Ob n} {Δ : Ob m} {Θ : Ob k} (θ : CtxMor Δ Θ) (δ : CtxMor Γ Δ) → CtxMor Γ Θ
  Mor-Mor (compCtx θ δ) = comp (Mor-Mor θ) (Mor-Mor δ) (Mor₁ δ ∙ ! (Mor₀ θ))
  Mor₀ (compCtx θ δ) = comp₀ ∙ Mor₀ δ
  Mor₁ (compCtx θ δ) = comp₁ ∙ Mor₁ θ

  qqCtx : {Γ : Ob n} (Δ : Ob (suc m)) (δ : CtxMor Γ (ft Δ)) → CtxMor (star (Mor-Mor δ) Δ (Mor₁ δ)) Δ
  Mor-Mor (qqCtx Δ δ) = qq (Mor-Mor δ) Δ (Mor₁ δ)
  Mor₀ (qqCtx Δ δ) = qq₀
  Mor₁ (qqCtx Δ δ) = qq₁

  apTm : {Γ : Ob n} {A B : Ty Γ} (p : A ≡ B) → Tm Γ A → Tm Γ B
  Tm-Mor (apTm p tm) = Tm-Mor tm
  Tmₛ (apTm p tm) = Tmₛ tm
  Tm₁ (apTm p tm) = Tm₁ tm ∙ ap Ty-Ctx p

  Tm-CtxMor : {Γ : Ob n} {A : Ty Γ} (u : Tm Γ A) → CtxMor Γ (Ty-Ctx A)
  Mor-Mor (Tm-CtxMor u) = Tm-Mor u
  Mor₀ (Tm-CtxMor u) = Tm₀ u
  Mor₁ (Tm-CtxMor u) = Tm₁ u

  starTy : {Δ : Ob m} (A : Ty Δ) {Γ : Ob n} (g : CtxMor Γ Δ) → Ty Γ
  Ty-Ctx (starTy A g) = star (Mor-Mor g) (Ty-Ctx A) (Mor₁ g ∙ ! (Ty-ft A))
  Ty-ft (starTy A g) = ft-star ∙ (Mor₀ g)

  substTy : {Γ : Ob n} {A : Ty Γ} (B : Ty (Ty-Ctx A)) (u : Tm Γ A) → Ty Γ
  substTy A u = starTy A (Tm-CtxMor u)

  starTm : {Δ : Ob m} {A : Ty Δ} (u : Tm Δ A) {Γ : Ob n} (g : CtxMor Γ Δ) → Tm Γ (starTy A g)
  Tm-Mor (starTm u g) = ss (comp (Tm-Mor u) (Mor-Mor g) (Mor₁ g ∙ ! (Tm₀ u)))
  Tmₛ (starTm u g) = ss-is-section
  Tm₁ (starTm u g) = ss-comp-section₁ (Tmₛ u) ∙ ap2-irr star refl (Tm₁ u)

  substTm : {Γ : Ob n} {A : Ty Γ} {B : Ty (Ty-Ctx A)} (v : Tm (Ty-Ctx A) B) (u : Tm Γ A)  → Tm Γ (substTy B u)
  substTm v u = starTm v (Tm-CtxMor u)

  qqCtxMor : {Δ : Ob m} (A : Ty Δ) {Γ : Ob n} (g : CtxMor Γ Δ) → CtxMor (star (Mor-Mor g) (Ty-Ctx A) (Mor₁ g ∙ ! (Ty-ft A))) (Ty-Ctx A)
  Mor-Mor (qqCtxMor A g) = (qq (Mor-Mor g) (Ty-Ctx A) (Mor₁ g ∙ ! (Ty-ft A)))
  Mor₀ (qqCtxMor A g) = qq₀
  Mor₁ (qqCtxMor A g) = qq₁
  
  substTyqqCtx : {Δ : Ob m} (A : Ty Δ) (B : Ty (Ty-Ctx A)) (u : Tm Δ A) {Γ : Ob n} (g : CtxMor Γ Δ)  → substTy (starTy B (qqCtxMor A g)) (starTm u g) ≡  starTy (substTy B u) g
  substTyqqCtx A'@record { Ty-Ctx = A ; Ty-ft = ftA} B'@record { Ty-Ctx = B ; Ty-ft = ftB} u g  = Ty= (! (star-comp {p = ss₁ ∙ ! (qq₀ ∙ ap2-irr star (! (! (assoc {q = Tm₁ {A = A'} u ∙ ! (pp₀ ∙ comp₁ ∙ (Tm₁ u))}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ (Tmₛ u) ∙ ap id (Tm₀ {A = A'} u ∙ ! (Mor₁ g))) refl ∙ id-right)) (! (comp₁ ∙ (Tm₁ u))))} (qq₁ ∙ ! ftB)) ∙ ap2-irr star (ap2-irr comp (! (ap2-irr qq (! (assoc {q = Tm₁ {A = A'} u ∙ ! (pp₀ ∙ comp₁ ∙ (Tm₁ u))}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ (Tmₛ u) ∙ ap id (Tm₀ {A = A'} u ∙ ! (Mor₁ g))) refl ∙ id-right) (comp₁ ∙ (Tm₁ u)))) refl ∙ ! ss-qq) refl ∙ star-comp (Tm₁ u ∙ ! ftB))

  weakenTy : {Γ : Ob n} (A B : Ty Γ) → Ty (Ty-Ctx B)
  weakenTy A B = starTy A (ppCtx B)

  trim : (k : Fin n) (X : Ob n) → Ob (n -F k)
  trim last X = X
  trim (prev k) X = trim k (ft X)
  
  weakenTy^ : (k : Fin n) {Γ : Ob n} (A : Ty (trim k Γ)) → Ty Γ
  weakenTy^ last A = A
  weakenTy^ (prev k) A = weakenTy (weakenTy^ k A) (Ob-Ty _)

  Ty-at : (k : Fin n) (Γ : Ob n)  → Ty (trim k Γ)
  Ty-at k Γ = (starTy (Ob-Ty (trim k Γ)) (ppCtx (Ob-Ty (trim k Γ))))

  var-unweaken : (k : Fin n) (Γ : Ob n) → Tm (trim k Γ) (Ty-at k Γ)
  Tm-Mor (var-unweaken last Γ) = ss (id Γ)
  Tmₛ (var-unweaken last Γ) = ss-is-section
  Tm₁ (var-unweaken last Γ) = ss₁ ∙ ap2-irr star (ap2-irr comp (ap pp id₁) (ap id (! pp₀)) ∙ id-left) id₁
  Tm-Mor (var-unweaken (prev k) Γ) = ss (Tm-Mor (var-unweaken k (ft Γ)))
  Tmₛ (var-unweaken (prev k) Γ) = ss-is-section
  Tm₁ (var-unweaken (prev k) Γ) = ss₁ ∙ ap2-irr star (ap2-irr comp (ap pp (Tm₁ (var-unweaken k (ft Γ)) ∙ ! (Tm₁ (var-unweaken k (ft Γ))))) refl ∙ (Tmₛ (var-unweaken k (ft Γ))) ∙ ap id (! (ft-star ∙ pp₀ ∙ ! (Tm₀ (var-unweaken k (ft Γ)))))) (Tm₁ (var-unweaken k (ft Γ))) ∙ star-id

  weakenTm : {Γ : Ob n} (A : Ty Γ) (u : Tm Γ A) (B : Ty Γ) → Tm (Ty-Ctx B) (weakenTy A B)
  weakenTm A u B = starTm u (ppCtx B)

  weakenTm^ : (k : Fin n) {Γ : Ob n} {A : Ty (trim k Γ)} (u : Tm (trim k Γ) A) → Tm Γ (weakenTy^ k A)
  weakenTm^ last u = u 
  weakenTm^ (prev k) {Γ} {A} u = weakenTm (weakenTy^ k A) (weakenTm^ k u) (Ob-Ty Γ)
  
  varStr : (k : Fin n) (Γ : Ob n) (Y : Ty Γ) (p : Y ≡ weakenTy^ k (Ty-at k Γ)) → Tm Γ Y
  varStr k Γ Y p  = apTm (! p) (weakenTm^ k (var-unweaken k Γ))



{- Contextual categories with structure corresponding to the type theory we are interested in -}

record StructuredCCat : Set₁ where
  field
    ccat : CCat

  open CCat ccat renaming (Mor to MorC)
  open M ccat
  
  field
    -- Additional structure on contextual categories
    PiStr : (Γ : Ob n) (A : Ty Γ) (B : Ty (Ty-Ctx A)) → Ty Γ
    lamStr : (Γ : Ob n) (A : Ty Γ) (B : Ty (Ty-Ctx A)) (u : Tm (Ty-Ctx A) B) (C : Ty Γ) (p : C ≡ PiStr Γ A B) → Tm Γ C
    appStr : (Γ : Ob n) (A : Ty Γ) (B : Ty (Ty-Ctx A)) (f : Tm Γ (PiStr Γ A B)) (a : Tm Γ A) (C : Ty Γ) (p : C ≡ substTy B a) → Tm Γ C
    UUStr : (Γ : Ob n) {-(i : ℕ)-} → Ty Γ
    ElStr : (Γ : Ob n) {-(i : ℕ)-} (v : Tm Γ (UUStr Γ {-i-})) → Ty Γ

    -- Naturality

    PiStrNat  : {Δ : Ob m} {A : Ty Δ} {B : Ty (Ty-Ctx A)} {Γ : Ob n} (g : CtxMor Γ Δ) → PiStr Γ (starTy A g) (starTy B (qqCtxMor A g)) ≡ starTy (PiStr Δ A B) g 
    lamStrNat : {Δ : Ob m} {A : Ty Δ} {B : Ty (Ty-Ctx A)} {u : Tm (Ty-Ctx A) B} {C : Ty Δ} (p : C ≡ PiStr Δ A B) {Γ : Ob n} (g : CtxMor Γ Δ) → lamStr Γ (starTy A g) (starTy B (qqCtxMor A g)) (starTm u (qqCtxMor A g)) (starTy C g) (ap (λ x → starTy x g) p ∙ ! (PiStrNat g)) ≡ starTm (lamStr Δ A B u C p) g
    appStrNat : {Δ : Ob m} {A : Ty Δ} {B : Ty (Ty-Ctx A)} {f : Tm Δ (PiStr Δ A B)} {a : Tm Δ A} {C : Ty Δ} {p : C ≡ substTy B a} {Γ : Ob n} (g : CtxMor Γ Δ) → appStr Γ (starTy A g) (starTy B (qqCtxMor A g)) (apTm (! (PiStrNat g)) (starTm f g)) (starTm a g) (starTy C g) (ap (λ x → starTy x g) p ∙ ! (substTyqqCtx A B a g)) ≡ starTm (appStr Δ A B f a C p) g
    UUStrNat : {Δ : Ob m} {-(i : ℕ)-} {Γ : Ob n} (g : CtxMor Γ Δ) → UUStr {-i-} Γ ≡ starTy (UUStr {-i-} Δ) g
    ElStrNat : {Δ : Ob m} {-(i : ℕ)-} {v : Tm Δ (UUStr Δ {-i-})} {Γ : Ob n} (g : CtxMor Γ Δ) → ElStr Γ (apTm (! (UUStrNat g)) (starTm v g)) ≡ starTy (ElStr Δ v) g
    
    betaStr : {Γ : Ob m} {A : Ty Γ} {B : Ty (Ty-Ctx A)} {u : Tm (Ty-Ctx A) B} {a : Tm Γ A} → appStr Γ A B (lamStr Γ A B u (PiStr Γ A B) refl) a (substTy B a) refl ≡ substTm u a

-- -- --     betaStr : {u : MorC (suc n) (suc (suc n))} {us : is-section u} {a : MorC n (suc n)} {as : is-section a} {a₁ : ∂₁ a ≡ ft (∂₁ u)}
-- -- --             → appStr (∂₁ u) (lamStr u us) lamStrs lamStr₁ a as a₁ ≡ ss (comp u a (a₁ ∙ ! (is-section₀ us)))
--     lamStr : (Γ : Ob n) (A : Ob (suc n)) (B : Ob (suc (suc n))) (u : MorC (suc n) (suc (suc n))) (uₛ : is-section u) (ftA : ft A ≡ Γ) (ftB : ft B ≡ A) (u₁ : ∂₁ u ≡ B) → MorC n (suc n)
--     lamStrₛ : {Γ : Ob n} {A : Ob (suc n)} {B : Ob (suc (suc n))} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {ftA : ft A ≡ Γ} {ftB : ft B ≡ A} {u₁ : ∂₁ u ≡ B} → is-section (lamStr Γ A B u uₛ ftA ftB u₁)
--     lamStr₁ : {Γ : Ob n} {A : Ob (suc n)} {B : Ob (suc (suc n))} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {ftA : ft A ≡ Γ} {ftB : ft B ≡ A} {u₁ : ∂₁ u ≡ B} → ∂₁ (lamStr Γ A B u uₛ ftA ftB u₁) ≡ PiStr Γ A B ftA ftB

--   lamStr₀ : {Γ : Ob n} {A : Ob (suc n)} {B : Ob (suc (suc n))} {u : MorC (suc n) (suc (suc n))} (uₛ : is-section u) {ftA : ft A ≡ Γ} {ftB : ft B ≡ A} {u₁ : ∂₁ u ≡ B} → ∂₀ (lamStr Γ A B u uₛ ftA ftB u₁) ≡ Γ
--   lamStr₀ us = is-section₀ lamStrₛ ∙ ap ft lamStr₁ ∙ PiStr= -- is-section₀ lamStrₛ ∙ ap ft lamStr₁ ∙ PiStr=

--   field
--     appStr  : (Γ : Ob n) (A : Ob (suc n)) (B : Ob (suc (suc n))) (f : MorC n (suc n)) (fₛ : is-section f) (a : MorC n (suc n)) (aₛ : is-section a) (ftA : ft A ≡ Γ) (ftB : ft B ≡ A) (f₁ : ∂₁ f ≡ PiStr Γ A B ftA ftB) (a₁ : ∂₁ a ≡ A) → MorC n (suc n)
--     appStrₛ : {Γ : Ob n} {A : Ob (suc n)} {B : Ob (suc (suc n))} {f : MorC n (suc n)} {fₛ : is-section f} {a : MorC n (suc n)} {aₛ : is-section a} {ftA : ft A ≡ Γ} {ftB : ft B ≡ A} {f₁ : ∂₁ f ≡ PiStr Γ A B ftA ftB} {a₁ : ∂₁ a ≡ A} → is-section (appStr Γ A B f fₛ a aₛ ftA ftB f₁ a₁)
--     appStr₁ : {Γ : Ob n} {A : Ob (suc n)} {B : Ob (suc (suc n))} {f : MorC n (suc n)} {fₛ : is-section f} {a : MorC n (suc n)} {aₛ : is-section a} {ftA : ft A ≡ Γ} {ftB : ft B ≡ A} {f₁ : ∂₁ f ≡ PiStr Γ A B ftA ftB} {a₁ : ∂₁ a ≡ A} → ∂₁ (appStr Γ A B f fₛ a aₛ ftA ftB f₁ a₁) ≡ star a B (a₁ ∙ ! ftB) 
 
--   appStr₀ : {Γ : Ob n} {A : Ob (suc n)} {B : Ob (suc (suc n))} {f : MorC n (suc n)} (fₛ : is-section f) {a : MorC n (suc n)} (aₛ : is-section a) (ftA : ft A ≡ Γ) {ftB : ft B ≡ A} {f₁ : ∂₁ f ≡ PiStr Γ A B ftA ftB} (a₁ : ∂₁ a ≡ A) → ∂₀ (appStr Γ A B f fₛ a aₛ ftA ftB f₁ a₁) ≡ Γ
--   appStr₀ fₛ aₛ ftA a₁ = is-section₀ appStrₛ ∙ ap ft appStr₁ ∙ ft-star ∙ is-section₀ aₛ ∙ ap ft a₁ ∙ ftA
 
--   field
--     UUStr  : (Γ : Ob n) → Ob (suc n)
--     UUStr= : {Γ : Ob n} → ft (UUStr Γ) ≡ Γ

--     ElStr  : (Γ : Ob n) (v : MorC n (suc n)) (vₛ : is-section v) (v₁ : ∂₁ v ≡ UUStr Γ) → Ob (suc n)
--     ElStr= : {Γ : Ob n} {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ UUStr Γ} → ft (ElStr Γ v vₛ v₁) ≡ Γ

--     -- Naturality
--     PiStrNat  : {Γ : Ob n} {A : Ob (suc n)} {B : Ob (suc (suc n))} (ftA : ft A ≡ Γ) (ftB : ft B ≡ A) {Δ : Ob m} (g : MorC m n) (g₁ : ∂₁ g ≡ Γ) (g₀ : ∂₀ g ≡ Δ)
--               → star g (PiStr Γ A B ftA ftB) (g₁ ∙ ! PiStr=) ≡ PiStr Δ (star g A (g₁ ∙ ! ftA)) (star (qq g A (g₁ ∙ ! ftA)) B (qq₁ ∙ ! ftB)) (ft-star ∙ g₀) (ft-star ∙ qq₀)
-- --     lamStrNat : {n m : ℕ} (g : MorC n m) {u : MorC (suc m) (suc (suc m))} {us : is-section u} {p : ft (∂₀ u) ≡ ∂₁ g}
-- --               → ss (comp (lamStr u us) g (! (lamStr₀ us ∙ p))) ≡ lamStr (ss (comp u (qq g (∂₀ u) (! p)) qq₁)) ss-is-section 
-- --     appStrNat : {n m : ℕ} (g : MorC n m) {B : Ob (suc (suc m))} {f : MorC m (suc m)} {fs : is-section f} {f₁ : ∂₁ f ≡ PiStr B}
-- --                 {a : MorC m (suc m)} {as : is-section a} {a₁ : ∂₁ a ≡ ft B} {p : ft (ft B) ≡ ∂₁ g}
-- --               → ss (comp (appStr B f fs f₁ a as a₁) g (! (appStr₀ as a₁ ∙ p)))
-- --                 ≡ appStr (star (qq g (ft B) (! p)) B qq₁)
-- --                          (ss (comp f g (! (is-section₀ fs ∙ ap ft f₁ ∙ PiStr= ∙ p)))) ss-is-section (ss-comp-section₁ fs ∙ ap2-irr star refl f₁ ∙ (PiStrNat g {B = B} {p = p}))
-- --                          (ss (comp a g (! (is-section₀ as ∙ ap ft a₁ ∙ p)))) ss-is-section (ss-comp-section₁ as ∙ ap2-irr star refl a₁ ∙ ! (ft-star ∙ qq₀))
-- --     UUStrNat : {n m : ℕ} (g : MorC n m) {X : Ob m} {p : X ≡ ∂₁ g}
-- --              → star g (UUStr X) (! p ∙ ! UUStr=) ≡ UUStr (∂₀ g)
-- --     ElStrNat : {n m : ℕ} (g : MorC n m) {v : MorC m (suc m)} {vs : is-section v} {v₁ : ∂₁ v ≡ UUStr (∂₀ v)} {p : ∂₀ v ≡ ∂₁ g}
-- --              → star g (ElStr v vs v₁) (! p ∙ ! ElStr=) ≡ ElStr (ss (comp v g (! p))) ss-is-section (ss-comp-section₁ vs ∙ ap2-irr star refl v₁ ∙ UUStrNat g {X = ∂₀ v} {p = p} ∙ ap UUStr (! (ss₀ ∙ comp₀)) )


-- -- --     betaStr : {u : MorC (suc n) (suc (suc n))} {us : is-section u} {a : MorC n (suc n)} {as : is-section a} {a₁ : ∂₁ a ≡ ft (∂₁ u)}
-- -- --             → appStr (∂₁ u) (lamStr u us) lamStrs lamStr₁ a as a₁ ≡ ss (comp u a (a₁ ∙ ! (is-section₀ us)))

open StructuredCCat


{- Morphisms of contextual categories -}

record CCatMor (C D : CCat) : Set where
  open CCat
  open M 
  
  field
    Ob→ : Ob C n → Ob D n
    Mor→ : Mor C n m → Mor D n m
    ∂₀→ : {X : Mor C n m} → Ob→ (∂₀ C X) ≡ ∂₀ D (Mor→ X)
    ∂₁→ : {X : Mor C n m} → Ob→ (∂₁ C X) ≡ ∂₁ D (Mor→ X)
    id→ : {X : Ob C n} → Mor→ (id C X) ≡ id D (Ob→ X)
    comp→ : {n m k : ℕ} {g : Mor C m k} {f : Mor C n m} {p : ∂₁ C f ≡ ∂₀ C g} → Mor→ (comp C g f p) ≡ comp D (Mor→ g) (Mor→ f) (! ∂₁→ ∙ (ap Ob→ p ∙ ∂₀→))
    ft→ : {X : Ob C (suc n)} → Ob→ (ft C X) ≡ ft D (Ob→ X)
    pp→ : {X : Ob C (suc n)} → Mor→ (pp C X) ≡ pp D (Ob→ X)
    star→ : {n m : ℕ} {f : Mor C m n} {X : Ob C (suc n)} {p : ∂₁ C f ≡ ft C X} → Ob→ (star C f X p) ≡ star D (Mor→ f) (Ob→ X) (! ∂₁→ ∙ (ap Ob→ p ∙ ft→))
    qq→ : {n m : ℕ} {f : Mor C m n} {X : Ob C (suc n)} {p : ∂₁ C f ≡ ft C X} → Mor→ (qq C f X p) ≡ qq D (Mor→ f) (Ob→ X) (! ∂₁→ ∙ (ap Ob→ p ∙ ft→))
    ss→ : {f : Mor C m (suc n)} → Mor→ (ss C f) ≡ ss D (Mor→ f)
    pt→ : Ob→ (pt C) ≡ pt D
    ptmor→ : {X : Ob C n} → Mor→ (ptmor C X) ≡ ptmor D (Ob→ X)

  Ty→ : {Γ : Ob C n} → Ty C Γ → Ty D (Ob→ Γ)
  Ty-Ctx (Ty→ A) = Ob→ (Ty-Ctx A)
  Ty-ft (Ty→ A) = ! ft→ ∙ ap Ob→ (Ty-ft A)
  
  preserve-section : {n : ℕ} {u : Mor C n (suc n)} (us : is-section C u) → is-section D (Mor→ u)
  preserve-section us = ! (comp→ ∙ ap2-irr (comp D) (pp→ ∙ ap (pp D) ∂₁→) refl) ∙ ap Mor→ us ∙ id→ ∙ ap (id D) ∂₀→

  Tm→ : {Γ : Ob C n} {A : Ty C Γ} → Tm C Γ A → Tm D (Ob→ Γ) (Ty→ A)
  Tm-Mor (Tm→ u) = Mor→ (Tm-Mor u)
  Tmₛ (Tm→ u) = preserve-section (Tmₛ u)
  Tm₁ (Tm→ u) = ! ∂₁→ ∙ ap Ob→ (Tm₁ u)

  substTy→ : {Γ : Ob C n} {A : Ty C Γ} (B : Ty C (Ty-Ctx A)) (a : Tm C Γ A) → substTy D (Ty→ B) (Tm→ a) ≡  Ty→ (substTy C B a)
  substTy→ B a = Ty= D (! star→)
  
{- Morphisms of structured contextual categories -}

record StructuredCCatMor (sC sD : StructuredCCat) : Set where
  private
    C = ccat sC
    D = ccat sD

  field
    ccat→ : CCatMor C D
    
  open CCatMor ccat→
  open CCat
  open M


  field
    PiStr→ : (Γ : Ob C n) (A : Ty C Γ) (B : Ty C (Ty-Ctx A)) → PiStr sD (Ob→ Γ) (Ty→ A) (Ty→ B) ≡ Ty→ (PiStr sC Γ A B)
    lamStr→ : (Γ : Ob C n) (A : Ty C Γ) (B : Ty C (Ty-Ctx A)) (u : Tm C (Ty-Ctx A) B) (Y : Ty C Γ) (p : Y ≡ PiStr sC Γ A B) →  lamStr sD (Ob→ Γ) (Ty→ A) (Ty→ B) (Tm→ u) (Ty→ Y) (ap Ty→ p ∙  ! (PiStr→ Γ A B)) ≡ Tm→ (lamStr sC Γ A B u Y p) 
    appStr→ : (Γ : Ob C n) (A : Ty C Γ) (B : Ty C (Ty-Ctx A)) (f : Tm C Γ (PiStr sC Γ A B)) (a : Tm C Γ A) (Y : Ty C Γ) (p : Y ≡ substTy C B a) → appStr sD (Ob→ Γ) (Ty→ A) (Ty→ B) (apTm D (! (PiStr→ Γ A B)) (Tm→ f)) (Tm→ a) (Ty→ Y) (ap Ty→ p ∙ ! (substTy→ B a)) ≡ Tm→ (appStr sC Γ A B f a Y p)
    UUStr→ : (Γ : Ob C n) {-(i : ℕ)-} → UUStr sD (Ob→ Γ) ≡ Ty→ (UUStr sC Γ)
    ElStr→ : (Γ : Ob C n) {-(i : ℕ)-} (v : Tm C Γ (UUStr sC Γ {-i-})) → ElStr sD (Ob→ Γ) (apTm D (! (UUStr→ Γ)) (Tm→ v)) ≡ Ty→ (ElStr sC Γ v)
  
  -- field
  --   PiStr→  : (B : Ob C (suc (suc n))) → Ob→ (PiStr sC B) ≡ PiStr sD (Ob→ B)
  --   lamStr→ : (u : Mor C (suc n) (suc (suc n))) (us : is-section C u)
  --           → Mor→ (lamStr sC u us) ≡ lamStr sD (Mor→ u) (preserve-section us)
  --   appStr→ : (B : Ob C (suc (suc n))) {f : Mor C n (suc n)} (fs : is-section C f) (f₁ : ∂₁ C f ≡ PiStr sC B) {a : Mor C n (suc n)} (as : is-section C a) (a₁ : ∂₁ C a ≡ ft C B)
  --           → Mor→ (appStr sC B f fs f₁ a as a₁) ≡ appStr sD (Ob→ B) (Mor→ f) (preserve-section fs) ((! ∂₁→) ∙ ap Ob→ f₁ ∙ PiStr→ B) (Mor→ a) (preserve-section as) ((! ∂₁→) ∙ ap Ob→ a₁ ∙ ft→)
  --   UUStr→ : (X : Ob C n) → Ob→ (UUStr sC X) ≡ UUStr sD (Ob→ X)
  --   ElStr→ : (v : Mor C n (suc n)) (vs : is-section C v) (v₁ : ∂₁ C v ≡ UUStr sC (∂₀ C v))
  --          → Ob→ (ElStr sC v vs v₁) ≡ ElStr sD (Mor→ v) (preserve-section vs) ((! ∂₁→) ∙ ap Ob→ v₁ ∙ UUStr→ (∂₀ C v) ∙ ap (UUStr sD) ∂₀→)


module _ {sC sD : StructuredCCat} where
  open StructuredCCatMor
  open CCatMor
  open CCat

  {- Equalities between morphisms between structured contextual categories -}

  structuredCCatMorEq : {f g : StructuredCCatMor sC sD}
                      → ({n : ℕ} (X : Ob (ccat sC) n) → Ob→ (ccat→ f) X ≡ Ob→ (ccat→ g) X)
                      → ({n m : ℕ} (X : Mor (ccat sC) n m) → Mor→ (ccat→ f) X ≡ Mor→ (ccat→ g) X)
                      → f ≡ g
  structuredCCatMorEq h k = lemma (funextI (λ n → funext h)) (funextI (λ n → funextI (λ m → funext k)))  where

    lemma : {f g : StructuredCCatMor sC sD}
            → ((λ {n} → Ob→ (ccat→ f) {n}) ≡ (λ {n} → Ob→ (ccat→ g) {n}))
            → ((λ {n m} → Mor→ (ccat→ f) {n} {m}) ≡ (λ {n m} → Mor→ (ccat→ g) {n} {m}))
            → f ≡ g
    lemma refl refl = refl
