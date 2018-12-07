{-# OPTIONS --rewriting --prop --without-K #-}

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

  ft^ : (k : Fin (suc n)) (X : Ob n) → Ob (n -F' k)
  ft^ {n} last X = X
  ft^ {zero} (prev ()) X
  ft^ {suc n} (prev k) X = ft^ {n = n} k (ft X)

  star^ : (k : Fin (suc n)) (X+ : Ob (suc (n -F' k))) (X : Ob n) (X= : ft X+ ≡ ft^ k X) → Ob (suc n)
  qq^ : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (X= : ft X+ ≡ ft^ k X) → Mor (suc n) n
  qq^₁ : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (X= : ft X+ ≡ ft^ k X) → ∂₁ (qq^ k X=) ≡ X
  qq^₀ : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (X= : ft X+ ≡ ft^ k X) → ∂₀ (qq^ k X=) ≡ star^ k X+ X X=

  star^ last X+ X X= = X+
  star^ {n = zero} (prev ()) X+ X X=
  star^ {n = suc n} (prev k) X+ X X= = star (qq^ k X=) X (qq^₁ k X=)

  qq^ last {X+ = X+} X= = pp X+
  qq^ {n = zero} (prev ()) X=
  qq^ {n = suc n} (prev k) {X = X} X= = qq (qq^ k X=) X (qq^₁ k X=)

  qq^₁ {n} last X= = pp₁ ∙ X=
  qq^₁ {zero} (prev ()) X=
  qq^₁ {suc n} (prev k) X= = qq₁

  qq^₀ last X= = pp₀
  qq^₀ {zero} (prev ()) X=
  qq^₀ {suc n} (prev k) X= = qq₀

{- Contextual categories with structure corresponding to the type theory we are interested in -}

record StructuredCCat : Set₁ where
  field
    ccat : CCat

  open CCat ccat renaming (Mor to MorC)

  {- Additional structure corresponding to type formers -}
  field
    UUStr  : (i : ℕ) (X : Ob n) → Ob (suc n)
    UUStr= : {i : ℕ} {X : Ob n} → ft (UUStr i X) ≡ X

    ElStr  : (i : ℕ) (v : MorC n (suc n)) (vs : is-section v) (v₁ : ∂₁ v ≡ UUStr i (∂₀ v)) → Ob (suc n)
    ElStr= : {i : ℕ} {v : MorC n (suc n)} {vs : is-section v} {v₁ : ∂₁ v ≡ UUStr i (∂₀ v)} → ft (ElStr i v vs v₁) ≡ ∂₀ v

    PiStr  : (B : Ob (suc (suc n))) → Ob (suc n)
    PiStr= : {B : Ob (suc (suc n))} → ft (PiStr B) ≡ ft (ft B)

    SigStr  : (B : Ob (suc (suc n))) → Ob (suc n)
    SigStr= : {B : Ob (suc (suc n))} → ft (SigStr B) ≡ ft (ft B)

    NatStr  : (X : Ob n) → Ob (suc n)
    NatStr= : {X : Ob n} → ft (NatStr X) ≡ X

    IdStr   : (a : MorC n (suc n)) (aₛ : is-section a) (b : MorC n (suc n)) (bₛ : is-section b) (p : ∂₁ a ≡ ∂₁ b) → Ob (suc n)
    IdStr=  : {a : MorC n (suc n)} {aₛ : is-section a} {b : MorC n (suc n)} {bₛ : is-section b} {p : ∂₁ a ≡ ∂₁ b} → ft (IdStr a aₛ b bₛ p) ≡ ∂₀ a

  {- Additional structure corresponding to term formers -}
  field
    uuStr  : (i : ℕ) (X : Ob n) → MorC n (suc n)
    uuStrₛ : {i : ℕ} {X : Ob n} → is-section (uuStr i X)
    uuStr₁ : {i : ℕ} {X : Ob n} → ∂₁ (uuStr i X) ≡ UUStr (suc i) X

    piStr  : (i : ℕ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i (∂₀ a)) (b : MorC (suc n) (suc (suc n))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)) → MorC n (suc n)
    piStrₛ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} → is-section (piStr i a aₛ a₁ b bₛ b₁)
    piStr₁ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} → ∂₁ (piStr i a aₛ a₁ b bₛ b₁) ≡ UUStr i (∂₀ a)

    lamStr  : (u : MorC (suc n) (suc (suc n))) (us : is-section u) → MorC n (suc n)
    lamStrs : {u : MorC (suc n) (suc (suc n))} {us : is-section u} → is-section (lamStr u us)
    lamStr₁ : {u : MorC (suc n) (suc (suc n))} {us : is-section u} → ∂₁ (lamStr u us) ≡ PiStr (∂₁ u)

    appStr  : (B : Ob (suc (suc n))) (f : MorC n (suc n)) (fs : is-section f) (f₁ : ∂₁ f ≡ PiStr B) (a : MorC n (suc n)) (as : is-section a) (a₁ : ∂₁ a ≡ ft B) → MorC n (suc n)
    appStrs : {B : Ob (suc (suc n))} {f : MorC n (suc n)} {fs : is-section f} {f₁ : ∂₁ f ≡ PiStr B} {a : MorC n (suc n)} {as : is-section a} {a₁ : ∂₁ a ≡ ft B} → is-section (appStr B f fs f₁ a as a₁)
    appStr₁ : {B : Ob (suc (suc n))} {f : MorC n (suc n)} {fs : is-section f} {f₁ : ∂₁ f ≡ PiStr B} {a : MorC n (suc n)} {as : is-section a} {a₁ : ∂₁ a ≡ ft B} → ∂₁ (appStr B f fs f₁ a as a₁) ≡ star a B a₁

    sigStr  : (i : ℕ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i (∂₀ a)) (b : MorC (suc n) (suc (suc n))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)) → MorC n (suc n)
    sigStrₛ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} → is-section (sigStr i a aₛ a₁ b bₛ b₁)
    sigStr₁ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} → ∂₁ (sigStr i a aₛ a₁ b bₛ b₁) ≡ UUStr i (∂₀ a)

    -- pair

    -- pr1

    -- pr2

    -- nat

    -- zero

    -- nat-elim

    -- id

    -- refl

  uuStr₀ : {i : ℕ} (X : Ob n) → ∂₀ (uuStr i X) ≡ X
  uuStr₀ _ = is-section₀ uuStrₛ ∙ ap ft uuStr₁ ∙ UUStr=

  piStr₀ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)) → ∂₀ (piStr i a aₛ a₁ b bₛ b₁) ≡ ∂₀ a
  piStr₀ _ = is-section₀ piStrₛ ∙ ap ft piStr₁ ∙ UUStr=

  lamStr₀ : {u : MorC (suc n) (suc (suc n))} (us : is-section u) → ∂₀ (lamStr u us) ≡ ft (∂₀ u)
  lamStr₀ us = is-section₀ lamStrs ∙ ap ft lamStr₁ ∙ PiStr= ∙ ap ft (! (is-section₀ us))

  appStr₀ : {B : Ob (suc (suc n))} {f : MorC n (suc n)} {fs : is-section f} {f₁ : ∂₁ f ≡ PiStr B} {a : MorC n (suc n)} (as : is-section a) (a₁ : ∂₁ a ≡ ft B) → ∂₀ (appStr B f fs f₁ a as a₁) ≡ ft (ft B)
  appStr₀ as a₁ = is-section₀ appStrs ∙ ap ft appStr₁ ∙ ft-star ∙ is-section₀ as ∙ ap ft a₁

  sigStr₀ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)) → ∂₀ (sigStr i a aₛ a₁ b bₛ b₁) ≡ ∂₀ a
  sigStr₀ _ = is-section₀ sigStrₛ ∙ ap ft sigStr₁ ∙ UUStr=

  {- Additional structure corresponding to naturality -}
  field
    UUStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {X : Ob m} {p : X ≡ ∂₁ g}
             → star g (UUStr i X) (! p ∙ ! UUStr=) ≡ UUStr i (∂₀ g)
    ElStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {v : MorC m (suc m)} {vs : is-section v} {v₁ : ∂₁ v ≡ UUStr i (∂₀ v)} {p : ∂₀ v ≡ ∂₁ g}
             → star g (ElStr i v vs v₁) (! p ∙ ! ElStr=) ≡ ElStr i (ss (comp v g (! p))) ss-is-section (ss-comp-section₁ vs ∙ ap2-irr star refl v₁ ∙ UUStrNat g {X = ∂₀ v} {p = p} ∙ ap (UUStr i) (! (ss₀ ∙ comp₀)) )
    PiStrNat  : {n m : ℕ} (g : MorC n m) {B : Ob (suc (suc m))} {p : ft (ft B) ≡ ∂₁ g}
              → star g (PiStr B) (! (PiStr= ∙ p)) ≡ PiStr (star (qq g (ft B) (! p)) B qq₁)
    lamStrNat : {n m : ℕ} (g : MorC n m) {u : MorC (suc m) (suc (suc m))} {us : is-section u} {p : ft (∂₀ u) ≡ ∂₁ g}
              → ss (comp (lamStr u us) g (! (lamStr₀ us ∙ p))) ≡ lamStr (ss (comp u (qq g (∂₀ u) (! p)) qq₁)) ss-is-section 
    appStrNat : {n m : ℕ} (g : MorC n m) {B : Ob (suc (suc m))} {f : MorC m (suc m)} {fs : is-section f} {f₁ : ∂₁ f ≡ PiStr B}
                {a : MorC m (suc m)} {as : is-section a} {a₁ : ∂₁ a ≡ ft B} {p : ft (ft B) ≡ ∂₁ g}
              → ss (comp (appStr B f fs f₁ a as a₁) g (! (appStr₀ as a₁ ∙ p)))
                ≡ appStr (star (qq g (ft B) (! p)) B qq₁)
                         (ss (comp f g (! (is-section₀ fs ∙ ap ft f₁ ∙ PiStr= ∙ p)))) ss-is-section (ss-comp-section₁ fs ∙ ap2-irr star refl f₁ ∙ (PiStrNat g {B = B} {p = p}))
                         (ss (comp a g (! (is-section₀ as ∙ ap ft a₁ ∙ p)))) ss-is-section (ss-comp-section₁ as ∙ ap2-irr star refl a₁ ∙ ! (ft-star ∙ qq₀))

  {- Additional structure corresponding to equality rules -}
  field
    eluuStr : (i : ℕ) (X : Ob n) → ElStr (suc i) (uuStr i X) uuStrₛ (uuStr₁ ∙ ap (UUStr (suc i)) (! (uuStr₀ _))) ≡ UUStr (suc i) X

    elpiStr : (i : ℕ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i (∂₀ a)) (b : MorC (suc n) (suc (suc n))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁))
            → ElStr i (piStr i a aₛ a₁ b bₛ b₁) piStrₛ (piStr₁ ∙ ap (UUStr i) (! (piStr₀ _))) ≡ PiStr (ElStr i b bₛ (b₁ ∙ ap (UUStr i) (! (is-section₀ bₛ ∙ ap ft b₁ ∙ UUStr=))))

    elsigStr : (i : ℕ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i (∂₀ a)) (b : MorC (suc n) (suc (suc n))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁))
            → ElStr i (sigStr i a aₛ a₁ b bₛ b₁) sigStrₛ (sigStr₁ ∙ ap (UUStr i) (! (sigStr₀ _))) ≡ SigStr (ElStr i b bₛ (b₁ ∙ ap (UUStr i) (! (is-section₀ bₛ ∙ ap ft b₁ ∙ UUStr=))))

    betaStr : {B : Ob (suc (suc n))} {u : MorC (suc n) (suc (suc n))} {us : is-section u} {u₁ : ∂₁ u ≡ B} {a : MorC n (suc n)} {as : is-section a} {a₁ : ∂₁ a ≡ ft (∂₁ u)}
            → appStr B (lamStr u us) lamStrs (lamStr₁ ∙ ap PiStr u₁) a as (a₁ ∙ ap ft u₁) ≡ ss (comp u a (a₁ ∙ ! (is-section₀ us)))

open StructuredCCat


{- Morphisms of contextual categories -}

record CCatMor (C D : CCat) : Set where
  open CCat
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


{- Morphisms of structured contextual categories -}

record StructuredCCatMor (sC sD : StructuredCCat) : Set where
  private
    C = ccat sC
    D = ccat sD

  field
    ccat→ : CCatMor C D
    
  open CCatMor ccat→
  open CCat

  preserve-section : {n : ℕ} {u : Mor C n (suc n)} (us : is-section C u) → is-section D (Mor→ u)
  preserve-section us = ! (comp→ ∙ ap2-irr (comp D) (pp→ ∙ ap (pp D) ∂₁→) refl) ∙ ap Mor→ us ∙ id→ ∙ ap (id D) ∂₀→

  field
    PiStr→  : (B : Ob C (suc (suc n))) → Ob→ (PiStr sC B) ≡ PiStr sD (Ob→ B)
    lamStr→ : (u : Mor C (suc n) (suc (suc n))) (us : is-section C u)
            → Mor→ (lamStr sC u us) ≡ lamStr sD (Mor→ u) (preserve-section us)
    appStr→ : (B : Ob C (suc (suc n))) {f : Mor C n (suc n)} (fs : is-section C f) (f₁ : ∂₁ C f ≡ PiStr sC B) {a : Mor C n (suc n)} (as : is-section C a) (a₁ : ∂₁ C a ≡ ft C B)
            → Mor→ (appStr sC B f fs f₁ a as a₁) ≡ appStr sD (Ob→ B) (Mor→ f) (preserve-section fs) ((! ∂₁→) ∙ ap Ob→ f₁ ∙ PiStr→ B) (Mor→ a) (preserve-section as) ((! ∂₁→) ∙ ap Ob→ a₁ ∙ ft→)
    UUStr→ : (i : ℕ) (X : Ob C n) → Ob→ (UUStr sC i X) ≡ UUStr sD i (Ob→ X)
    ElStr→ : (i : ℕ) (v : Mor C n (suc n)) (vs : is-section C v) (v₁ : ∂₁ C v ≡ UUStr sC i (∂₀ C v))
           → Ob→ (ElStr sC i v vs v₁) ≡ ElStr sD i (Mor→ v) (preserve-section vs) ((! ∂₁→) ∙ ap Ob→ v₁ ∙ UUStr→ i (∂₀ C v) ∙ ap (UUStr sD i) ∂₀→)


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
