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

  is-section₀ : {u : Mor n (suc n)} {X : Ob (suc n)} (uₛ : is-section u) (u₁ : ∂₁ u ≡ X) → ∂₀ u ≡ ft X
  is-section₀ uₛ u₁ = ! id₁ ∙ ap ∂₁ (! uₛ) ∙ comp₁ ∙ pp₁ ∙ ap ft u₁

  ssₛ : {f : Mor m (suc n)} → is-section (ss f)
  ssₛ = ap2-irr comp (ap pp ss₁) refl ∙ ss-pp ∙ ap id (! ss₀)

  ss-comp-section₁ : {g : Mor m n} {f : Mor n (suc n)} (fₛ : is-section f) {p : ∂₁ g ≡ ∂₀ f} → ∂₁ (ss (comp f g p)) ≡ star g (∂₁ f) (p ∙ is-section₀ fₛ refl)
  ss-comp-section₁ fₛ {p} = ss₁ ∙ ap2-irr star (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ fₛ ∙ ap id (! p)) refl ∙ id-right ) comp₁

  ss-of-section : (u : Mor n (suc n)) (uₛ : is-section u) → ss u ≡ u
  ss-of-section u uₛ = ! (ss-qq ∙ ap2-irr comp (ap2-irr qq uₛ refl {b' = id₁ ∙ is-section₀ uₛ refl} ∙ ap2-irr qq (ap id (! (ap ft ss₁ ∙ ft-star ∙ comp₀))) (! (ss₁ ∙ ap2-irr star (uₛ ∙ ap id (is-section₀ uₛ refl)) refl ∙ star-id)) ∙ qq-id) refl ∙ id-right)

  {- Iterated father and qq operations -}

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

  {- Other helper functions -}

  ss₁' : {f : Mor m (suc n)} {X : Ob (suc n)} (p : ∂₁ f ≡ X) → ∂₁ (ss f) ≡ star (comp (pp X) f (p ∙ ! pp₀)) X (comp₁ ∙ pp₁)
  ss₁' refl = ss₁

  id-left' : {f : Mor n m} {X : Ob n} (p : ∂₀ f ≡ X) → comp f (id X) (id₁ ∙ ! p) ≡ f
  id-left' refl = id-left

  star+ : (g : Mor n m) (A : Ob (suc (suc m))) (A= : ft (ft A) ≡ ∂₁ g) → Ob (suc (suc n))
  star+ g A A= = star (qq g (ft A) (! A=)) A qq₁

  starTm : (g : Mor n m) (u : Mor m (suc m)) (u₀ : ∂₀ u ≡ ∂₁ g) → Mor n (suc n)
  starTm g u u₀ = ss (comp u g (! u₀))

  starTm₁ : {g : Mor n m} {u : Mor m (suc m)} (uₛ : is-section u) (u₀ : ∂₀ u ≡ ∂₁ g) {X : Ob (suc m)} (p : ∂₁ u ≡ X) → ∂₁ (starTm g u u₀) ≡ star g X (! u₀ ∙ is-section₀ uₛ p)
  starTm₁ uₛ u₀ p = ss₁' comp₁ ∙ ap2-irr star (! (assoc {q = ! pp₀}) ∙ ap2-irr comp (uₛ ∙ ap id u₀) refl ∙ id-right) p

  starTm+ : (g : Mor n m) (u : Mor (suc m) (suc (suc m))) (p : ft (∂₀ u) ≡ ∂₁ g) → Mor (suc n) (suc (suc n))
  starTm+ g u p = ss (comp u (qq g (∂₀ u) (! p)) qq₁)

  starTm+₁ : (g : Mor n m) (u : Mor (suc m) (suc (suc m))) (uₛ : is-section u) {X : Ob (suc (suc m))} (u₁ : ∂₁ u ≡ X) (p : ft (∂₀ u) ≡ ∂₁ g) → ∂₁ (starTm+ g u p) ≡ star+ g X (ap ft (! (is-section₀ uₛ u₁)) ∙ p)
  starTm+₁ g u uₛ u₁ p = starTm₁ uₛ (! qq₁) u₁ ∙ ap2-irr star (ap2-irr qq refl (is-section₀ uₛ u₁)) refl

  starstar : (g : Mor n m) (a : Mor m (suc m)) (aₛ : is-section a) (B : Ob (suc (suc m))) {a₁ : ∂₁ a ≡ ft B} {g₁ : ∂₁ g ≡ ft (star a B a₁)} {a₀ : ∂₀ a ≡ ∂₁ g} {p : ft (ft B) ≡ ∂₁ g} → star g (star a B a₁) g₁ ≡ star (starTm g a a₀) (star+ g B p) (starTm₁ aₛ a₀ a₁ ∙ ap2-irr star refl refl ∙ ! qq₀ ∙ ! ft-star)
  starstar g a aₛ B {a₁} {g₁} {a₀} {p} = ! (star-comp {p = ! a₀} a₁) ∙ ap2-irr star (ss-qq ∙ ap2-irr comp (ap2-irr qq (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ aₛ ∙ ap id a₀) refl ∙ id-right) (comp₁ ∙ a₁)) refl) refl ∙ star-comp {p = starTm₁ aₛ a₀ a₁ ∙ ap2-irr star refl refl ∙ ! qq₀} qq₁


{- Contextual categories with structure corresponding to the type theory we are interested in -}

record StructuredCCat : Set₁ where
  field
    ccat : CCat

  open CCat ccat renaming (Mor to MorC)

  {- Additional structure corresponding to type formers -}
  field
    UUStr  : (i : ℕ) (X : Ob n) → Ob (suc n)
    UUStr= : {i : ℕ} {X : Ob n} → ft (UUStr i X) ≡ X

    ElStr  : (i : ℕ) (v : MorC n (suc n)) (vₛ : is-section v) (v₁ : ∂₁ v ≡ UUStr i (∂₀ v)) → Ob (suc n)
    ElStr= : {i : ℕ} {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ UUStr i (∂₀ v)} → ft (ElStr i v vₛ v₁) ≡ ∂₀ v

    PiStr  : (B : Ob (suc (suc n))) → Ob (suc n)
    PiStr= : {B : Ob (suc (suc n))} → ft (PiStr B) ≡ ft (ft B)

    SigStr  : (B : Ob (suc (suc n))) → Ob (suc n)
    SigStr= : {B : Ob (suc (suc n))} → ft (SigStr B) ≡ ft (ft B)

    NatStr  : (X : Ob n) → Ob (suc n)
    NatStr= : {X : Ob n} → ft (NatStr X) ≡ X

    IdStr   : (A : Ob (suc n)) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) (b : MorC n (suc n)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ A) → Ob (suc n)
    IdStr=  : {A : Ob (suc n)} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} → ft (IdStr A a aₛ a₁ b bₛ b₁) ≡ ft A

  {- Additional structure corresponding to term formers -}
  field
    uuStr  : (i : ℕ) (X : Ob n) → MorC n (suc n)
    uuStrₛ : {i : ℕ} {X : Ob n} → is-section (uuStr i X)
    uuStr₁ : {i : ℕ} {X : Ob n} → ∂₁ (uuStr i X) ≡ UUStr (suc i) X

    piStr  : (i : ℕ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i (∂₀ a)) (b : MorC (suc n) (suc (suc n))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)) → MorC n (suc n)
    piStrₛ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} → is-section (piStr i a aₛ a₁ b bₛ b₁)
    piStr₁ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} → ∂₁ (piStr i a aₛ a₁ b bₛ b₁) ≡ UUStr i (∂₀ a)

    lamStr  : (B : Ob (suc (suc n))) (u : MorC (suc n) (suc (suc n))) (uₛ : is-section u) (u₁ : ∂₁ u ≡ B) → MorC n (suc n)
    lamStrₛ : {B : Ob (suc (suc n))} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} → is-section (lamStr B u uₛ u₁)
    lamStr₁ : {B : Ob (suc (suc n))} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} → ∂₁ (lamStr B u uₛ u₁) ≡ PiStr B

    appStr  : (B : Ob (suc (suc n))) (f : MorC n (suc n)) (fₛ : is-section f) (f₁ : ∂₁ f ≡ PiStr B) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ ft B) → MorC n (suc n)
    appStrₛ : {B : Ob (suc (suc n))} {f : MorC n (suc n)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr B} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ ft B} → is-section (appStr B f fₛ f₁ a aₛ a₁)
    appStr₁ : {B : Ob (suc (suc n))} {f : MorC n (suc n)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr B} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ ft B} → ∂₁ (appStr B f fₛ f₁ a aₛ a₁) ≡ star a B a₁

    sigStr  : (i : ℕ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i (∂₀ a)) (b : MorC (suc n) (suc (suc n))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)) → MorC n (suc n)
    sigStrₛ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} → is-section (sigStr i a aₛ a₁ b bₛ b₁)
    sigStr₁ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} → ∂₁ (sigStr i a aₛ a₁ b bₛ b₁) ≡ UUStr i (∂₀ a)

    pairStr  : (B : Ob (suc (suc n))) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ ft B) (b : MorC n (suc n)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ star a B a₁) → MorC n (suc n)
    pairStrₛ : {B : Ob (suc (suc n))} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ ft B} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B a₁} → is-section (pairStr B a aₛ a₁ b bₛ b₁)
    pairStr₁ : {B : Ob (suc (suc n))} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ ft B} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B a₁} → ∂₁ (pairStr B a aₛ a₁ b bₛ b₁) ≡ SigStr B

    pr1Str  : (B : Ob (suc (suc n))) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ SigStr B) → MorC n (suc n)
    pr1Strₛ : {B : Ob (suc (suc n))} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr B} → is-section (pr1Str B u uₛ u₁)
    pr1Str₁ : {B : Ob (suc (suc n))} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr B} → ∂₁ (pr1Str B u uₛ u₁) ≡ ft B

    pr2Str  : (B : Ob (suc (suc n))) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ SigStr B) → MorC n (suc n)
    pr2Strₛ : {B : Ob (suc (suc n))} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr B} → is-section (pr2Str B u uₛ u₁)
    pr2Str₁ : {B : Ob (suc (suc n))} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr B} → ∂₁ (pr2Str B u uₛ u₁) ≡ star (pr1Str B u uₛ u₁) B pr1Str₁

    natStr  : (i : ℕ) (X : Ob n) → MorC n (suc n)
    natStrₛ : {i : ℕ} {X : Ob n} → is-section (natStr i X)
    natStr₁ : {i : ℕ} {X : Ob n} → ∂₁ (natStr i X) ≡ UUStr i X

    zeroStr  : (X : Ob n) → MorC n (suc n)
    zeroStrₛ : {X : Ob n} → is-section (zeroStr X)
    zeroStr₁ : {X : Ob n} → ∂₁ (zeroStr X) ≡ NatStr X

    sucStr  : (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ NatStr (∂₀ u)) → MorC n (suc n)
    sucStrₛ : {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr (∂₀ u)} → is-section (sucStr u uₛ u₁)
    sucStr₁ : {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr (∂₀ u)} → ∂₁ (sucStr u uₛ u₁) ≡ NatStr (∂₀ u)

    -- nat-elimStr  : (P : Ob (suc (suc n))) (P= : ft P ≡ NatStr (ft (ft P))) (d0 : MorC n (suc n)) (d0ₛ : is-section d0) (d0₁ : ∂₁ d0 ≡ star (zeroStr (ft (ft P))) P (zeroStr₁ ∙ ! P=))
    --                (dS : MorC (suc n) (suc (suc n))) (dSₛ : is-section dS) (dS₁ : ∂₁ dS ≡ star (comp (qq (pp (ft P)) (ft P) pp₁) (sucStr (ss (id (ft P))) ssₛ (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl ∙ {!?!})) (sucStr₁ ∙ ! (qq₀ ∙ {!!}))) P (comp₁ ∙ qq₁))
    --                (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ ft P) → MorC n (suc n)

    idStr  : (i : ℕ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i (∂₀ a)) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ ElStr i a aₛ a₁)
                     (v : MorC n (suc n)) (vₛ : is-section v) (v₁ : ∂₁ v ≡ ElStr i a aₛ a₁) → MorC n (suc n)
    idStrₛ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i a aₛ a₁}
                     {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i a aₛ a₁} → is-section (idStr i a aₛ a₁ u uₛ u₁ v vₛ v₁)
    idStr₁ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i a aₛ a₁}
                     {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i a aₛ a₁} → ∂₁ (idStr i a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ UUStr i (∂₀ a)

    reflStr  : (A : Ob (suc n)) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) → MorC n (suc n)
    reflStrₛ : {A : Ob (suc n)} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → is-section (reflStr A a aₛ a₁)
    reflStr₁ : {A : Ob (suc n)} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → ∂₁ (reflStr A a aₛ a₁) ≡ IdStr A a aₛ a₁ a aₛ a₁

    -- jjStr
    -- jjStrₛ
    -- jjStr₁

  uuStr₀ : {i : ℕ} (X : Ob n) → ∂₀ (uuStr i X) ≡ X
  uuStr₀ _ = is-section₀ uuStrₛ uuStr₁ ∙ UUStr=

  piStr₀ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)) → ∂₀ (piStr i a aₛ a₁ b bₛ b₁) ≡ ∂₀ a
  piStr₀ _ = is-section₀ piStrₛ piStr₁ ∙ UUStr=

  lamStr₀ : {B : Ob (suc (suc n))} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} (u₁ : ∂₁ u ≡ B) → ∂₀ (lamStr B u uₛ u₁) ≡ ft (ft B)
  lamStr₀ _ = is-section₀ lamStrₛ lamStr₁ ∙ PiStr=

  appStr₀ : {B : Ob (suc (suc n))} {f : MorC n (suc n)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr B} {a : MorC n (suc n)} (aₛ : is-section a) (a₁ : ∂₁ a ≡ ft B) → ∂₀ (appStr B f fₛ f₁ a aₛ a₁) ≡ ft (ft B)
  appStr₀ aₛ a₁ = is-section₀ appStrₛ appStr₁ ∙ ft-star ∙ is-section₀ aₛ a₁

  sigStr₀ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)) → ∂₀ (sigStr i a aₛ a₁ b bₛ b₁) ≡ ∂₀ a
  sigStr₀ _ = is-section₀ sigStrₛ sigStr₁ ∙ UUStr=

  pairStr₀ : {B : Ob (suc (suc n))} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ ft B} {b : MorC n (suc n)} {bₛ : is-section b} (b₁ : ∂₁ b ≡ star a B a₁) → ∂₀ (pairStr B a aₛ a₁ b bₛ b₁) ≡ ft (ft B)
  pairStr₀ _ = is-section₀ pairStrₛ pairStr₁ ∙ SigStr=

  pr1Str₀ : {B : Ob (suc (suc n))} {u : MorC n (suc n)} {uₛ : is-section u} (u₁ : ∂₁ u ≡ SigStr B) → ∂₀ (pr1Str B u uₛ u₁) ≡ ft (ft B)
  pr1Str₀ _ = is-section₀ pr1Strₛ pr1Str₁

  pr2Str₀ : {B : Ob (suc (suc n))} {u : MorC n (suc n)} {uₛ : is-section u} (u₁ : ∂₁ u ≡ SigStr B) → ∂₀ (pr2Str B u uₛ u₁) ≡ ft (ft B)
  pr2Str₀ _ = is-section₀ pr2Strₛ pr2Str₁ ∙ ft-star ∙ pr1Str₀ _

  natStr₀ : {i : ℕ} (X : Ob n) → ∂₀ (natStr i X) ≡ X
  natStr₀ _ = is-section₀ natStrₛ natStr₁ ∙ UUStr=

  zeroStr₀ : (X : Ob n) → ∂₀ (zeroStr X) ≡ X
  zeroStr₀ _ = is-section₀ zeroStrₛ zeroStr₁ ∙ NatStr=

  sucStr₀ : {u : MorC n (suc n)} {uₛ : is-section u} (u₁ : ∂₁ u ≡ NatStr (∂₀ u)) → ∂₀ (sucStr u uₛ u₁) ≡ ∂₀ u
  sucStr₀ _ = is-section₀ sucStrₛ sucStr₁ ∙ NatStr=

  idStr₀ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i a aₛ a₁}
                   {v : MorC n (suc n)} {vₛ : is-section v} (v₁ : ∂₁ v ≡ ElStr i a aₛ a₁) → ∂₀ (idStr i a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ ∂₀ a
  idStr₀ _ = is-section₀ idStrₛ idStr₁ ∙ UUStr=

  reflStr₀ : {A : Ob (suc n)} {u : MorC n (suc n)} {uₛ : is-section u} (u₁ : ∂₁ u ≡ A) → ∂₀ (reflStr A u uₛ u₁) ≡ ft A
  reflStr₀ _ = is-section₀ reflStrₛ reflStr₁ ∙ IdStr=

  {- Additional structure corresponding to naturality -}
  field
    UUStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {X : Ob m} (p : X ≡ ∂₁ g)
             → star g (UUStr i X) (! (UUStr= ∙ p)) ≡ UUStr i (∂₀ g)
    ElStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {v : MorC m (suc m)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ UUStr i (∂₀ v)} (p : ∂₀ v ≡ ∂₁ g)
             → star g (ElStr i v vₛ v₁) (! (ElStr= ∙ p)) ≡ ElStr i (starTm g v p) ssₛ (starTm₁ vₛ p v₁ ∙ UUStrNat g p ∙ ap (UUStr i) (! (ss₀ ∙ comp₀)))
    PiStrNat : {n m : ℕ} (g : MorC n m) {B : Ob (suc (suc m))} (p : ft (ft B) ≡ ∂₁ g)
             → star g (PiStr B) (! (PiStr= ∙ p)) ≡ PiStr (star+ g B p)
    SigStrNat : {n m : ℕ} (g : MorC n m) {B : Ob (suc (suc m))} (p : ft (ft B) ≡ ∂₁ g)
             → star g (SigStr B) (! (SigStr= ∙ p)) ≡ SigStr (star+ g B p)
    NatStrNat : {n m : ℕ} (g : MorC n m) {X : Ob m} (p : X ≡ ∂₁ g)
             → star g (NatStr X) (! (NatStr= ∙ p)) ≡ NatStr (∂₀ g)
    IdStrNat : {n m : ℕ} (g : MorC n m) {A : Ob (suc m)} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC m (suc m)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} (p : ft A ≡ ∂₁ g)
             (let a₀ = is-section₀ aₛ a₁ ∙ p) (let b₀ = is-section₀ bₛ b₁ ∙ p)
             → star g (IdStr A a aₛ a₁ b bₛ b₁) (! (IdStr= ∙ p)) ≡ IdStr (star g A (! p)) (starTm g a a₀) ssₛ (starTm₁ aₛ a₀ a₁) (starTm g b b₀) ssₛ (starTm₁ bₛ b₀ b₁)

    uuStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {X : Ob m} (p : X ≡ ∂₁ g)
             → starTm g (uuStr i X) (uuStr₀ X ∙ p) ≡ uuStr i (∂₀ g)

    piStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)}
                                                {b : MorC (suc m) (suc (suc m))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} (p : ∂₀ a ≡ ∂₁ g)
                                                (let b₀ = ap ft (is-section₀ bₛ b₁ ∙ UUStr=) ∙ ElStr= ∙ p)
             → starTm g (piStr i a aₛ a₁ b bₛ b₁) (piStr₀ _ ∙ p) ≡ piStr i (starTm g a p) ssₛ (starTm₁ aₛ p a₁ ∙ UUStrNat g p ∙ ap (UUStr i) (! (ss₀ ∙ comp₀)))
                                                                           (starTm+ g b b₀) ssₛ
                                                                             (starTm+₁ g b bₛ b₁ b₀ ∙ UUStrNat _ (! (qq₁ ∙ UUStr=))
                                                                              ∙ ap (UUStr i) (qq₀ ∙ ap2-irr star refl UUStr= ∙ ElStrNat g p))

    lamStrNat : {n m : ℕ} (g : MorC n m) {B : Ob (suc (suc m))} {u : MorC (suc m) (suc (suc m))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} (p : ft (ft B) ≡ ∂₁ g)
             → starTm g (lamStr B u uₛ u₁) (lamStr₀ _ ∙ p) ≡ lamStr (star+ g B p) (starTm+ g u (ap ft (is-section₀ uₛ u₁) ∙ p)) ssₛ (starTm+₁ g u uₛ u₁ (ap ft (is-section₀ uₛ u₁) ∙ p))

    appStrNat : {n m : ℕ} (g : MorC n m) {B : Ob (suc (suc m))} {f : MorC m (suc m)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr B}
                {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ ft B} (p : ft (ft B) ≡ ∂₁ g)
                (let a₀ = is-section₀ aₛ a₁ ∙ p) (let f₀ = is-section₀ fₛ f₁ ∙ PiStr= ∙ p)
             → starTm g (appStr B f fₛ f₁ a aₛ a₁) (appStr₀ aₛ a₁ ∙ p)
                ≡ appStr (star+ g B p)
                         (starTm g f f₀) ssₛ (starTm₁ fₛ f₀ f₁ ∙ PiStrNat g p)
                         (starTm g a a₀) ssₛ (starTm₁ aₛ a₀ a₁ ∙ ! (ft-star ∙ qq₀))

    sigStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)}
                                                {b : MorC (suc m) (suc (suc m))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} (p : ∂₀ a ≡ ∂₁ g)
                                                (let b₀ = ap ft (is-section₀ bₛ b₁ ∙ UUStr=) ∙ ElStr= ∙ p)
             → starTm g (sigStr i a aₛ a₁ b bₛ b₁) (sigStr₀ _ ∙ p) ≡ sigStr i (starTm g a p) ssₛ (starTm₁ aₛ p a₁ ∙ UUStrNat g p ∙ ap (UUStr i) (! (ss₀ ∙ comp₀)))
                                                                              (starTm+ g b b₀) ssₛ
                                                                                (starTm+₁ g b bₛ b₁ b₀ ∙ UUStrNat _ (! (qq₁ ∙ UUStr=))
                                                                                 ∙ ap (UUStr i) (qq₀ ∙ ap2-irr star refl UUStr= ∙ ElStrNat g p))

    pairStrNat : {n m : ℕ} (g : MorC n m) {B : Ob (suc (suc m))} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ ft B} {b : MorC m (suc m)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B a₁} (p : ft (ft B) ≡ ∂₁ g)
                 (let a₀ = is-section₀ aₛ a₁ ∙ p) (let b₀ = is-section₀ bₛ b₁ ∙ ft-star ∙ a₀)
             → starTm g (pairStr B a aₛ a₁ b bₛ b₁) (pairStr₀ _ ∙ p) ≡ pairStr (star+ g B p) (starTm g a a₀) ssₛ (starTm₁ aₛ a₀ a₁ ∙ ! (ft-star ∙ qq₀)) (starTm g b b₀) ssₛ (starTm₁ bₛ b₀ b₁ ∙ starstar g a aₛ B {a₀ = a₀} {p = p})

    pr1StrNat : {n m : ℕ} (g : MorC n m) {B : Ob (suc (suc m))} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr B} (p : ft (ft B) ≡ ∂₁ g)
                (let u₀ = is-section₀ uₛ u₁ ∙ SigStr= ∙ p)
             → starTm g (pr1Str B u uₛ u₁) (pr1Str₀ _ ∙ p) ≡ pr1Str (star+ g B p) (starTm g u u₀) ssₛ (starTm₁ uₛ u₀ u₁ ∙ SigStrNat g p)

    pr2StrNat : {n m : ℕ} (g : MorC n m) {B : Ob (suc (suc m))} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr B} (p : ft (ft B) ≡ ∂₁ g)
                (let u₀ = is-section₀ uₛ u₁ ∙ SigStr= ∙ p)
             → starTm g (pr2Str B u uₛ u₁) (pr2Str₀ _ ∙ p) ≡ pr2Str (star+ g B p) (starTm g u u₀) ssₛ (starTm₁ uₛ u₀ u₁ ∙ SigStrNat g p)

    natStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {X : Ob m} (p : X ≡ ∂₁ g)
             → starTm g (natStr i X) (natStr₀ X ∙ p) ≡ natStr i (∂₀ g)

    zeroStrNat : {n m : ℕ} (g : MorC n m) {X : Ob m} (p : X ≡ ∂₁ g)
             → starTm g (zeroStr X) (zeroStr₀ X ∙ p) ≡ zeroStr (∂₀ g)

    sucStrNat : {n m : ℕ} (g : MorC n m) {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr (∂₀ u)} (p : ∂₀ u ≡ ∂₁ g)
             → starTm g (sucStr u uₛ u₁) (sucStr₀ _ ∙ p) ≡ sucStr (starTm g u p) ssₛ (starTm₁ uₛ p u₁ ∙ NatStrNat g p ∙ ap NatStr (! (ss₀ ∙ comp₀)))

    -- nat-elimStrNat

    idStrNat : {n m : ℕ} (g : MorC n m) {i : ℕ} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i a aₛ a₁}
                                                {v : MorC m (suc m)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i a aₛ a₁} (p : ∂₀ a ≡ ∂₁ g)
                                                (let u₀ = is-section₀ uₛ u₁ ∙ ElStr= ∙ p) (let v₀ = is-section₀ vₛ v₁ ∙ ElStr= ∙ p)
             → starTm g (idStr i a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStr₀ _ ∙ p) ≡ idStr i (starTm g a p) ssₛ (starTm₁ aₛ p a₁ ∙ UUStrNat g p ∙ ap (UUStr i) (! (ss₀ ∙ comp₀)))
                                                                                   (starTm g u u₀) ssₛ (starTm₁ uₛ u₀ u₁ ∙ ElStrNat g p) (starTm g v v₀) ssₛ (starTm₁ vₛ v₀ v₁ ∙ ElStrNat g p)

    reflStrNat : {n m : ℕ} (g : MorC n m) {A : Ob (suc m)} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ A} (p : ft A ≡ ∂₁ g)
                 (let u₀ = is-section₀ uₛ u₁ ∙ p)
             → starTm g (reflStr A u uₛ u₁) (reflStr₀ _ ∙ p) ≡ reflStr (star g A (! p)) (starTm g u u₀) ssₛ (starTm₁ uₛ u₀ u₁)

  {- Additional structure corresponding to equality rules -}
  field
    betaPiStr : {B : Ob (suc (suc n))} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ ft B}
            → appStr B (lamStr B u uₛ u₁) lamStrₛ lamStr₁ a aₛ a₁ ≡ starTm a u (is-section₀ uₛ refl ∙ ap ft u₁ ∙ ! a₁)
    betaSig1Str : {B : Ob (suc (suc n))} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ ft B} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B a₁} → pr1Str B (pairStr B a aₛ a₁ b bₛ b₁) pairStrₛ pairStr₁ ≡ a
    betaSig2Str : {B : Ob (suc (suc n))} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ ft B} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B a₁} → pr2Str B (pairStr B a aₛ a₁ b bₛ b₁) pairStrₛ pairStr₁ ≡ b

    eluuStr : {i : ℕ} {X : Ob n} → ElStr (suc i) (uuStr i X) uuStrₛ (uuStr₁ ∙ ap (UUStr (suc i)) (! (uuStr₀ _))) ≡ UUStr i X
    elpiStr : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)}
            → ElStr i (piStr i a aₛ a₁ b bₛ b₁) piStrₛ (piStr₁ ∙ ap (UUStr i) (! (piStr₀ _))) ≡ PiStr (ElStr i b bₛ (b₁ ∙ ap (UUStr i) (! (is-section₀ bₛ b₁ ∙ UUStr=))))
    elsigStr : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)}
            → ElStr i (sigStr i a aₛ a₁ b bₛ b₁) sigStrₛ (sigStr₁ ∙ ap (UUStr i) (! (sigStr₀ _))) ≡ SigStr (ElStr i b bₛ (b₁ ∙ ap (UUStr i) (! (is-section₀ bₛ b₁ ∙ UUStr=))))
    elnatStr : {i : ℕ} {X : Ob n} → ElStr i (natStr i X) natStrₛ (natStr₁ ∙ ap (UUStr i) (! (natStr₀ _))) ≡ NatStr X
    elidStr : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i a aₛ a₁}
                      {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i a aₛ a₁} → ElStr i (idStr i a aₛ a₁ u uₛ u₁ v vₛ v₁) idStrₛ (idStr₁ ∙ ap (UUStr i) (! (idStr₀ _))) ≡ IdStr (ElStr i a aₛ a₁) u uₛ u₁ v vₛ v₁

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

  Mor→ₛ : {n : ℕ} {u : Mor C n (suc n)} (uₛ : is-section C u) → is-section D (Mor→ u)
  Mor→ₛ uₛ = ! (comp→ ∙ ap2-irr (comp D) (pp→ ∙ ap (pp D) ∂₁→) refl) ∙ ap Mor→ uₛ ∙ id→ ∙ ap (id D) ∂₀→

  Mor→₁ : {n : ℕ} {u : Mor C n (suc n)} {X : Ob C (suc n)} (u₁ : ∂₁ C u ≡ X) → ∂₁ D (Mor→ u) ≡ Ob→ X
  Mor→₁ u₁ = ! ∂₁→ ∙ ap Ob→ u₁

  field
    UUStr→ : {i : ℕ} {X : Ob C n} → Ob→ (UUStr sC i X) ≡ UUStr sD i (Ob→ X)
    ElStr→ : {i : ℕ} {v : Mor C n (suc n)} {vₛ : is-section C v} {v₁ : ∂₁ C v ≡ UUStr sC i (∂₀ C v)}
           → Ob→ (ElStr sC i v vₛ v₁) ≡ ElStr sD i (Mor→ v) (Mor→ₛ vₛ) (Mor→₁ v₁ ∙ UUStr→ ∙ ap (UUStr sD i) ∂₀→)
    PiStr→  : {B : Ob C (suc (suc n))} → Ob→ (PiStr sC B) ≡ PiStr sD (Ob→ B)
    SigStr→ : {B : Ob C (suc (suc n))} → Ob→ (SigStr sC B) ≡ SigStr sD (Ob→ B)
    NatStr→ : {X : Ob C n} → Ob→ (NatStr sC X) ≡ NatStr sD (Ob→ X)
    IdStr→  : (A : Ob C (suc n)) {a : Mor C n (suc n)} {aₛ : is-section C a} {a₁ : ∂₁ C a ≡ A} {b : Mor C n (suc n)} {bₛ : is-section C b} {b₁ : ∂₁ C b ≡ A}
            → Ob→ (IdStr sC A a aₛ a₁ b bₛ b₁) ≡ IdStr sD (Ob→ A) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁)


    uuStr→ : {i : ℕ} {X : Ob C n}
            → Mor→ (uuStr sC i X) ≡ uuStr sD i (Ob→ X)
    piStr→ : {i : ℕ} {a : Mor C n (suc n)} {aₛ : is-section C a} {a₁ : ∂₁ C a ≡ UUStr sC i (∂₀ C a)} {b : Mor C (suc n) (suc (suc n))} {bₛ : is-section C b} {b₁ : ∂₁ C b ≡ UUStr sC i (ElStr sC i a aₛ a₁)}
            → Mor→ (piStr sC i a aₛ a₁ b bₛ b₁) ≡ piStr sD i (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ UUStr→ ∙ ap (UUStr sD i) ∂₀→) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁ ∙ UUStr→ ∙ ap (UUStr sD i) ElStr→)
    lamStr→ : {B : Ob C (suc (suc n))} {u : Mor C (suc n) (suc (suc n))} {uₛ : is-section C u} {u₁ : ∂₁ C u ≡ B}
            → Mor→ (lamStr sC B u uₛ u₁) ≡ lamStr sD (Ob→ B) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁)
    appStr→ : {B : Ob C (suc (suc n))} {f : Mor C n (suc n)} {fₛ : is-section C f} {f₁ : ∂₁ C f ≡ PiStr sC B} {a : Mor C n (suc n)} {aₛ : is-section C a} {a₁ : ∂₁ C a ≡ ft C B}
            → Mor→ (appStr sC B f fₛ f₁ a aₛ a₁) ≡ appStr sD (Ob→ B) (Mor→ f) (Mor→ₛ fₛ) (Mor→₁ f₁ ∙ PiStr→) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ ft→)
    sigStr→ : {i : ℕ} {a : Mor C n (suc n)} {aₛ : is-section C a} {a₁ : ∂₁ C a ≡ UUStr sC i (∂₀ C a)} {b : Mor C (suc n) (suc (suc n))} {bₛ : is-section C b} {b₁ : ∂₁ C b ≡ UUStr sC i (ElStr sC i a aₛ a₁)}
            → Mor→ (sigStr sC i a aₛ a₁ b bₛ b₁) ≡ sigStr sD i (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ UUStr→ ∙ ap (UUStr sD i) ∂₀→) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁ ∙ UUStr→ ∙ ap (UUStr sD i) ElStr→)
    pairStr→ : {B : Ob C (suc (suc n))} {a : Mor C n (suc n)} {aₛ : is-section C a} {a₁ : ∂₁ C a ≡ ft C B} {b : Mor C n (suc n)} {bₛ : is-section C b} {b₁ : ∂₁ C b ≡ star C a B a₁}
            → Mor→ (pairStr sC B a aₛ a₁ b bₛ b₁) ≡ pairStr sD (Ob→ B) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ ft→) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁ ∙ star→)
    pr1Str→ : {B : Ob C (suc (suc n))} {u : Mor C n (suc n)} {uₛ : is-section C u} {u₁ : ∂₁ C u ≡ SigStr sC B}
            → Mor→ (pr1Str sC B u uₛ u₁) ≡ pr1Str sD (Ob→ B) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ SigStr→)
    pr2Str→ : {B : Ob C (suc (suc n))} {u : Mor C n (suc n)} {uₛ : is-section C u} {u₁ : ∂₁ C u ≡ SigStr sC B}
            → Mor→ (pr2Str sC B u uₛ u₁) ≡ pr2Str sD (Ob→ B) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ SigStr→)
    natStr→ : {i : ℕ} {X : Ob C n}
            → Mor→ (natStr sC i X) ≡ natStr sD i (Ob→ X)
    zeroStr→ : {X : Ob C n}
            → Mor→ (zeroStr sC X) ≡ zeroStr sD (Ob→ X)
    sucStr→ : {u : Mor C n (suc n)} {uₛ : is-section C u} {u₁ : ∂₁ C u ≡ NatStr sC (∂₀ C u)}
            → Mor→ (sucStr sC u uₛ u₁) ≡ sucStr sD (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ NatStr→ ∙ ap (NatStr sD) ∂₀→)
    idStr→ : {i : ℕ} {a : Mor C n (suc n)} {aₛ : is-section C a} {a₁ : ∂₁ C a ≡ UUStr sC i (∂₀ C a)} {u : Mor C n (suc n)} {uₛ : is-section C u} {u₁ : ∂₁ C u ≡ ElStr sC i a aₛ a₁}
                     {v : Mor C n (suc n)} {vₛ : is-section C v} {v₁ : ∂₁ C v ≡ ElStr sC i a aₛ a₁}
            → Mor→ (idStr sC i a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ idStr sD i (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ UUStr→ ∙ ap (UUStr sD i) ∂₀→) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ ElStr→) (Mor→ v) (Mor→ₛ vₛ) (Mor→₁ v₁ ∙ ElStr→)
    reflStr→ : {A : Ob C (suc n)} {a : Mor C n (suc n)} {aₛ : is-section C a} {a₁ : ∂₁ C a ≡ A}
            → Mor→ (reflStr sC A a aₛ a₁) ≡ reflStr sD (Ob→ A) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁)


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
