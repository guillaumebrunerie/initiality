{-# OPTIONS --rewriting --prop --without-K --allow-unsolved-metas #-}

open import common hiding (_,_; _∙_; !; ap) renaming (_∙#_ to _∙_; !# to !; ap# to ap)


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

  comp' : (g : Mor m k) (f : Mor n m) (_ : ∂₁ f ≡ ∂₀ g) → Mor n k
  comp' g f p = comp g f (# p)

  star' : (f : Mor m n) (X : Ob (suc n)) (_ : ∂₁ f ≡ ft X) → Ob (suc m)
  star' f X p = star f X (# p)

  qq' : (f : Mor m n) (X : Ob (suc n)) (_ : ∂₁ f ≡ ft X) → Mor (suc m) (suc n)
  qq' f X p = qq f X (# p)

  {- Sections of [pp] -}

  is-section : (u : Mor n (suc n)) → Prop
  is-section u = comp' (pp (∂₁ u)) u (common.! pp₀) ≡ id (∂₀ u)

  is-section₀ : {u : Mor n (suc n)} {X : Ob (suc n)} (uₛ : is-section u) (u₁ : ∂₁ u ≡ X) → ∂₀ u ≡ ft X
  is-section₀ uₛ u₁ = ! id₁ ∙ ap ∂₁ (! uₛ) ∙ comp₁ ∙ pp₁ ∙ ap ft u₁

  ssₛ : {f : Mor m (suc n)} → is-section (ss f)
  ssₛ = ap2-irr comp (ap pp ss₁) refl ∙ ss-pp ∙ ap id (! ss₀)

  ss-comp-section₁ : {g : Mor m n} {f : Mor n (suc n)} (fₛ : is-section f) {p : ∂₁ g ≡ ∂₀ f} → ∂₁ (ss (comp f g p)) ≡ star g (∂₁ f) (p ∙ is-section₀ fₛ refl)
  ss-comp-section₁ fₛ {p} = ss₁ ∙ ap2-irr star (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ fₛ ∙ ap id (! p)) refl ∙ id-right ) comp₁

  ss-of-section : (u : Mor n (suc n)) (uₛ : is-section u) → ss u ≡ u
  ss-of-section u uₛ = ! (ss-qq ∙ ap2-irr comp (ap2-irr qq uₛ refl {b' = id₁ ∙ is-section₀ uₛ refl} ∙ ap2-irr qq (ap id (! (ap ft ss₁ ∙ ft-star ∙ comp₀))) (! (ss₁ ∙ ap2-irr star (uₛ ∙ ap id (is-section₀ uₛ refl)) refl ∙ star-id)) ∙ qq-id) refl ∙ id-right)

  {- Iterated father and qq operations -}

  -- Take the prefix of the context up to spot [k]
  ft^ : (k : Fin (suc n)) (X : Ob n) → Ob (n -F' k)
  ft^ {n} last X = X
  ft^ {zero} (prev ()) X
  ft^ {suc n} (prev k) X = ft^ {n = n} k (ft X)

  -- Weaken [X] by adding [X+] at spot [k]
  star^ : (k : Fin (suc n)) (X+ : Ob (suc (n -F' k))) (X : Ob n) (X= : ft X+ ≡ ft^ k X) → Ob (suc n)
  qq^   : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} (X= : ft X+ ≡ ft^ k X) → Mor (suc n) n
  qq^₁  : {k : Fin (suc n)} {X+ : Ob (suc (n -F' k))} {X : Ob n} {X= : ft X+ ≡ ft^ k X} → ∂₁ (qq^ k X=) ≡ X
  qq^₀  : {k : Fin (suc n)} {X+ : Ob (suc (n -F' k))} {X : Ob n} {X= : ft X+ ≡ ft^ k X} → ∂₀ (qq^ k X=) ≡ star^ k X+ X X=

  star^ last X+ X X= = X+
  star^ {n = zero} (prev ()) X+ X X=
  star^ {n = suc n} (prev k) X+ X X= = star' (qq^ k X=) X qq^₁

  abstract
    qq^ last {X+ = X+} X= = pp X+
    qq^ {n = zero} (prev ()) X=
    qq^ {n = suc n} (prev k) {X = X} X= = qq (qq^ k X=) X (qq^₁ {k = k} {X= = X=})

    qq^₁ {n} {last} {X= = X=} = pp₁ ∙ X=
    qq^₁ {zero} {prev ()}
    qq^₁ {suc n} {prev k} = qq₁

    qq^₀ {_} {last} = pp₀
    qq^₀ {zero} {prev ()}
    qq^₀ {suc n} {prev k} = qq₀

    qq^last : {X+ : Ob (suc n)} {X : Ob n} {X= : ft X+ ≡ X} → qq^ last X= ≡ pp X+
    qq^last = refl

    qq^prev : {k : Fin (suc n)} {X+ : Ob (suc (n -F' k))} {X : Ob (suc n)} {X= : ft X+ ≡ ft^ (prev k) X} → qq^ (prev k) X= ≡ qq (qq^ k X=) X (qq^₁ {k = k} {X= = X=})
    qq^prev = refl

  qq^=p : {k : Fin (suc n)} {X : Ob n} {X+ : Ob (suc (n -F' k))} {X= : ft X+ ≡ ft^ k X} {X' : Ob n} {X'= : ft X+ ≡ ft^ k X'} (p : X' ≡ X) → qq^ k X'= ≡ qq^ k X=
  qq^=p refl = refl

  star^=p : {k : Fin (suc n)} {X : Ob n} {X+ : Ob (suc (n -F' k))} {X= : ft X+ ≡ ft^ k X} {X' : Ob n} {X'= : ft X+ ≡ ft^ k X'} (p : X' ≡ X) → star^ k X+ X X= ≡ star^ k X+ X' X'=
  star^=p refl = refl

  {- Other helper functions -}

  ss₁' : {f : Mor m (suc n)} {X : Ob (suc n)} (p : ∂₁ f ≡ X) → ∂₁ (ss f) ≡ star (comp (pp X) f (p ∙ ! pp₀)) X (comp₁ ∙ pp₁)
  ss₁' refl = ss₁

  id-left' : {f : Mor n m} {X : Ob n} (p : ∂₀ f ≡ X) → comp f (id X) (id₁ ∙ ! p) ≡ f
  id-left' refl = id-left

  id-right' : {f : Mor n m} {X : Ob m} (p : ∂₁ f ≡ X) → comp (id X) f (p ∙ (! id₀)) ≡ f
  id-right' refl = id-right

  ss-pp' : {m n : ℕ} {f : Mor m (suc n)} {X : Ob m} (f₀ : ∂₀ f ≡ X) {Y : Ob (suc n)} (f₁ : ∂₁ f ≡ Y) → comp (pp (star (comp (pp Y) f (f₁ ∙ ! pp₀)) Y (comp₁ ∙ pp₁))) (ss f) (ss₁' f₁ ∙ ! pp₀) ≡ id X
  ss-pp' refl refl = ss-pp

  star+ : (g : Mor n m) (A : Ob (suc (suc m))) {A' : Ob (suc m)} (A= : ft A ≡ A') (p : ft A' ≡ ∂₁ g) → Ob (suc (suc n))
  star+ g A {A'} A= p = star' (qq' g A' (! p)) A (qq₁ ∙ ! A=)

  star++ : (g : Mor n m) (A : Ob (suc (suc (suc m)))) {A' : Ob (suc (suc m))} (p : ft A ≡ A') {A'' : Ob (suc m)} (q : ft A' ≡ A'') (A= : ∂₁ g ≡ ft A'') → Ob (suc (suc (suc n)))
  star++ g A {A'} p {A''} q A= = star' (qq' (qq' g A'' A=) A' (qq₁ ∙ ! q)) A (qq₁ ∙ ! p)

  starTm : (g : Mor n m) (u : Mor m (suc m)) (u₀ : ∂₀ u ≡ ∂₁ g) → Mor n (suc n)
  starTm g u u₀ = ss (comp' u g (! u₀))

  starTm₁ : {g : Mor n m} {u : Mor m (suc m)} (uₛ : is-section u) (u₀ : ∂₀ u ≡ ∂₁ g) {X : Ob (suc m)} (p : ∂₁ u ≡ X) → ∂₁ (starTm g u u₀) ≡ star' g X (! u₀ ∙ is-section₀ uₛ p)
  starTm₁ uₛ u₀ p = ss₁' comp₁ ∙ ap2-irr star (! (assoc {q = ! pp₀}) ∙ ap2-irr comp (uₛ ∙ ap id u₀) refl ∙ id-right) p

  starTm+ : (g : Mor n m) (u : Mor (suc m) (suc (suc m))) (p : ft (∂₀ u) ≡ ∂₁ g) → Mor (suc n) (suc (suc n))
  starTm+ g u p = ss (comp' u (qq' g (∂₀ u) (! p)) qq₁)

  starTm+₁ : (g : Mor n m) (u : Mor (suc m) (suc (suc m))) (uₛ : is-section u) {X : Ob (suc (suc m))} {X' : Ob (suc m)} (X= : ft X ≡ X') (u₁ : ∂₁ u ≡ X) (p : ft (∂₀ u) ≡ ∂₁ g) → ∂₁ (starTm+ g u p) ≡ star+ g X X= (ap ft (! X= ∙ ! (is-section₀ uₛ u₁)) ∙ p)
  starTm+₁ g u uₛ refl u₁ p = starTm₁ {g = qq g (∂₀ u) (! p)} uₛ (! qq₁) u₁ ∙ ap2-irr star {a = qq g (∂₀ u) (! p)} (ap2-irr qq {a = g} refl (is-section₀ uₛ u₁) {b = ! p} {b' = ! (ap ft (! (is-section₀ uₛ u₁)) ∙ p)}) refl {b = ! (! (qq₁)) ∙ is-section₀ uₛ u₁} {b' = qq₁ }

  starTm++ : (g : Mor n m) (u : Mor (suc (suc m)) (suc (suc (suc m)))) (p : ft (ft (∂₀ u)) ≡ ∂₁ g) → Mor (suc (suc n)) (suc (suc (suc n)))
  starTm++ g u p = ss (comp' u (qq' (qq' g (ft (∂₀ u)) (! p)) (∂₀ u) qq₁) qq₁)

  postulate
    starTm++₁ : (g : Mor n m) (u : Mor (suc (suc m)) (suc (suc (suc m)))) (uₛ : is-section u) {X : Ob (suc (suc (suc m)))} {X' : Ob (suc (suc m))} (X= : ft X ≡ X')
                {X'' : Ob (suc m)} (X'= : ft X' ≡ X'') (u₁ : ∂₁ u ≡ X) (p : ft (ft (∂₀ u)) ≡ ∂₁ g)
              → ∂₁ (starTm++ g u p) ≡ star++ g X X= X'= (! p ∙ ap ft (ap ft (is-section₀ uₛ u₁ ∙ X=) ∙ X'=))
--    starTm++₁ g u uₛ u₁ p = {!!}
    -- starTm₁ {g = qq g (∂₀ u) (! p)} uₛ (! qq₁) u₁ ∙ ap2-irr star {a = qq g (∂₀ u) (! p)} (ap2-irr qq {a = g} refl (is-section₀ uₛ u₁) {b = ! p} {b' = ! (ap (ft) (! (is-section₀ uₛ u₁)) ∙ p)}) refl {b = ! (! (qq₁)) ∙ is-section₀ uₛ u₁} {b' = qq₁

  star-pp : {n m : ℕ} {g : Mor n m} {X X' : Ob (suc m)} {Y : Ob (suc m)} {w1 : _} {w2 : _} {w3 : _} (q : ft X ≡ ft Y) (r : X ≡ X')
           → star (qq g X w1) (star (pp X') Y w2) w3 ≡ star' (pp (star' g X w1)) (star' g Y (w1 ∙ q)) (pp₁ ∙ ft-star ∙ ! ft-star)
  star-pp {w1 = w1} q r =
    ! (star-comp {p = qq₁ ∙ r ∙ ! pp₀} _)
    ∙ ap2-irr star (ap2-irr comp (ap pp (! r)) refl ∙ pp-qq) refl
    ∙ star-comp (w1 ∙ q)

  star-pp' : {n : ℕ} {g : Mor (suc n) (suc (suc n))} (gₛ : is-section g) {X : Ob (suc (suc n))} {Y : Ob (suc (suc n))} {w1 : _} {w2 : _}
           → star g (star (pp X) Y w1) w2 ≡ Y
  star-pp' gₛ {w1 = w1} {w2 = w2} = ! (star-comp {p = w2 ∙ ft-star} _) ∙ ap2-irr star (ap2-irr comp (ap pp (! (w2 ∙ ft-star ∙ pp₀))) refl ∙ gₛ ∙ ap id (is-section₀ gₛ (w2 ∙ ft-star ∙ pp₀) ∙ ! pp₁ ∙ w1)) refl ∙ star-id ∙ refl

  star-qqpp : {n m : ℕ} {g : Mor n m} {X : Ob (suc m)} {Z : Ob (suc (suc m))}
            → ∀ {w1 w2 w3 w4 w5} → (q : ft Z ≡ X)
            → star (qq (qq g X w1) (star (pp X) X w2) w3) (star (qq (pp X) X w2) Z w4) w5
              ≡ star' (qq' (pp (star' g X w1)) (star' g X w1) pp₁) (star' (qq' g X w1) Z (w3 ∙ ft-star ∙ pp₀ ∙ ! q)) (qq₁ ∙ ! qq₀ ∙ ! ft-star)
  star-qqpp refl =
    ! (star-comp _)
    ∙ ap2-irr star (! (qq-comp _) ∙ ap2-irr qq pp-qq refl ∙ qq-comp _) refl
    ∙ star-comp _

  starstar : {g : Mor n m} {a : Mor m (suc m)} (aₛ : is-section a) {B : Ob (suc (suc m))} {a₁ : ∂₁ a ≡ ft B} {g₁ : ∂₁ g ≡ ft (star a B a₁)} (a₀ : ∂₀ a ≡ ∂₁ g) (p : ft (ft B) ≡ ∂₁ g) {B' : Ob (suc m)} (q : ft B ≡ B')
         → star g (star a B a₁) g₁ ≡ star' (starTm g a a₀) (star' (qq' g B' (! p ∙ ap ft q)) B (qq₁ ∙ ! q)) (starTm₁ aₛ a₀ a₁ ∙ ! qq₀ ∙ ! (ft-star ∙ qq₀ ∙ ap-irr (star _) (! q) ∙ ! qq₀))
  starstar {g} {a} aₛ {B} {a₁} {g₁} a₀ p q = ! (star-comp {p = ! a₀} a₁) ∙ ap2-irr star (ss-qq ∙ ap2-irr comp (ap2-irr qq (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ aₛ ∙ ap id a₀) refl ∙ id-right) (comp₁ ∙ a₁)) refl) refl ∙ star-comp {p = starTm₁ aₛ a₀ a₁ ∙ ! qq₀} qq₁ ∙ ap-irr (star _) (ap2-irr star (ap2-irr qq refl q) refl)

  star-varCL : {g : Mor n m} {X : Ob (suc m)} {p : ∂₁ g ≡ ft X} → starTm (qq g X p) (ss (id X)) (ss₀ ∙ id₀ ∙ ! qq₁) ≡ ss (id (star g X p))
  star-varCL = ss-comp {f₁ = comp₁ ∙ ss₁} ∙ ap ss (! (assoc {q = ss₁ ∙ ! qq₀}) ∙ ap2-irr comp (! ss-qq) refl ∙ id-right' qq₁) ∙ ap ss (! (id-left' qq₀)) ∙ ! (ss-comp {f₁ = id₁})

  star-varCL' : {g : Mor (suc n) (suc m)} {X : Ob (suc m)} {p : ∂₁ g ≡ X} → starTm g (ss (id X)) (ss₀ ∙ id₀ ∙ ! p) ≡ ss g
  star-varCL' {p = p} = ss-comp {f₁ = comp₁ ∙ ss₁' id₁} ∙ ap ss (! (assoc {q = ss₁' id₁ ∙ ! qq₀}) ∙ ap2-irr comp (ap2-irr comp (ap2-irr qq (ap2-irr comp (ap pp (! id₁)) refl) (! id₁)) refl ∙ ! ss-qq) refl ∙ id-right' p)

  star-varCL'' : {g : Mor n m} {f : Mor m (suc k)} {p : ∂₁ g ≡ ∂₀ f} → starTm g (ss f) (ss₀ ∙ ! p) ≡ ss (comp f g p)
  star-varCL'' = ss-comp {f₁ = comp₁ ∙ ss₁} ∙ ap ss (! (assoc {q = ss₁ ∙ ! qq₀}) ∙ ap2-irr comp (! ss-qq) refl)

  pp^  : (k : Fin n) → Ob n → Mor n (n -F k)
  pp^₀ : (k : Fin n) (X : Ob n) → ∂₀ (pp^ k X) ≡ X

  pp^ last X = id X
  pp^ (prev last) X = pp X
  pp^ (prev k@(prev _)) X = comp (pp^ k (ft X)) (pp X) (pp₁ ∙ ! (pp^₀ k (ft X)))

  pp^₀ last X = id₀
  pp^₀ (prev last) X = pp₀
  pp^₀ (prev k@(prev _)) X = comp₀ ∙ pp₀

  -- Take the prefix of the context up to (and including) variable [k]
  ft^' : (k : Fin n) (X : Ob n) → Ob (n -F k)
  ft^' {n} last X = X
  ft^' {suc n} (prev k) X = ft^' {n = n} k (ft X)

  pp^₁ : (k : Fin n) (X : Ob n) → ∂₁ (pp^ k X) ≡ ft^' k X
  pp^₁ last X = id₁
  pp^₁ (prev last) X = pp₁
  pp^₁ (prev (prev k)) X = comp₁ ∙ pp^₁ (prev k) (ft X)

  varC : (k : Fin n) → Ob n → Mor n (suc n)
  varC k X = ss (pp^ k X)

  varC₀ : (k : Fin n) (X : Ob n) → ∂₀ (varC k X) ≡ X
  varC₀ k X = ss₀ ∙ pp^₀ k X

  varCL₁ : {X : Ob (suc n)} → ∂₁ (varC last X) ≡ star (pp X) X (pp₁ ∙ refl)
  varCL₁ = ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl

  varC+₁ : (k : Fin n) {X : Ob (suc n)} {Y : Ob n} (Y= : ft X ≡ Y) {Z : Ob (suc n)} (Z= : ∂₁ (varC k Y) ≡ Z) → ∂₁ (varC (prev k) X) ≡ star (pp X) Z (pp₁ ∙ {!TODO!})
  varC+₁ last refl refl = ss₁' pp₁ ∙ star-comp pp₁ ∙ ap2-irr star refl (! varCL₁)
  varC+₁ (prev k) {X = X} refl refl = ss₁' (comp₁ ∙ pp^₁ (prev k) (ft X)) ∙ ap2-irr star (! (assoc {q = pp^₁ (prev k) (ft X) ∙ ! pp₀})) refl ∙ star-comp (comp₁ ∙ pp₁) ∙ ap2-irr star refl (ap2-irr star (ap2-irr comp (ap pp (! (pp^₁ (prev k) _))) refl) (! (pp^₁ (prev k) _)) ∙ ! ss₁)

  ss-id₁ : {X : Ob (suc n)} → ∂₁ (ss (id X)) ≡ star (pp X) X pp₁
  ss-id₁ = ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl

{- Contextual categories with structure corresponding to the type theory we are interested in -}

record CCatwithUU (ccat : CCat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)

  field
    UUStr  : (i : ℕ) (X : Ob n) → Ob (suc n)
    UUStr= : {i : ℕ} {X : Ob n} → ft (UUStr i X) ≡ X
    UUStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {X : Ob m} (p : X ≡ ∂₁ g)
             → star g (UUStr i X) (! (UUStr= ∙ p)) ≡ UUStr i (∂₀ g)

record CCatwithEl (ccat : CCat) (ccatuu : CCatwithUU ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu

  field
    ElStr  : (i : ℕ) (v : MorC n (suc n)) (vₛ : is-section v) (v₁ : ∂₁ v ≡ UUStr i (∂₀ v)) → Ob (suc n)
    ElStr= : {i : ℕ} {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ UUStr i (∂₀ v)} → ft (ElStr i v vₛ v₁) ≡ ∂₀ v
    ElStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {v : MorC m (suc m)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ UUStr i (∂₀ v)} (p : ∂₀ v ≡ ∂₁ g)
             → star g (ElStr i v vₛ v₁) (! (ElStr= ∙ p)) ≡ ElStr i (starTm g v p) ssₛ (starTm₁ vₛ p v₁ ∙ UUStrNat g p ∙ ap (UUStr i) (! (ss₀ ∙ comp₀)))

record CCatwithPi (ccat : CCat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)

  field
    PiStr  : (A : Ob (suc n)) (B : Ob (suc (suc n))) (B= : ft B ≡ A) → Ob (suc n)
    PiStr= : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} → ft (PiStr A B B=) ≡ ft A
    PiStrNat : {n m : ℕ} (g : MorC n m) {A : Ob (suc m)} {B : Ob (suc (suc m))} {B= : ft B ≡ A} (p : ft A ≡ ∂₁ g)
             → star g (PiStr A B B=) (! (PiStr= ∙ p)) ≡ PiStr (star g A (! p)) (star+ g B B= p) (ft-star ∙ qq₀)

record CCatwithSig (ccat : CCat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)

  field
    SigStr  : (A : Ob (suc n)) (B : Ob (suc (suc n))) (B= : ft B ≡ A) → Ob (suc n)
    SigStr= : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} → ft (SigStr A B B=) ≡ ft A
    SigStrNat : {n m : ℕ} (g : MorC n m) {A : Ob (suc m)} {B : Ob (suc (suc m))} {B= : ft B ≡ A} (p : ft A ≡ ∂₁ g)
             → star g (SigStr A B B=) (! (SigStr= ∙ p)) ≡ SigStr (star g A (! p)) (star+ g B B= p) (ft-star ∙ qq₀)

record CCatwithNat (ccat : CCat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)

  field
    NatStr  : (X : Ob n) → Ob (suc n)
    NatStr= : {X : Ob n} → ft (NatStr X) ≡ X
    NatStrNat : {n m : ℕ} (g : MorC n m) {X : Ob m} (p : X ≡ ∂₁ g)
             → star g (NatStr X) (! (NatStr= ∙ p)) ≡ NatStr (∂₀ g)

  

record CCatwithId (ccat : CCat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)

  field
    IdStr   : (A : Ob (suc n)) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) (b : MorC n (suc n)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ A) → Ob (suc n)
    IdStr=  : {A : Ob (suc n)} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} → ft (IdStr A a aₛ a₁ b bₛ b₁) ≡ ft A
    IdStrNat : {n m : ℕ} (g : MorC n m) {A : Ob (suc m)} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC m (suc m)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} (p : ft A ≡ ∂₁ g)
             (let a₀ = is-section₀ aₛ a₁ ∙ p) (let b₀ = is-section₀ bₛ b₁ ∙ p)
             → star g (IdStr A a aₛ a₁ b bₛ b₁) (! (IdStr= ∙ p)) ≡ IdStr (star g A (! p)) (starTm g a a₀) ssₛ (starTm₁ aₛ a₀ a₁) (starTm g b b₀) ssₛ (starTm₁ bₛ b₀ b₁)
             
  ap-irr-IdStr : {A A' : Ob (suc n)} (A= : A ≡ A') {u u' : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ A} {uₛ' : is-section u'} {u₁' : ∂₁ u' ≡ A'} (u= : u ≡ u') {v v' : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ A} {vₛ' : is-section v'} {v₁' : ∂₁ v' ≡ A'} (v= : v ≡ v') → IdStr A u uₛ u₁ v vₛ v₁ ≡ IdStr A' u' uₛ' u₁' v' vₛ' v₁'
  ap-irr-IdStr refl refl refl = refl

record CCatwithuu (ccat : CCat) (ccatuu : CCatwithUU ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu

  field
    uuStr  : (i : ℕ) (X : Ob n) → MorC n (suc n)
    uuStrₛ : {i : ℕ} {X : Ob n} → is-section (uuStr i X)
    uuStr₁ : {i : ℕ} {X : Ob n} → ∂₁ (uuStr i X) ≡ UUStr (suc i) X

  uuStr₀ : {i : ℕ} (X : Ob n) → ∂₀ (uuStr i X) ≡ X
  uuStr₀ _ = is-section₀ uuStrₛ uuStr₁ ∙ UUStr=

  field
    uuStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {X : Ob m} (p : X ≡ ∂₁ g)
             → starTm g (uuStr i X) (uuStr₀ X ∙ p) ≡ uuStr i (∂₀ g)

record CCatwithpi (ccat : CCat) (ccatuu : CCatwithUU ccat) (ccatel : CCatwithEl ccat ccatuu) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu
  open CCatwithEl ccatel

  field
    piStr  : (i : ℕ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i (∂₀ a)) (b : MorC (suc n) (suc (suc n))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)) → MorC n (suc n)
    piStrₛ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} → is-section (piStr i a aₛ a₁ b bₛ b₁)
    piStr₁ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} → ∂₁ (piStr i a aₛ a₁ b bₛ b₁) ≡ UUStr i (∂₀ a)

  piStr₀ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)) → ∂₀ (piStr i a aₛ a₁ b bₛ b₁) ≡ ∂₀ a
  piStr₀ _ = is-section₀ piStrₛ piStr₁ ∙ UUStr=

  field
    piStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)}
                                                {b : MorC (suc m) (suc (suc m))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} (p : ∂₀ a ≡ ∂₁ g)
                                                (let b₀ = ap ft (is-section₀ bₛ b₁ ∙ UUStr=) ∙ ElStr= ∙ p)
             → starTm g (piStr i a aₛ a₁ b bₛ b₁) (piStr₀ _ ∙ p) ≡ piStr i (starTm g a p)   ssₛ (starTm₁ aₛ p a₁ ∙ UUStrNat g p ∙ ap (UUStr i) (! (ss₀ ∙ comp₀)))
                                                                           (starTm+ g b b₀) ssₛ (starTm+₁ g b bₛ UUStr= b₁ b₀ ∙ UUStrNat _ (! qq₁)
                                                                                                 ∙ ap (UUStr i) (qq₀ ∙ ElStrNat g p))

record CCatwithlam (ccat : CCat) (ccatpi : CCatwithPi ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithPi ccatpi

  field
    lamStr  : (A : Ob (suc n)) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (u : MorC (suc n) (suc (suc n))) (uₛ : is-section u) (u₁ : ∂₁ u ≡ B) → MorC n (suc n)
    lamStrₛ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} → is-section (lamStr A B B= u uₛ u₁)
    lamStr₁ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} → ∂₁ (lamStr A B B= u uₛ u₁) ≡ PiStr A B B=

  lamStr₀ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} (u₁ : ∂₁ u ≡ B) → ∂₀ (lamStr A B B= u uₛ u₁) ≡ ft A
  lamStr₀ _ = is-section₀ lamStrₛ lamStr₁ ∙ PiStr=

  field
    lamStrNat : {n m : ℕ} (g : MorC n m) {A : Ob (suc m)} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {u : MorC (suc m) (suc (suc m))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} (p : ft A ≡ ∂₁ g)
             → starTm g (lamStr A B B= u uₛ u₁) (lamStr₀ _ ∙ p) ≡ lamStr (star g A (! p)) (star+ g B B= p) (ft-star ∙ qq₀) (starTm+ g u (ap ft (is-section₀ uₛ u₁) ∙ ap ft B= ∙ p)) ssₛ (starTm+₁ g u uₛ B= u₁ (ap ft (is-section₀ uₛ u₁) ∙ ap ft B= ∙ p))

record CCatwithapp (ccat : CCat) (ccatpi : CCatwithPi ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithPi ccatpi

  field
    appStr  : (A : Ob (suc n)) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (f : MorC n (suc n)) (fₛ : is-section f) (f₁ : ∂₁ f ≡ PiStr A B B=) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) → MorC n (suc n)
    appStrₛ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {f : MorC n (suc n)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr A B B=} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → is-section (appStr A B B= f fₛ f₁ a aₛ a₁)
    appStr₁ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {f : MorC n (suc n)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr A B B=} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → ∂₁ (appStr A B B= f fₛ f₁ a aₛ a₁) ≡ star a B (a₁ ∙ ! B=)

  appStr₀ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {f : MorC n (suc n)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr A B B=} {a : MorC n (suc n)} (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) → ∂₀ (appStr A B B= f fₛ f₁ a aₛ a₁) ≡ ft A
  appStr₀ aₛ a₁ = is-section₀ appStrₛ appStr₁ ∙ ft-star ∙ is-section₀ aₛ a₁

  field
    appStrNat : {n m : ℕ} (g : MorC n m) {A : Ob (suc m)} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {f : MorC m (suc m)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr A B B=}
                {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} (p : ft A ≡ ∂₁ g)
                (let a₀ = is-section₀ aₛ a₁ ∙ p) (let f₀ = is-section₀ fₛ f₁ ∙ PiStr= ∙ p)
             → starTm g (appStr A B B= f fₛ f₁ a aₛ a₁) (appStr₀ aₛ a₁ ∙ p)
                ≡ appStr (star g A (! p))
                         (star+ g B B= p)
                         (ft-star ∙ qq₀)
                         (starTm g f f₀) ssₛ (starTm₁ fₛ f₀ f₁ ∙ PiStrNat g p)
                         (starTm g a a₀) ssₛ (starTm₁ aₛ a₀ a₁)

record CCatwithsig (ccat : CCat) (ccatuu : CCatwithUU ccat) (ccatel : CCatwithEl ccat ccatuu) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu
  open CCatwithEl ccatel

  field
    sigStr  : (i : ℕ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i (∂₀ a)) (b : MorC (suc n) (suc (suc n))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)) → MorC n (suc n)
    sigStrₛ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} → is-section (sigStr i a aₛ a₁ b bₛ b₁)
    sigStr₁ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} → ∂₁ (sigStr i a aₛ a₁ b bₛ b₁) ≡ UUStr i (∂₀ a)

  sigStr₀ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} (b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)) → ∂₀ (sigStr i a aₛ a₁ b bₛ b₁) ≡ ∂₀ a
  sigStr₀ _ = is-section₀ sigStrₛ sigStr₁ ∙ UUStr=

  field
    sigStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)}
                                                {b : MorC (suc m) (suc (suc m))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)} (p : ∂₀ a ≡ ∂₁ g)
                                                (let b₀ = ap ft (is-section₀ bₛ b₁ ∙ UUStr=) ∙ ElStr= ∙ p)
             → starTm g (sigStr i a aₛ a₁ b bₛ b₁) (sigStr₀ _ ∙ p) ≡ sigStr i (starTm g a p) ssₛ (starTm₁ aₛ p a₁ ∙ UUStrNat g p ∙ ap (UUStr i) (! (ss₀ ∙ comp₀)))
                                                                              (starTm+ g b b₀) ssₛ
                                                                                (starTm+₁ g b bₛ UUStr= b₁ b₀ ∙ UUStrNat _ (! qq₁)
                                                                                 ∙ ap (UUStr i) (qq₀ ∙ ElStrNat g p))

record CCatwithpair (ccat : CCat) (ccatsig : CCatwithSig ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithSig ccatsig

  field
    pairStr  : (A : Ob (suc n)) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) (b : MorC n (suc n)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ star a B (a₁ ∙ ! B=)) → MorC n (suc n)
    pairStrₛ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B (a₁ ∙ ! B=)} → is-section (pairStr A B B= a aₛ a₁ b bₛ b₁)
    pairStr₁ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B (a₁ ∙ ! B=)} → ∂₁ (pairStr A B B= a aₛ a₁ b bₛ b₁) ≡ SigStr A B B=

  pairStr₀ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} (b₁ : ∂₁ b ≡ star a B (a₁ ∙ ! B=)) → ∂₀ (pairStr A B B= a aₛ a₁ b bₛ b₁) ≡ ft A
  pairStr₀ _ = is-section₀ pairStrₛ pairStr₁ ∙ SigStr=

  field
    pairStrNat : {n m : ℕ} (g : MorC n m) {A : Ob (suc m)} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC m (suc m)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B (a₁ ∙ ! B=)} (p : ft A ≡ ∂₁ g)
                 (let a₀ = is-section₀ aₛ a₁ ∙ p) (let b₀ = is-section₀ bₛ b₁ ∙ ft-star ∙ a₀)
             → starTm g (pairStr A B B= a aₛ a₁ b bₛ b₁) (pairStr₀ _ ∙ p) ≡ pairStr (star g A (! p)) (star+ g B B= p) (ft-star ∙ qq₀) (starTm g a a₀) ssₛ (starTm₁ aₛ a₀ a₁) (starTm g b b₀) ssₛ (starTm₁ bₛ b₀ b₁ ∙ starstar aₛ a₀ (ap ft B= ∙ p) B=)

record CCatwithpr1 (ccat : CCat) (ccatsig : CCatwithSig ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithSig ccatsig

  field
    pr1Str  : (A : Ob (suc n)) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ SigStr A B B=) → MorC n (suc n)
    pr1Strₛ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr A B B=} → is-section (pr1Str A B B= u uₛ u₁)
    pr1Str₁ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr A B B=} → ∂₁ (pr1Str A B B= u uₛ u₁) ≡ A

  pr1Str₀ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} (u₁ : ∂₁ u ≡ SigStr A B B=) → ∂₀ (pr1Str A B B= u uₛ u₁) ≡ ft A
  pr1Str₀ _ = is-section₀ pr1Strₛ pr1Str₁

  field
    pr1StrNat : {n m : ℕ} (g : MorC n m) {A : Ob (suc m)} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr A B B=} (p : ft A ≡ ∂₁ g)
                (let u₀ = is-section₀ uₛ u₁ ∙ SigStr= ∙ p)
             → starTm g (pr1Str A B B= u uₛ u₁) (pr1Str₀ _ ∙ p) ≡ pr1Str (star g A (! p)) (star+ g B B= p) (ft-star ∙ qq₀) (starTm g u u₀) ssₛ (starTm₁ uₛ u₀ u₁ ∙ SigStrNat g p)

record CCatwithpr2 (ccat : CCat) (ccatsig : CCatwithSig ccat) (ccatpr1 : CCatwithpr1 ccat ccatsig) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithSig ccatsig
  open CCatwithpr1 ccatpr1

  field
    pr2Str  : (A : Ob (suc n)) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ SigStr A B B=) → MorC n (suc n)
    pr2Strₛ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr A B B=} → is-section (pr2Str A B B= u uₛ u₁)
    pr2Str₁ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr A B B=} → ∂₁ (pr2Str A B B= u uₛ u₁) ≡ star (pr1Str A B B= u uₛ u₁) B (pr1Str₁ ∙ ! B=)

  pr2Str₀ : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} (u₁ : ∂₁ u ≡ SigStr A B B=) → ∂₀ (pr2Str A B B= u uₛ u₁) ≡ ft A
  pr2Str₀ _ = is-section₀ pr2Strₛ pr2Str₁ ∙ ft-star ∙ pr1Str₀ _

  field
    pr2StrNat : {n m : ℕ} (g : MorC n m) {A : Ob (suc m)} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr A B B=} (p : ft A ≡ ∂₁ g)
                (let u₀ = is-section₀ uₛ u₁ ∙ SigStr= ∙ p)
             → starTm g (pr2Str A B B= u uₛ u₁) (pr2Str₀ _ ∙ p) ≡ pr2Str (star g A (! p)) (star+ g B B= p) (ft-star ∙ qq₀) (starTm g u u₀) ssₛ (starTm₁ uₛ u₀ u₁ ∙ SigStrNat g p)

record CCatwithnat (ccat : CCat) (ccatuu : CCatwithUU ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu

  field
    natStr  : (i : ℕ) (X : Ob n) → MorC n (suc n)
    natStrₛ : {i : ℕ} {X : Ob n} → is-section (natStr i X)
    natStr₁ : {i : ℕ} {X : Ob n} → ∂₁ (natStr i X) ≡ UUStr i X

  natStr₀ : {i : ℕ} (X : Ob n) → ∂₀ (natStr i X) ≡ X
  natStr₀ _ = is-section₀ natStrₛ natStr₁ ∙ UUStr=

  field
    natStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {X : Ob m} (p : X ≡ ∂₁ g)
             → starTm g (natStr i X) (natStr₀ X ∙ p) ≡ natStr i (∂₀ g)

record CCatwithzero (ccat : CCat) (ccatnat : CCatwithNat ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithNat ccatnat

  field
    zeroStr  : (X : Ob n) → MorC n (suc n)
    zeroStrₛ : {X : Ob n} → is-section (zeroStr X)
    zeroStr₁ : {X : Ob n} → ∂₁ (zeroStr X) ≡ NatStr X

  zeroStr₀ : (X : Ob n) → ∂₀ (zeroStr X) ≡ X
  zeroStr₀ _ = is-section₀ zeroStrₛ zeroStr₁ ∙ NatStr=

  field
    zeroStrNat : {n m : ℕ} (g : MorC n m) {X : Ob m} (p : X ≡ ∂₁ g)
             → starTm g (zeroStr X) (zeroStr₀ X ∙ p) ≡ zeroStr (∂₀ g)

record CCatwithsuc (ccat : CCat) (ccatnat : CCatwithNat ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithNat ccatnat

  field
    sucStr  : (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ NatStr (∂₀ u)) → MorC n (suc n)
    sucStrₛ : {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr (∂₀ u)} → is-section (sucStr u uₛ u₁)
    sucStr₁ : {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr (∂₀ u)} → ∂₁ (sucStr u uₛ u₁) ≡ NatStr (∂₀ u)

  sucStr₀ : {u : MorC n (suc n)} {uₛ : is-section u} (u₁ : ∂₁ u ≡ NatStr (∂₀ u)) → ∂₀ (sucStr u uₛ u₁) ≡ ∂₀ u
  sucStr₀ _ = is-section₀ sucStrₛ sucStr₁ ∙ NatStr=

  field
    sucStrNat : {n m : ℕ} (g : MorC n m) {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr (∂₀ u)} (p : ∂₀ u ≡ ∂₁ g)
             → starTm g (sucStr u uₛ u₁) (sucStr₀ _ ∙ p) ≡ sucStr (starTm g u p) ssₛ (starTm₁ uₛ p u₁ ∙ NatStrNat g p ∙ ap NatStr (! (ss₀ ∙ comp₀)))

record CCatwithnatelim (ccat : CCat) (ccatnat : CCatwithNat ccat) (ccatzero : CCatwithzero ccat ccatnat) (ccatsuc : CCatwithsuc ccat ccatnat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithNat ccatnat
  open CCatwithzero ccatzero
  open CCatwithsuc ccatsuc

  T-dS₁ : (X : Ob n) (P : Ob (suc (suc n))) (P= : ft P ≡ NatStr X) (dS : MorC (suc (suc n)) (suc (suc (suc n)))) → Prop
  T-dS₁ X P P= dS = ∂₁ dS ≡ star' (pp P)
                                  (star' (sucStr (ss (id (NatStr X))) ssₛ (ss₁' id₁ ∙ NatStrNat _ (! (comp₁ ∙ pp₁ ∙ NatStr=)) ∙ ap NatStr (comp₀ ∙ ! ss₀)))
                                         (star' (qq' (pp (NatStr X)) (NatStr X) pp₁)
                                                P
                                                (qq₁ ∙ ! P=))
                                         (sucStr₁ ∙ ap NatStr (ss₀ ∙ id₀ ∙ ! pp₀) ∙ ! (NatStrNat _ (! NatStr= ∙ ! pp₁)) ∙ ! qq₀ ∙ ! ft-star))
                                  (pp₁ ∙ ! (ft-star ∙ sucStr₀ _ ∙ ss₀ ∙ id₀ ∙ ! P=))

  field
    natelimStr  : (X : Ob n) (P : Ob (suc (suc n))) (P= : ft P ≡ NatStr X)
                  (dO : MorC n (suc n)) (dOₛ : is-section dO) (dO₁ : ∂₁ dO ≡ star (zeroStr X) P (zeroStr₁ ∙ ! P=))
                  (dS : MorC (suc (suc n)) (suc (suc (suc n)))) (dSₛ : is-section dS) (dS₁ : T-dS₁ X P P= dS)
                  (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ ft P)
                  → MorC n (suc n)
    natelimStrₛ : ∀ {X P P= dO dS u} {dOₛ : is-section dO} {dO₁ : ∂₁ dO ≡ star (zeroStr X) P (zeroStr₁ ∙ ! P=)} {dSₛ : is-section dS} {dS₁ : T-dS₁ X P P= dS} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ft P}
                → is-section (natelimStr {n = n} X P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)
    natelimStr₁ : ∀ {X P P= dO dS u} {dOₛ : is-section dO} {dO₁ : ∂₁ dO ≡ star (zeroStr X) P (zeroStr₁ ∙ ! P=)} {dSₛ : is-section dS} {dS₁ : T-dS₁ X P P= dS} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ft P}
                → ∂₁ (natelimStr {n = n} X P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) ≡ star u P u₁

  natelimStr₀ : ∀ {X P} (P= : _) → ∀ {dO dS u} {dOₛ : is-section dO} {dO₁ : ∂₁ dO ≡ star (zeroStr X) P (zeroStr₁ ∙ ! P=)} {dSₛ : is-section dS} {dS₁ : T-dS₁ X P P= dS} (uₛ : is-section u) (u₁ : ∂₁ u ≡ ft P)
                → ∂₀ (natelimStr {n = n} X P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) ≡ X
  natelimStr₀ P= uₛ u₁ = is-section₀ natelimStrₛ natelimStr₁ ∙ ft-star ∙ is-section₀ uₛ u₁ ∙ ap ft P= ∙ NatStr=

  field
    natelimStrNat : {n m : ℕ} (g : MorC n m) → ∀ {X P P= dO dS u} {dOₛ : is-section dO} {dO₁ : ∂₁ dO ≡ star (zeroStr X) P (zeroStr₁ ∙ ! P=)} {dSₛ : is-section dS} {dS₁ : T-dS₁ X P P= dS} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ft P} (p : X ≡ ∂₁ g)
                    (let zeroStr₀' = zeroStr₀ _ ∙ p)
                    (let p' = ap ft P= ∙ NatStr= ∙ p)
                    (let dO₀' = is-section₀ dOₛ dO₁ ∙ ft-star ∙ zeroStr₀')
                    (let dS₀' = ap ft (ap ft (is-section₀ dSₛ dS₁ ∙ ft-star ∙ pp₀) ∙ P=) ∙ NatStr= ∙ p)
                    (let u₀' = is-section₀ uₛ u₁ ∙ p')
                    (let nat = NatStrNat _ p)
                  → starTm g (natelimStr {n = m} X P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) (natelimStr₀ _ _ _ ∙ p)
                  ≡ natelimStr (∂₀ g) (star+ g P P= (NatStr= ∙ p)) (ft-star ∙ qq₀ ∙ nat)
                               (starTm g dO dO₀') ssₛ (starTm₁ dOₛ dO₀' dO₁ ∙ starstar zeroStrₛ zeroStr₀' p' P= ∙ ap2-irr star (zeroStrNat _ p) refl)
                               (starTm++ g dS dS₀') ssₛ (starTm++₁ g dS dSₛ (ft-star ∙ pp₀) P= dS₁ dS₀' ∙ star-pp (P= ∙ ! (varC₀ last _) ∙ ! (sucStr₀ _) ∙ ! ft-star) refl ∙ ap2-irr star refl (starstar sucStrₛ (sucStr₀ _ ∙ varC₀ last _ ∙ ! qq₁) (ap ft (ft-star ∙ qq₀) ∙ ft-star ∙ pp₀ ∙ ! qq₁) (ft-star ∙ qq₀) ∙ ap2-irr star (sucStrNat _ (varC₀ last _ ∙ ! qq₁) ∙ ap-irr2 sucStr (star-varCL ∙ ap ss (ap id nat))) (star-qqpp P= ∙ ap2-irr star (ap2-irr qq (ap pp nat) nat) refl)))
                               (starTm g u u₀') ssₛ (starTm₁ uₛ u₀' u₁ ∙ ap2-irr star refl P= ∙ ! qq₀ ∙ ! ft-star)

record CCatwithid (ccat : CCat) (ccatuu : CCatwithUU ccat) (ccatel : CCatwithEl ccat ccatuu) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu
  open CCatwithEl ccatel

  field
    idStr  : (i : ℕ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i (∂₀ a)) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ ElStr i a aₛ a₁)
                     (v : MorC n (suc n)) (vₛ : is-section v) (v₁ : ∂₁ v ≡ ElStr i a aₛ a₁) → MorC n (suc n)
    idStrₛ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i a aₛ a₁}
                     {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i a aₛ a₁} → is-section (idStr i a aₛ a₁ u uₛ u₁ v vₛ v₁)
    idStr₁ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i a aₛ a₁}
                     {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i a aₛ a₁} → ∂₁ (idStr i a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ UUStr i (∂₀ a)

  idStr₀ : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i a aₛ a₁}
                   {v : MorC n (suc n)} {vₛ : is-section v} (v₁ : ∂₁ v ≡ ElStr i a aₛ a₁) → ∂₀ (idStr i a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ ∂₀ a
  idStr₀ _ = is-section₀ idStrₛ idStr₁ ∙ UUStr=

  field
    idStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m)  {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i a aₛ a₁}
                                                {v : MorC m (suc m)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i a aₛ a₁} (p : ∂₀ a ≡ ∂₁ g)
                                                (let u₀ = is-section₀ uₛ u₁ ∙ ElStr= ∙ p) (let v₀ = is-section₀ vₛ v₁ ∙ ElStr= ∙ p)
             → starTm g (idStr i a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStr₀ _ ∙ p) ≡ idStr i (starTm g a p) ssₛ (starTm₁ aₛ p a₁ ∙ UUStrNat g p ∙ ap (UUStr i) (! (ss₀ ∙ comp₀)))
                                                                                   (starTm g u u₀) ssₛ (starTm₁ uₛ u₀ u₁ ∙ ElStrNat g p) (starTm g v v₀) ssₛ (starTm₁ vₛ v₀ v₁ ∙ ElStrNat g p)

record CCatwithrefl (ccat : CCat) (ccatid : CCatwithId ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithId ccatid

  field
    reflStr  : (A : Ob (suc n)) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) → MorC n (suc n)
    reflStrₛ : {A : Ob (suc n)} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → is-section (reflStr A a aₛ a₁)
    reflStr₁ : {A : Ob (suc n)} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → ∂₁ (reflStr A a aₛ a₁) ≡ IdStr A a aₛ a₁ a aₛ a₁

  reflStr₀ : {A : Ob (suc n)} {u : MorC n (suc n)} {uₛ : is-section u} (u₁ : ∂₁ u ≡ A) → ∂₀ (reflStr A u uₛ u₁) ≡ ft A
  reflStr₀ _ = is-section₀ reflStrₛ reflStr₁ ∙ IdStr=

  field
    reflStrNat : {n m : ℕ} (g : MorC n m) {A : Ob (suc m)} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ A} (p : ft A ≡ ∂₁ g)
                 (let u₀ = is-section₀ uₛ u₁ ∙ p)
             → starTm g (reflStr A u uₛ u₁) (reflStr₀ _ ∙ p) ≡ reflStr (star g A (! p)) (starTm g u u₀) ssₛ (starTm₁ uₛ u₀ u₁)



record CCatwithjj (ccat : CCat) (ccatid : CCatwithId ccat) (ccatrefl : CCatwithrefl ccat ccatid) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithId ccatid
  open CCatwithrefl ccatrefl

  T-d₁ : (A : Ob (suc n)) (P : Ob (suc (suc (suc (suc n)))))
         (P= : ft P ≡ IdStr (star (pp (star (pp A) A pp₁)) (star (pp A) A pp₁) pp₁) (ss (pp (star (pp A) A pp₁))) ssₛ (ss₁' (pp₁ ∙ ft-star ∙ pp₀) ∙ star-comp pp₁) (ss (id (star (pp A) A pp₁))) ssₛ (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl)) (d : MorC (suc n) (suc (suc n))) → Ob (suc (suc n))
  T-d₁ A P P= d =
    star (reflStr (star (pp A) A pp₁)
                  (ss (id A))
                  (ap2-irr comp (ap pp ss₁) refl ∙ ss-pp ∙ ap id (! ss₀))
                  (ss₁ ∙ ap2-irr star (id-left' (pp₀ ∙ id₁) ∙ ap pp id₁) id₁))
         (star (qq (ss (id A))
                   (IdStr
                     (star
                       (pp (star (pp A) A pp₁))
                       (star (pp A) A pp₁)
                       pp₁)
                     (ss (pp (star (pp A) A pp₁)))
                     (ap2-irr comp (ap pp ss₁) refl ∙ ss-pp ∙ ap id (! ss₀))
                     (ss₁' (pp₁ ∙ ft-star ∙ pp₀) ∙ star-comp pp₁)
                     (ss (id (star (pp A) A pp₁)))
                     (ap2-irr comp (ap pp ss₁) refl ∙ ss-pp ∙ ap id (! ss₀))
                     (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl))
                   (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl ∙ ! (IdStr= ∙ ft-star ∙ pp₀)))
               P
               (qq₁ ∙ ! P=))
         (reflStr₁
          ∙ ! (ft-star ∙ qq₀ ∙ (IdStrNat _ (ft-star ∙ pp₀ ∙ ! (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl)))
              ∙ ap-irr-IdStr {!(! (star-comp {p = ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl ∙ ! pp₀} pp₁) ∙ ap2-irr star (ap2-irr comp (ap pp (ap2-irr star (! (id-left' (pp₀ ∙ id₁) ∙ ap pp id₁)) (! id₁))) refl ∙ ss-pp ∙ ap id (id₀ ∙ ! (ft-star ∙ pp₀))) refl ∙ star-id)!}
                             {!(ss-comp {g₁ = comp₁ {p = pp₁ ∙ ft-star ∙ pp₀ ∙ ! id₀ ∙ ! comp₀ ∙ ! ft-star ∙ ! pp₀} ∙ pp₁ ∙ ap ft (ft-star ∙ comp₀)} {f₁ = comp₁ ∙ ss₁' (pp₁ ∙ ft-star) ∙ ap2-irr star (ap2-irr comp (ap pp (pp₀ ∙ ! id₀ ∙ ! comp₀ ∙ ! ft-star)) refl) (pp₀ ∙ ! id₀)} ∙ ap ss (! (assoc {q = ss₁' (pp₁ ∙ ft-star) ∙ ap2-irr star (ap2-irr comp (ap pp (pp₀ ∙ ! id₀ ∙ ! comp₀ ∙ ! ft-star)) refl) (pp₀ ∙ ! id₀) ∙ ! qq₀}) ∙ ap2-irr comp (ap2-irr comp (ap2-irr qq (! (ap2-irr comp (ap pp pp₁) (ap pp (ap2-irr star (id-left' (pp₀ ∙ id₁) ∙ ap pp id₁) id₁)))) (! (pp₁ ∙ ft-star ∙ comp₀))) (! (ap ss (ap pp (ap2-irr star (id-left' (pp₀ ∙ id₁) ∙ ap pp id₁) id₁)))) ∙ ! ss-qq) refl ∙ ss-pp ∙ ap id id₀) ∙ refl)!}
                             {!(ss-comp {g₁ = pp₁ ∙ ft-star ∙ pp₀ ∙ ! pp₀ ∙ ! ft-star ∙ ap ft (! id₁ ∙ ! id₁)} {f₁ = comp₁ ∙ ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) (! id₁ ∙ ! id₁)} ∙ ap ss (! (assoc {q = ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) (! id₁ ∙ ! id₁) ∙ ! qq₀}) ∙ ap2-irr comp (ap2-irr comp (ap2-irr qq (! (id-left' (pp₀ ∙ id₁) ∙ ap pp id₁)) id₁) refl ∙ ! ss-qq) refl ∙ id-right' (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl)) ∙ ss-comp {g₁ = pp₁} {f₁ = ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl} ∙ ap ss (ap2-irr comp (! (ap2-irr qq (id-left' (pp₀ ∙ id₁) ∙ ap pp id₁) id₁)) refl ∙ ! ss-qq))!}))

  field
    jjStr  : (A : Ob (suc n)) (P : Ob (suc (suc (suc (suc n)))))
             (P= : ft P ≡ IdStr (star (pp (star (pp A) A pp₁)) (star (pp A) A pp₁) pp₁) (ss (pp (star (pp A) A pp₁))) ssₛ (ss₁' (pp₁ ∙ ft-star ∙ pp₀) ∙ star-comp pp₁) (ss (id (star (pp A) A pp₁))) ssₛ (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl))
             (d : MorC (suc n) (suc (suc n))) (dₛ : is-section d)
             (d₁ : ∂₁ d ≡ T-d₁ A P P= d)
             (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A)
             (b : MorC n (suc n)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ A)
             (p : MorC n (suc n)) (pₛ : is-section p) (p₁ : ∂₁ p ≡ IdStr A a aₛ a₁ b bₛ b₁)
             → MorC n (suc n)
    jjStrₛ : ∀ {A P P= d a b p} {dₛ : is-section d} {d₁ : ∂₁ d ≡ T-d₁ A P P= d} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} {pₛ : is-section p} {p₁ : ∂₁ p ≡ IdStr A a aₛ a₁ b bₛ b₁}
           → is-section (jjStr {n = n} A P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁)
    jjStr₁ : ∀ {A P P= d a b p} {dₛ : is-section d} {d₁ : ∂₁ d ≡ T-d₁ A P P= d} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} {pₛ : is-section p} {p₁ : ∂₁ p ≡ IdStr A a aₛ a₁ b bₛ b₁}
           → ∂₁ (jjStr {n = n} A P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁)
             ≡ {!!}

  jjStr₀ : ∀ {A P P= d a b p} {dₛ : is-section d} {d₁ : ∂₁ d ≡ T-d₁ A P P= d} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} {pₛ : is-section p} (p₁ : ∂₁ p ≡ IdStr A a aₛ a₁ b bₛ b₁)
         → ∂₀ (jjStr {n = n} A P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁) ≡ ft A
  jjStr₀ p₁ = is-section₀ jjStrₛ jjStr₁ ∙ {!!}



record StructuredCCat : Set₁ where
  field
    ccat : CCat
    ccatUU : CCatwithUU ccat
    ccatEl : CCatwithEl ccat ccatUU
    ccatPi : CCatwithPi ccat
    ccatSig : CCatwithSig ccat
    ccatNat : CCatwithNat ccat
    ccatId : CCatwithId ccat
    ccatuu : CCatwithuu ccat ccatUU
    ccatpi : CCatwithpi ccat ccatUU ccatEl
    ccatlam : CCatwithlam ccat ccatPi
    ccatapp : CCatwithapp ccat ccatPi
    ccatsig : CCatwithsig ccat ccatUU ccatEl
    ccatpair : CCatwithpair ccat ccatSig
    ccatpr1 : CCatwithpr1 ccat ccatSig
    ccatpr2 : CCatwithpr2 ccat ccatSig ccatpr1
    ccatnat : CCatwithnat ccat ccatUU
    ccatzero : CCatwithzero ccat ccatNat
    ccatsuc : CCatwithsuc ccat ccatNat
    ccatnatelim : CCatwithnatelim ccat ccatNat ccatzero ccatsuc
    ccatid : CCatwithid ccat ccatUU ccatEl
    ccatrefl : CCatwithrefl ccat ccatId
    ccatjj : CCatwithjj ccat ccatId ccatrefl

  open CCat ccat renaming (Mor to MorC)
  open CCatwithUU ccatUU public
  open CCatwithEl ccatEl public
  open CCatwithPi ccatPi public
  open CCatwithSig ccatSig public
  open CCatwithNat ccatNat public
  open CCatwithId ccatId public
  open CCatwithuu ccatuu public
  open CCatwithpi ccatpi public
  open CCatwithlam ccatlam public
  open CCatwithapp ccatapp public
  open CCatwithsig ccatsig public
  open CCatwithpair ccatpair public
  open CCatwithpr1 ccatpr1 public
  open CCatwithpr2 ccatpr2 public
  open CCatwithnat ccatnat public
  open CCatwithzero ccatzero public
  open CCatwithsuc ccatsuc public
  open CCatwithnatelim ccatnatelim public
  open CCatwithid ccatid public
  open CCatwithrefl ccatrefl public
  open CCatwithjj ccatjj public

  field
    {- Additional structure corresponding to equality rules -}
    betaPiStr : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A}
            → appStr A B B= (lamStr A B B= u uₛ u₁) lamStrₛ lamStr₁ a aₛ a₁ ≡ starTm a u (is-section₀ uₛ refl ∙ ap ft u₁ ∙ B= ∙ ! a₁)
    betaSig1Str : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B (a₁ ∙ ! B=)} → pr1Str A B B= (pairStr A B B= a aₛ a₁ b bₛ b₁) pairStrₛ pairStr₁ ≡ a
    betaSig2Str : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B (a₁ ∙ ! B=)} → pr2Str A B B= (pairStr A B B= a aₛ a₁ b bₛ b₁) pairStrₛ pairStr₁ ≡ b

    eluuStr : {i : ℕ} {X : Ob n} → ElStr (suc i) (uuStr i X) uuStrₛ (uuStr₁ ∙ ap (UUStr (suc i)) (! (uuStr₀ _))) ≡ UUStr i X
    elpiStr : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)}
            → ElStr i (piStr i a aₛ a₁ b bₛ b₁) piStrₛ (piStr₁ ∙ ap (UUStr i) (! (piStr₀ _))) ≡ PiStr (ElStr i a aₛ a₁) (ElStr i b bₛ (b₁ ∙ ap (UUStr i) (! (is-section₀ bₛ b₁ ∙ UUStr=)))) (ElStr= ∙ is-section₀ bₛ b₁ ∙ UUStr=)
    elsigStr : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)}
            → ElStr i (sigStr i a aₛ a₁ b bₛ b₁) sigStrₛ (sigStr₁ ∙ ap (UUStr i) (! (sigStr₀ _))) ≡ SigStr (ElStr i a aₛ a₁) (ElStr i b bₛ (b₁ ∙ ap (UUStr i) (! (is-section₀ bₛ b₁ ∙ UUStr=)))) (ElStr= ∙ is-section₀ bₛ b₁ ∙ UUStr=)
    elnatStr : {i : ℕ} {X : Ob n} → ElStr i (natStr i X) natStrₛ (natStr₁ ∙ ap (UUStr i) (! (natStr₀ _))) ≡ NatStr X
    elidStr : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i a aₛ a₁}
                      {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i a aₛ a₁} → ElStr i (idStr i a aₛ a₁ u uₛ u₁ v vₛ v₁) idStrₛ (idStr₁ ∙ ap (UUStr i) (! (idStr₀ _))) ≡ IdStr (ElStr i a aₛ a₁) u uₛ u₁ v vₛ v₁


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
    open StructuredCCat
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
    UUStr→ : {n : ℕ} (i : ℕ) (X : Ob C n) → Ob→ (UUStr sC i X) ≡ UUStr sD i (Ob→ X)
    ElStr→ : (i : ℕ) (v : Mor C n (suc n)) (vₛ : is-section C v) (v₁ : ∂₁ C v ≡ UUStr sC i (∂₀ C v))
           → Ob→ (ElStr sC i v vₛ v₁) ≡ ElStr sD i (Mor→ v) (Mor→ₛ vₛ) (Mor→₁ v₁ ∙ UUStr→ _ _ ∙ ap (UUStr sD i) ∂₀→)
    PiStr→  : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) → Ob→ (PiStr sC A B B=) ≡ PiStr sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=)
    SigStr→ : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) → Ob→ (SigStr sC A B B=) ≡ SigStr sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=)
    NatStr→ : (X : Ob C n) → Ob→ (NatStr sC X) ≡ NatStr sD (Ob→ X)
    IdStr→  : (A : Ob C (suc n)) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ A) (b : Mor C n (suc n)) (bₛ : is-section C b) (b₁ : ∂₁ C b ≡ A)
            → Ob→ (IdStr sC A a aₛ a₁ b bₛ b₁) ≡ IdStr sD (Ob→ A) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁)


    uuStr→ : (i : ℕ) (X : Ob C n)
            → Mor→ (uuStr sC i X) ≡ uuStr sD i (Ob→ X)
    piStr→ : (i : ℕ) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ UUStr sC i (∂₀ C a)) (b : Mor C (suc n) (suc (suc n))) (bₛ : is-section C b) (b₁ : ∂₁ C b ≡ UUStr sC i (ElStr sC i a aₛ a₁))
            → Mor→ (piStr sC i a aₛ a₁ b bₛ b₁) ≡ piStr sD i (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ UUStr→ _ _ ∙ ap (UUStr sD i) ∂₀→) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁ ∙ UUStr→ _ _ ∙ ap (UUStr sD i) (ElStr→ _ _ _ _))
    lamStr→ : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (u : Mor C (suc n) (suc (suc n))) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ B)
            → Mor→ (lamStr sC A B B= u uₛ u₁) ≡ lamStr sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁)
    appStr→ : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (f : Mor C n (suc n)) (fₛ : is-section C f) (f₁ : ∂₁ C f ≡ PiStr sC A B B=) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ A)
            → Mor→ (appStr sC A B B= f fₛ f₁ a aₛ a₁) ≡ appStr sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ f) (Mor→ₛ fₛ) (Mor→₁ f₁ ∙ PiStr→ _ _ _) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁)
    sigStr→ : (i : ℕ) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ UUStr sC i (∂₀ C a)) (b : Mor C (suc n) (suc (suc n))) (bₛ : is-section C b) (b₁ : ∂₁ C b ≡ UUStr sC i (ElStr sC i a aₛ a₁))
            → Mor→ (sigStr sC i a aₛ a₁ b bₛ b₁) ≡ sigStr sD i (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ UUStr→ _ _ ∙ ap (UUStr sD i) ∂₀→) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁ ∙ UUStr→ _ _ ∙ ap (UUStr sD i) (ElStr→ _ _ _ _))
    pairStr→ : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ A) (b : Mor C n (suc n)) (bₛ : is-section C b) (b₁ : ∂₁ C b ≡ star C a B (a₁ ∙ ! B=))
            → Mor→ (pairStr sC A B B= a aₛ a₁ b bₛ b₁) ≡ pairStr sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁ ∙ star→)
    pr1Str→ : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (u : Mor C n (suc n)) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ SigStr sC A B B=)
            → Mor→ (pr1Str sC A B B= u uₛ u₁) ≡ pr1Str sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ SigStr→ _ _ _)
    pr2Str→ : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (u : Mor C n (suc n)) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ SigStr sC A B B=)
            → Mor→ (pr2Str sC A B B= u uₛ u₁) ≡ pr2Str sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ SigStr→ _ _ _)
    natStr→ : (i : ℕ) (X : Ob C n)
            → Mor→ (natStr sC i X) ≡ natStr sD i (Ob→ X)
    zeroStr→ : (X : Ob C n)
            → Mor→ (zeroStr sC X) ≡ zeroStr sD (Ob→ X)
    sucStr→ : (u : Mor C n (suc n)) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ NatStr sC (∂₀ C u))
            → Mor→ (sucStr sC u uₛ u₁) ≡ sucStr sD (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ NatStr→ _ ∙ ap (NatStr sD) ∂₀→)
    idStr→ : (i : ℕ) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ UUStr sC i (∂₀ C a)) (u : Mor C n (suc n)) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ ElStr sC i a aₛ a₁)
                     (v : Mor C n (suc n)) (vₛ : is-section C v) (v₁ : ∂₁ C v ≡ ElStr sC i a aₛ a₁)
            → Mor→ (idStr sC i a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ idStr sD i (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ UUStr→ _ _ ∙ ap (UUStr sD i) ∂₀→) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ ElStr→ _ _ _ _) (Mor→ v) (Mor→ₛ vₛ) (Mor→₁ v₁ ∙ ElStr→ _ _ _ _)
    reflStr→ : (A : Ob C (suc n)) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ A)
            → Mor→ (reflStr sC A a aₛ a₁) ≡ reflStr sD (Ob→ A) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁)


module _ {sC sD : StructuredCCat} where
  open StructuredCCatMor
  open StructuredCCat
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
