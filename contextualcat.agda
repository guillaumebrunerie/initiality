{-# OPTIONS --rewriting --prop --without-K  #-}

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
    comp :  (g : Mor m k) (f : Mor n m) {X : Ob m} (g₀ : ∂₀ g ≡ X) (f₁ : ∂₁ f ≡ X) → Mor n k
    comp₀ : {g : Mor m k} {f : Mor n m} {X : Ob m} {g₀ : ∂₀ g ≡ X} {f₁ : ∂₁ f ≡ X} → ∂₀ (comp g f g₀ f₁) ≡ ∂₀ f
    comp₁ : {g : Mor m k} {f : Mor n m} {X : Ob m} {g₀ : ∂₀ g ≡ X} {f₁ : ∂₁ f ≡ X} → ∂₁ (comp g f g₀ f₁) ≡ ∂₁ g
    -- father and projection
    ft  : Ob (suc n) → Ob n
    pp  : (X : Ob (suc n)) → Mor (suc n) n
    pp₀ : {X : Ob (suc n)} → ∂₀ (pp X) ≡ X
    pp₁ : {X : Ob (suc n)} → ∂₁ (pp X) ≡ ft X
    -- star and q
    star : (f : Mor m n) (X : Ob (suc n)) {Y : Ob n} (q : ft X ≡ Y) (f₁ : ∂₁ f ≡ Y) → Ob (suc m)
    qq   : (f : Mor m n) (X : Ob (suc n)) {Y : Ob n} (q : ft X ≡ Y) (f₁ : ∂₁ f ≡ Y) → Mor (suc m) (suc n)
    qq₀  : {f : Mor m n} {X : Ob (suc n)} {Y : Ob n} {q : ft X ≡ Y} {f₁ : ∂₁ f ≡ Y} → ∂₀ (qq f X q f₁) ≡ star f X q f₁
    qq₁  : {f : Mor m n} {X : Ob (suc n)} {Y : Ob n} {q : ft X ≡ Y} {f₁ : ∂₁ f ≡ Y} → ∂₁ (qq f X q f₁) ≡ X
    -- s
    ss  : (f : Mor m (suc n)) → Mor m (suc m)
    ss₀ : {f : Mor m (suc n)} → ∂₀ (ss f) ≡ ∂₀ f
    ss₁ : {f : Mor m (suc n)} {X : Ob (suc n)} {f₁ : ∂₁ f ≡ X} → ∂₁ (ss f) ≡ star (comp (pp X) f pp₀ f₁) X refl (comp₁ ∙ pp₁)
    -- terminal object
    pt : Ob 0
    pt-unique : (X : Ob 0) → X ≡ pt
    ptmor : Ob n → Mor n 0
    ptmor₀ : {X : Ob n} → ∂₀ (ptmor X) ≡ X
    ptmor₁ : {X : Ob n} → ∂₁ (ptmor X) ≡ pt
    ptmor-unique : (X : Ob n) (f : Mor n 0) (f₀ : ∂₀ f ≡ X) (f₁ : ∂₁ f ≡ pt) → f ≡ ptmor X
    -- identity laws and associativity
    id-right : {f : Mor n m} {X : Ob m} (f₁ : ∂₁ f ≡ X) → comp (id X) f id₀ f₁ ≡ f
    id-left  : {f : Mor n m} {X : Ob n} (f₀ : ∂₀ f ≡ X) → comp f (id X) f₀ id₁ ≡ f
    assoc : {h : Mor k l} {g : Mor m k} {f : Mor n m} {X : Ob m} {f₁ : ∂₁ f ≡ X} {g₀ : ∂₀ g ≡ X} {Y : Ob k} {g₁ : ∂₁ g ≡ Y} {h₀ : ∂₀ h ≡ Y} → comp (comp h g h₀ g₁) f (comp₀ ∙ g₀) f₁ ≡ comp h (comp g f g₀ f₁) h₀ (comp₁ ∙ g₁)
    -- properties of star and q
    ft-star : {f : Mor m n} {X : Ob (suc n)} {Y : Ob n} {p : ft X ≡ Y} {f₁ : ∂₁ f ≡ Y} → ft (star f X p f₁) ≡ ∂₀ f
    pp-qq   : {f : Mor m n} {X : Ob (suc n)} {Y : Ob n} {p : ft X ≡ Y} {f₁ : ∂₁ f ≡ Y} → comp (pp X) (qq f X p f₁) pp₀ qq₁ ≡ comp f (pp (star f X p f₁)) refl (pp₁ ∙ ft-star)
    star-id : {X : Ob (suc n)} {Y : Ob n} {p : ft X ≡ Y} → star (id Y) X p id₁ ≡ X
    qq-id : {X : Ob (suc n)}  {Y : Ob n} {p : ft X ≡ Y} → qq (id Y) X p id₁ ≡ id X
    star-comp : {m n k : ℕ} {g : Mor m k} {f : Mor n m} {Y : Ob m} {f₁ : ∂₁ f ≡ Y} {g₀ : ∂₀ g ≡ Y} {X : Ob (suc k)} {Z : Ob k} (p : ft X ≡ Z) (g₁ : ∂₁ g ≡ Z) → star (comp g f g₀ f₁) X p (comp₁ ∙ g₁) ≡ star f (star g X p g₁) (ft-star ∙ g₀) f₁
    qq-comp : {m n k : ℕ} {g : Mor m k} {f : Mor n m} {Y : Ob m} {f₁ : ∂₁ f ≡ Y} {g₀ : ∂₀ g ≡ Y} {X : Ob (suc k)} {Z : Ob k} (p : ft X ≡ Z) (g₁ : ∂₁ g ≡ Z) → qq (comp g f g₀ f₁) X p (comp₁ ∙ g₁) ≡ comp (qq g X p g₁) (qq f (star g X p g₁) (ft-star ∙ g₀) f₁) qq₀ qq₁
    -- properties of s
    ss-pp : {m n : ℕ} {f : Mor m (suc n)} {X : Ob m} (f₀ : ∂₀ f ≡ X) {Y : Ob (suc n)} (f₁ : ∂₁ f ≡ Y) → comp (pp (star (comp (pp Y) f pp₀ f₁) Y refl (comp₁ ∙ pp₁))) (ss f) pp₀ ss₁ ≡ id X
    ss-qq : {m n : ℕ} {f : Mor m (suc n)} {X : Ob (suc n)} {f₁ : ∂₁ f ≡ X} → f ≡ comp (qq (comp (pp X) f pp₀ f₁) X refl (comp₁ ∙ pp₁)) (ss f) qq₀ ss₁
    ss-comp : {m n k : ℕ} {U : Ob (suc k)} {X : Ob k} {p : ft U ≡ X} {g : Mor n k}  {g₁ : ∂₁ g ≡ X} {f : Mor m (suc n)} {f₁ : ∂₁ f ≡ star g U p g₁} → ss f ≡ ss (comp (qq g U p g₁) f qq₀ f₁)


  ap-irr-comp : {g g' : Mor m k} (g= : g ≡ g') {f f' : Mor n m} (f= : f ≡ f') {X X' : Ob m} {g₀ : ∂₀ g ≡ X} {g₀' : ∂₀ g' ≡ X'} {f₁ : ∂₁ f ≡ X} {f₁' : ∂₁ f' ≡ X'} → comp g f g₀ f₁ ≡ comp g' f' g₀' f₁'
  ap-irr-comp refl refl {g₀ = g₀} {g₀'} = ap-irr2 (λ X y z → comp _ _ {X = X} y z) (! g₀ ∙ g₀')

  ap-irr-qq : {f f' : Mor m n} (f= : f ≡ f') {X X' : Ob (suc n)} (X= : X ≡ X') {Y Y' : Ob n} {q : ft X ≡ Y} {q' : ft X' ≡ Y'} {f₁ : ∂₁ f ≡ Y} {f₁' : ∂₁ f' ≡ Y'} → qq f X q f₁ ≡ qq f' X' q' f₁'
  ap-irr-qq refl refl {q = q} {q'} = ap-irr2 (λ Y y z → qq _ _ {Y = Y} y z) (! q ∙ q')

  ap-irr-star : {f f' : Mor m n} (f= : f ≡ f') {X X' : Ob (suc n)} (X= : X ≡ X') {Y Y' : Ob n} {q : ft X ≡ Y} {q' : ft X' ≡ Y'} {f₁ : ∂₁ f ≡ Y} {f₁' : ∂₁ f' ≡ Y'} → star f X q f₁ ≡ star f' X' q' f₁'
  ap-irr-star refl refl {q = q} {q'} = ap-irr2 (λ Y y z → star _ _ {Y = Y} y z) (! q ∙ q')


  comp' : (g : Mor m k) (f : Mor n m) {X : Ob m}  (_ : ∂₀ g ≡ X) (_ : ∂₁ f ≡ X) → Mor n k
  comp' g f q p = comp g f (# q) (# p)

  star' : (f : Mor m n) (X : Ob (suc n)) {Y : Ob n} (q : ft X ≡ Y) (f₁ : ∂₁ f ≡ Y) → Ob (suc m)
  star' f X q f₁ = star f X (# q) (# f₁)

  qq' : (f : Mor m n) (X : Ob (suc n)) {Y : Ob n} (q : ft X ≡ Y) (f₁ : ∂₁ f ≡ Y) → Mor (suc m) (suc n)
  qq' f X q f₁ = qq f X (# q) (# f₁) 

  {- Sections of [pp] -}


  abstract
    is-section : (u : Mor n (suc n)) → Prop
    is-section u = comp' (pp (∂₁ u)) u pp₀ refl ≡ id (∂₀ u)
  
    is-section₀ : {u : Mor n (suc n)} {X : Ob (suc n)} (uₛ : is-section u) (u₁ : ∂₁ u ≡ X) → ∂₀ u ≡ ft X
    is-section₀ uₛ u₁ = ! id₁ ∙ ap ∂₁ (! uₛ) ∙ comp₁ ∙ pp₁ ∙ ap ft u₁

    ssₛ : {f : Mor m (suc n)} → is-section (ss f)
    ssₛ = ap3-irr2 comp (ap pp ss₁) refl ss₁ ∙ ss-pp refl refl ∙ ap id (! ss₀)
 
    is-section= : {X : Ob (suc n)} {Y : Ob n} (X= : ft X ≡ Y) (u : Mor n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ X) → comp (pp X) u pp₀ u₁ ≡ id Y
    is-section= refl u uₛ refl = uₛ ∙ ap id (is-section₀ uₛ refl)
  
  -- ss-comp-section₁ : (g : Mor m (suc m)) (f : Mor n m) {X : Ob m} (g₀ : ∂₀ g ≡ X) (f₁ : ∂₁ f ≡ X) (gₛ : is-section g) {Y : Ob (suc m)} (p : ft Y ≡ X) (g₁ : ∂₁ g ≡ Y) → ∂₁ (ss (comp g f g₀ f₁) (comp₁ ∙ g₁)) ≡ star f Y f₁ p
  -- ss-comp-section₁ g f g₀ f₁ gₛ p g₁ = ss₁ ∙ ap3-irr2 star {!gₛ!} {!!} {!!} --ss₁ ∙ ap3-irr2 star (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ fₛ ∙ ap id (! p)) refl ∙ id-right ) comp₁

    ss-of-section : (u : Mor n (suc n)) (uₛ : is-section u) → ss u ≡ u
    ss-of-section u uₛ = ! (ss-qq ∙ ap3-irr2 comp (ap3-irr2 qq (uₛ ∙ ap id (is-section₀ uₛ refl)) refl refl {e' = refl} ∙ qq-id) refl (ap3-irr2 star (uₛ ∙ ap id (is-section₀ uₛ refl)) refl refl {e' = refl} ∙ star-id) ∙ id-right (ss₁ ∙ (ap3-irr2 star (uₛ ∙ ap id (is-section₀ uₛ refl)) refl refl {e' = refl} ∙ star-id))) -- ! (ss-qq ∙ ap2-irr comp (ap2-irr qq uₛ refl {b' = id₁ ∙ is-section₀ uₛ refl} ∙ ap2-irr qq (ap id (! (ap ft ss₁ ∙ ft-star ∙ comp₀))) (! (ss₁ ∙ ap2-irr star (uₛ ∙ ap id (is-section₀ uₛ refl)) refl ∙ star-id)) ∙ qq-id) refl ∙ id-right)

  {- Iterated father and qq operations -}

  -- Take the prefix of the context up to spot [k]
  ft^ : (k : Fin (suc n)) (X : Ob n) → Ob (n -F' k)
  ft^ {n} last X = X
  ft^ {zero} (prev ()) X
  ft^ {suc n} (prev k) X = ft^ {n = n} k (ft X)

  -- Weaken [X] by adding [X+] at spot [k]
  star^ : (k : Fin (suc n)) (X+ : Ob (suc (n -F' k))) (X : Ob n) {Y : Ob (n -F' k)} (p : ft X+ ≡ Y) (q : ft^ k X ≡ Y) → Ob (suc n)
  qq^   : (k : Fin (suc n)) {X+ : Ob (suc (n -F' k))} {X : Ob n} {Y : Ob (n -F' k)} (p : ft X+ ≡ Y) (q : ft^ k X ≡ Y) → Mor (suc n) n
  qq^₁  : {k : Fin (suc n)} {X+ : Ob (suc (n -F' k))} {X : Ob n} {Y : Ob (n -F' k)} {p : ft X+ ≡ Y} {q : ft^ k X ≡ Y} → ∂₁ (qq^ k p q) ≡ X
  qq^₀  : {k : Fin (suc n)} {X+ : Ob (suc (n -F' k))} {X : Ob n} {Y : Ob (n -F' k)} {p : ft X+ ≡ Y} {q : ft^ k X ≡ Y} → ∂₀ (qq^ k p q) ≡ star^ k X+ X p q

  star^ last X+ X p q = X+
  star^ {n = zero} (prev ()) X+ X p q
  star^ {n = suc n} (prev k) X+ X p q = star' (qq^ k p q) X refl qq^₁

  abstract
    qq^ last {X+ = X+} p q = pp X+
    qq^ {n = zero} (prev ()) p q
    qq^ {n = suc n} (prev k) {X = X} p q = qq (qq^ k p q) X refl (qq^₁ {k = k} {p = p} {q = q})

    qq^₁ {n} {last} {p = p} {q} = pp₁ ∙ p ∙ ! q
    qq^₁ {zero} {prev ()}
    qq^₁ {suc n} {prev k} = qq₁

    qq^₀ {_} {last} = pp₀
    qq^₀ {zero} {prev ()}
    qq^₀ {suc n} {prev k} = qq₀

    qq^last : {X+ : Ob (suc n)} {X : Ob n} {p : ft X+ ≡ X} → qq^ last p refl ≡ pp X+
    qq^last = refl

    qq^prev : {k : Fin (suc n)} {X+ : Ob (suc (n -F' k))} {X : Ob (suc n)} {Y : Ob (n -F' k)} {p : ft X+ ≡ Y} {q : ft^ (prev k) X ≡ Y} → qq^ (prev k) p q ≡ qq (qq^ k p q) X refl (qq^₁ {k = k} {p = p} {q = q})
    qq^prev = refl

  qq^=p : {k : Fin (suc n)} {X : Ob n} {X+ : Ob (suc (n -F' k))} {Y : Ob (n -F' k)} {p : ft X+ ≡ Y} {q : ft^ k X ≡ Y} {X' : Ob n} {q' : ft^ k X' ≡ Y} (X= : X ≡ X') → qq^ k p q ≡ qq^ k p q'
  qq^=p refl = refl

  star^=p : {k : Fin (suc n)} {X : Ob n} {X+ : Ob (suc (n -F' k))} {Y : Ob (n -F' k)} {p : ft X+ ≡ Y} {q : ft^ k X ≡ Y} {X' : Ob n} {q' : ft^ k X' ≡ Y} (X= : X ≡ X') → star^ k X+ X p q ≡ star^ k X+ X' p q'
  star^=p refl = refl

  {- Other helper functions -}

--   ss₁' : {f : Mor m (suc n)} {X : Ob (suc n)} (p : ∂₁ f ≡ X) → ∂₁ (ss f) ≡ star (comp (pp X) f (p ∙ ! pp₀)) X (comp₁ ∙ pp₁)
--   ss₁' refl = ss₁

--   id-left' : {f : Mor n m} {X : Ob n} (p : ∂₀ f ≡ X) → comp f (id X) (id₁ ∙ ! p) ≡ f
--   id-left' refl = id-left

--   id-right' : {f : Mor n m} {X : Ob m} (p : ∂₁ f ≡ X) → comp (id X) f (p ∙ (! id₀)) ≡ f
--   id-right' refl = id-right

--   ss-pp' : {m n : ℕ} {f : Mor m (suc n)} {X : Ob m} (f₀ : ∂₀ f ≡ X) {Y : Ob (suc n)} (f₁ : ∂₁ f ≡ Y) → comp (pp (star (comp (pp Y) f (f₁ ∙ ! pp₀)) Y (comp₁ ∙ pp₁))) (ss f) (ss₁' f₁ ∙ ! pp₀) ≡ id X
--   ss-pp' refl refl = ss-pp

  star+ : (g : Mor n m) (X : Ob (suc (suc m))) {X' : Ob (suc m)} (X= : ft X ≡ X') {X'' : Ob m} (X'= : ft X' ≡ X'') (g₁ : ∂₁ g ≡ X'') → Ob (suc (suc n))
  star+ g X {X'} X= X'= g₁ = star' (qq' g X' X'= g₁) X X= qq₁

  star++ : (g : Mor n m) (X : Ob (suc (suc (suc m)))) {X' : Ob (suc (suc m))} (X= : ft X ≡ X') {X'' : Ob (suc m)} (X'= : ft X' ≡ X'') {X''' : Ob m} (X''= : ft X'' ≡ X''') (g₁ : ∂₁ g ≡ X''') → Ob (suc (suc (suc n)))
  star++ g X {X'} X= {X''} X'= {X'''} X''= g₁ = star' (qq' (qq' g X'' X''= g₁) X' X'= qq₁) X X= qq₁


  starTm : (g : Mor n m) {X : Ob m} (u : Mor m (suc m)) (u₀ : ∂₀ u ≡ X) (g₁ : ∂₁ g ≡ X) → Mor n (suc n)
  starTm g {X} u u₀ g₁ = ss (comp u g u₀ g₁)


  ap-irr-starTm : {f f' : Mor m n} (f= : f ≡ f') {u u' : Mor n (suc n)} (u= : u ≡ u') {Y Y' : Ob n} {u₀ : ∂₀ u ≡ Y} {u₀' : ∂₀ u' ≡ Y'} {f₁ : ∂₁ f ≡ Y} {f₁' : ∂₁ f' ≡ Y'} → starTm f u u₀ f₁ ≡ starTm f' u' u₀' f₁'
  ap-irr-starTm refl refl {u₀ = u₀} {u₀'} = ap-irr2 (λ X y z → starTm _ {X = X} _ y z) (! u₀ ∙ u₀')
  

  starTm₁ : (g : Mor n m) {X : Ob (suc m)} {X' : Ob m} (X= : ft X ≡ X') (u : Mor m (suc m)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ X) (g₁ : ∂₁ g ≡ X')  → ∂₁ (starTm g u (is-section₀ uₛ u₁ ∙ X=) g₁) ≡ star' g X X= g₁
  starTm₁ g X= u uₛ u₁ g₁ = ss₁ ∙ ap-irr-star (! assoc ∙ ap-irr-comp (is-section= X= u uₛ u₁) refl ∙ id-right g₁) refl 

  starTm+ : (g : Mor n m) {X : Ob (suc m)} {X' : Ob m} (X= : ft X ≡ X') (u : Mor (suc m) (suc (suc m))) (u₀ : ∂₀ u ≡ X) (g₁ : ∂₁ g ≡ X') → Mor (suc n) (suc (suc n))
  starTm+ g {X} X= u u₀ g₁ = ss (comp' u (qq g X X= g₁) u₀ qq₁) 
  
  starTm+₁ :(g : Mor n m) {X : Ob (suc (suc m))} {X' : Ob (suc m)} (X= : ft X ≡ X') {X'' : Ob m} (X'= : ft X' ≡ X'') (u : Mor (suc m) (suc (suc m))) (uₛ : is-section u) (u₁ : ∂₁ u ≡ X)  (g₁ : ∂₁ g ≡ X'') → ∂₁ (starTm+ g X'= u (is-section₀ uₛ u₁ ∙ X=) g₁) ≡ star+ g X X= X'= g₁
  starTm+₁ g {X} {X'} X= {X''} X'= u uₛ u₁ g₁ = starTm₁ (qq g X' X'= g₁) X= u uₛ u₁ qq₁

  starTm++ : (g : Mor n m) {X : Ob (suc (suc m))} {X' : Ob (suc m)} (X= : ft X ≡ X') {X'' : Ob m} (X'= : ft X' ≡ X'') (u : Mor (suc (suc m)) (suc (suc (suc m)))) (u₀ : ∂₀ u ≡ X) (g₁ : ∂₁ g ≡ X'')  → Mor (suc (suc n)) (suc (suc (suc n)))
  starTm++ g {X} {X'} X= {X''} X'= u u₀ g₁ = ss (comp' u (qq' (qq' g X' X'= g₁) X X= qq₁) u₀ qq₁) --ss (comp' u (qq' (qq' g (ft (∂₀ u)) g₁) (∂₀ u) qq₁) qq₁)

  starTm++₁ : (g : Mor n m) {X : Ob (suc (suc (suc m)))} {X' : Ob (suc (suc m))} (X= : ft X ≡ X') {X'' : Ob (suc m)} (X'= : ft X' ≡ X'') {X''' : Ob m} (X''= : ft X'' ≡ X''') (u : Mor (suc (suc m)) (suc (suc (suc m)))) (uₛ : is-section u) (u₁ : ∂₁ u ≡ X) (g₁ : ∂₁ g ≡ X''') → ∂₁ (starTm++ g X'= X''= u (is-section₀ uₛ u₁ ∙ X=) g₁) ≡ star++ g X X= X'= X''= g₁
  starTm++₁ g {X} {X'} X= {X''} X'= {X'''} X''= u uₛ u₁ g₁ = starTm+₁ (qq g X'' X''= g₁) X= X'= u uₛ u₁ qq₁
  --   -- starTm₁ {g = qq g (∂₀ u) (! p)} uₛ (! qq₁) u₁ ∙ ap2-irr star {a = qq g (∂₀ u) (! p)} (ap2-irr qq {a = g} refl (is-section₀ uₛ u₁) {b = ! p} {b' = ! (ap (ft) (! (is-section₀ uₛ u₁)) ∙ p)}) refl {b = ! (! (qq₁)) ∙ is-section₀ uₛ u₁} {b' = qq₁

  star-pp : {n m : ℕ} {g : Mor n m} {A : Ob (suc m)} {B : Ob (suc m)} {X : Ob m} (A= : ft A ≡ X) (B= : ft B ≡ X) (g₁ : ∂₁ g ≡ X)
           → star (qq g A A= g₁) (star (pp A) B B= (pp₁ ∙ A=)) (ft-star ∙ pp₀) qq₁ ≡ star' (pp (star' g A A= g₁)) (star' g B B= g₁) ft-star (pp₁ ∙ ft-star)
  star-pp A= B= g₁ = ! (star-comp B= (pp₁ ∙ A=)) ∙ ap-irr-star pp-qq refl ∙ star-comp B= g₁
    -- ! (star-comp {p = qq₁ ∙ r ∙ ! pp₀} _)
    -- ∙ ap2-irr star (ap2-irr comp (ap pp (! r)) refl ∙ pp-qq) refl
    -- ∙ star-comp (w1 ∙ q)

  star-pp' : {n : ℕ} {g : Mor n (suc n)} {A : Ob (suc n)} {B : Ob (suc n)} {X : Ob n} (A= : ft A ≡ X) (B= : ft B ≡ X) (gₛ : is-section g) (g₁ : ∂₁ g ≡ A)
           → star g (star (pp A) B  B= (pp₁ ∙ A=)) (ft-star ∙ pp₀) g₁  ≡ B
  star-pp' {g = g} A= B= gₛ g₁ = ! (star-comp B= (pp₁ ∙ A=)) ∙ ap-irr-star (is-section= A= g gₛ g₁) refl {q' = B=} ∙ star-id -- ! (star-comp {p = w2 ∙ ft-star} _) ∙ ap2-irr star (ap2-irr comp (ap pp (! (w2 ∙ ft-star ∙ pp₀))) refl ∙ gₛ ∙ ap id (is-section₀ gₛ (w2 ∙ ft-star ∙ pp₀) ∙ ! pp₁ ∙ w1)) refl ∙ star-id ∙ refl

  

  star-qqpp : {n m : ℕ} {g : Mor n m} {B : Ob (suc (suc m))} {A : Ob (suc m)} (B= : ft B ≡ A) {X : Ob m} (A= : ft A ≡ X)
            → (g₁ : ∂₁ g ≡ X)
            → star (qq (qq g A A= g₁) (star (pp A) A A= (pp₁ ∙ A=)) (ft-star ∙ pp₀) qq₁) (star (qq (pp A) A A= (pp₁ ∙ A=)) B B= qq₁) (ft-star ∙ qq₀) qq₁
              ≡ star (qq (pp (star g A A= g₁)) (star g A A= g₁) ft-star (pp₁ ∙ ft-star)) (star (qq g A A= g₁) B B= qq₁) (ft-star ∙ qq₀) qq₁
  star-qqpp B= A= g₁ = ! (star-comp B= qq₁) ∙ ap-irr-star (! (qq-comp A= (pp₁ ∙ A=)) ∙ ap-irr-qq pp-qq refl ∙ qq-comp A= g₁) refl ∙ star-comp B= qq₁
--     ! (star-comp _)
--     ∙ ap2-irr star (! (qq-comp _) ∙ ap2-irr qq pp-qq refl ∙ qq-comp _) refl
--     ∙ star-comp _

  star-qqpp' : {n m : ℕ} {g : Mor n m} {B : Ob (suc (suc m))} {A : Ob (suc m)} (B= : ft B ≡ A) {X : Ob m} (A= : ft A ≡ X)
             → (g₁ : ∂₁ g ≡ X) {C : Ob _} (C= : star (pp A) A A= (pp₁ ∙ A=) ≡ C)
             → star (qq (qq g A A= g₁) C (ap ft (! C=) ∙ ft-star ∙ pp₀) qq₁) (star (qq (pp A) A A= (pp₁ ∙ A=)) B B= qq₁) (ft-star ∙ qq₀ ∙ C=) qq₁
               ≡ star (qq (pp (star g A A= g₁)) (star g A A= g₁) ft-star (pp₁ ∙ ft-star)) (star (qq g A A= g₁) B B= qq₁) (ft-star ∙ qq₀) qq₁
  star-qqpp' B= A= g₁ refl = ! (star-comp B= qq₁) ∙ ap-irr-star (! (qq-comp A= (pp₁ ∙ A=)) ∙ ap-irr-qq pp-qq refl ∙ qq-comp A= g₁) refl ∙ star-comp B= qq₁

  starstar : (g : Mor n m) (B : Ob (suc (suc m))) {A : Ob (suc m)} (B= : ft B ≡ A) {X : Ob m} (A= : ft A ≡ X) (g₁ : ∂₁ g ≡ X) (a : Mor m (suc m)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A)
         → star g (star a B B= a₁) (ft-star ∙ is-section₀ aₛ a₁ ∙ A=) g₁ ≡ star (starTm g a (is-section₀ aₛ a₁ ∙ A=) g₁) (star (qq g A A= g₁) B B= qq₁) (ft-star ∙ qq₀) (starTm₁ g A= a aₛ a₁ g₁)
  starstar g B B= A= g₁ a aₛ a₁ = ! (star-comp B= a₁) ∙ ap-irr-star (ss-qq ∙ ap-irr-comp (ap-irr-qq (! assoc ∙ ap-irr-comp (is-section= A= a aₛ a₁) refl ∙ id-right g₁) refl) refl {g₀' = qq₀}) refl ∙ star-comp B= qq₁
  --! (star-comp {p = ! a₀} a₁) ∙ ap2-irr star (ss-qq ∙ ap2-irr comp (ap2-irr qq (! (assoc {q = ! (pp₀ ∙ comp₁)}) ∙ ap2-irr comp (ap2-irr comp (ap pp comp₁) refl ∙ aₛ ∙ ap id a₀) refl ∙ id-right) (comp₁ ∙ a₁)) refl) refl ∙ star-comp {p = starTm₁ aₛ a₀ a₁ ∙ ! qq₀} qq₁ ∙ ap-irr (star _) (ap2-irr star (ap2-irr qq refl q) refl)

  star-varCL : {g : Mor n m} {A : Ob (suc m)} {X : Ob m} {A= : ft A ≡ X} {g₁ : ∂₁ g ≡ X} → starTm (qq g A A= g₁) (ss (id A)) (ss₀ ∙ id₀) qq₁ ≡ ss (id (star g A A= g₁))
  star-varCL {A = A} = ss-comp {U = A} ∙ ap ss (! assoc ∙ ap-irr-comp (! (ss-qq {f₁ = id₁})) refl ∙ id-right qq₁) ∙ ! (ss-comp {U = A} ∙ ap ss (id-left qq₀)) --ss-comp {f₁ = comp₁ ∙ ss₁} ∙ ap ss (! (assoc {q = ss₁ ∙ ! qq₀}) ∙ ap2-irr comp (! ss-qq) refl ∙ id-right qq₁) ∙ ap ss (! (id-left qq₀)) ∙ ! (ss-comp {f₁ = id₁})

  star-varCL' : {g : Mor (suc n) (suc m)} {A : Ob (suc m)} {g₁ : ∂₁ g ≡ A} → starTm g (ss (id A)) (ss₀ ∙ id₀) g₁ ≡ ss g
  star-varCL' {g₁ = g₁} = ss-comp  ∙ ap ss (! assoc ∙ ap-irr-comp (! (ss-qq {f₁ = id₁})) refl ∙ id-right g₁) --ss-comp {f₁ = comp₁ ∙ ss₁' id₁} ∙ ap ss (! (assoc {q = ss₁' id₁ ∙ ! qq₀}) ∙ ap2-irr comp (ap2-irr comp (ap2-irr qq (ap2-irr comp (ap pp (! id₁)) refl) (! id₁)) refl ∙ ! ss-qq) refl ∙ id-right' p)

  star-varCL'' : {g : Mor m (suc k)} {f : Mor n m}  {X : Ob m} {g₀ : ∂₀ g ≡ X} {f₁ : ∂₁ f ≡ X} → starTm f (ss g) (ss₀ ∙ g₀) f₁ ≡ ss (comp g f g₀ f₁)
  star-varCL'' = ss-comp  ∙ ap ss (! assoc ∙ ap-irr-comp (! (ss-qq {f₁ = refl})) refl) --ss-comp {f₁ = comp₁ ∙ ss₁} ∙ ap ss (! (assoc {q = ss₁ ∙ ! qq₀}) ∙ ap2-irr comp (! ss-qq) refl)

  pp^  : (k : Fin n) → Ob n → Mor n (n -F k)
  pp^₀ : (k : Fin n) (X : Ob n) → ∂₀ (pp^ k X) ≡ X

  pp^ last X = id X
  pp^ (prev last) X = pp X
  pp^ (prev k@(prev _)) X = comp (pp^ k (ft X)) (pp X) (pp^₀ k (ft X)) pp₁ -- (pp₁ ∙ ! (pp^₀ k (ft X)))

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

  varCₛ : (k : Fin n)(X : Ob n) → is-section (varC k X)
  varCₛ k X = ssₛ

  varC₀ : (k : Fin n) (X : Ob n) → ∂₀ (varC k X) ≡ X
  varC₀ k X = ss₀ ∙ pp^₀ k X

  varCL₁ : {X : Ob (suc n)} {Y : Ob n} {X= : ft X ≡ Y} → ∂₁ (varC last X) ≡ star (pp X) X X= (pp₁ ∙ X=)
  varCL₁ = ss₁ ∙ ap-irr-star (id-left pp₀) refl --ap2-irr star (id-left' pp₀) refl

  varC+₁ : (k : Fin n) {X : Ob (suc n)} {Y : Ob n} (Y= : ft X ≡ Y) {Z : Ob (suc n)} (var₁ : ∂₁ (varC k Y) ≡ Z) → ∂₁ (varC (prev k) X) ≡ star (pp X) Z (! (is-section₀ (varCₛ k Y) var₁) ∙ varC₀ k Y) (pp₁ ∙ Y=)
  varC+₁ last refl refl = ss₁ {f₁ = pp₁} ∙ star-comp refl pp₁ ∙ ap-irr-star refl (! varCL₁) --ap-irr-star refl (! varCL₁) refl --ss₁ ∙ star-comp pp₁ ∙ ? --ap2-irr star refl (! varCL₁)
  varC+₁ (prev k) {X = X} {Y = Y}  refl refl = ss₁ ∙ ap-irr-star (! (assoc {g₁ = pp^₁ (prev k) (ft X)})) refl ∙ star-comp refl (comp₁ ∙ pp₁) ∙ (ap-irr-star refl (! ss₁)) --ap-irr-star refl (! ss₁) refl -- ap2-irr star (! (assoc {q = pp^₁ (prev k) (ft X) ∙ ! pp₀})) refl ∙ star-comp (comp₁ ∙ pp₁) ∙ ap2-irr star refl (ap2-irr star (ap2-irr comp (ap pp (! (pp^₁ (prev k) _))) refl) (! (pp^₁ (prev k) _)) ∙ ! ss₁)
  
  ss-id₁ : {X : Ob (suc n)} {Y : Ob n} {X= : ft X ≡ Y} → ∂₁ (ss (id X)) ≡ star (pp X) X X= (pp₁ ∙ X=)
  ss-id₁ = ss₁ ∙ ap-irr-star (id-left pp₀) refl --ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl

{- Contextual categories with structure corresponding to the type theory we are interested in -}

record CCatwithUU (ccat : CCat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)

  field
    UUStr  : (i : ℕ) (Γ : Ob n) → Ob (suc n)
    UUStr= : {i : ℕ} {Γ : Ob n} → ft (UUStr i Γ) ≡ Γ
    UUStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} (g₁ : ∂₁ g ≡ Γ)
             → star g (UUStr i Γ) UUStr= g₁ ≡ UUStr i Δ

record CCatwithEl (ccat : CCat) (ccatuu : CCatwithUU ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu

  field
    ElStr  : (i : ℕ) (Γ : Ob n) (v : MorC n (suc n)) (vₛ : is-section v) (v₁ : ∂₁ v ≡ UUStr i Γ) → Ob (suc n)
    ElStr= : {i : ℕ} {Γ : Ob n} {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ UUStr i Γ} → ft (ElStr i Γ v vₛ v₁) ≡ Γ
    ElStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {v : MorC m (suc m)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ UUStr i Γ} (g₁ : ∂₁ g ≡ Γ)
             → star g (ElStr i Γ v vₛ v₁) ElStr= g₁ ≡ ElStr i Δ (starTm g v (is-section₀ vₛ v₁ ∙ UUStr=) g₁) ssₛ (starTm₁ g UUStr= v vₛ v₁ g₁ ∙ UUStrNat g g₀ g₁)

record CCatwithPi (ccat : CCat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)

  field
    PiStr  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) → Ob (suc n)
    PiStr= : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} → ft (PiStr Γ A A= B B=) ≡ Γ
    PiStrNat : {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} (g₁ : ∂₁ g ≡ Γ)
             → star g (PiStr Γ A A= B B=) PiStr= g₁ ≡ PiStr Δ (star g A A= g₁) (ft-star ∙ g₀) (star+ g B B= A= g₁) (ft-star ∙ qq₀)

record CCatwithSig (ccat : CCat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)

  field
    SigStr  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) → Ob (suc n)
    SigStr= : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} → ft (SigStr Γ A A= B B=) ≡ Γ
    SigStrNat : {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} (g₁ : ∂₁ g ≡ Γ)
             → star g (SigStr Γ A A= B B=) SigStr= g₁ ≡ SigStr Δ (star g A A= g₁) (ft-star ∙ g₀) (star+ g B B= A= g₁) (ft-star ∙ qq₀)

record CCatwithNat (ccat : CCat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)

  field
    NatStr  : (Γ : Ob n) → Ob (suc n)
    NatStr= : {Γ : Ob n} → ft (NatStr Γ) ≡ Γ
    NatStrNat : {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} (g₁ : ∂₁ g ≡ Γ)
             → star g (NatStr Γ) NatStr= g₁ ≡ NatStr Δ

  
record CCatwithId (ccat : CCat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)

  field
    IdStr   : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) (b : MorC n (suc n)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ A) → Ob (suc n)
    IdStr=  : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} → ft (IdStr Γ A A= a aₛ a₁ b bₛ b₁) ≡ Γ
    IdStrNat : {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC m (suc m)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} (g₁ : ∂₁ g ≡ Γ)
             (let a₀ = is-section₀ aₛ a₁ ∙ A=) (let b₀ = is-section₀ bₛ b₁ ∙ A=)
             → star g (IdStr Γ A A= a aₛ a₁ b bₛ b₁) IdStr= g₁ ≡ IdStr Δ (star g A A= g₁) (ft-star ∙ g₀) (starTm g a a₀ g₁) ssₛ (starTm₁ g A= a aₛ a₁ g₁) (starTm g b b₀ g₁) ssₛ (starTm₁ g A= b bₛ b₁ g₁)
             
  ap-irr-IdStr : {Γ Γ' : Ob n} (rΓ : Γ ≡ Γ') {A A' : Ob (suc n)} (rA : A ≡ A') {A= : ft A ≡ Γ} {A'= : ft A' ≡ Γ'} {u u' : MorC n (suc n)}(ru : u ≡ u') {uₛ : is-section u} {u₁ : ∂₁ u ≡ A} {uₛ' : is-section u'} {u₁' : ∂₁ u' ≡ A'}  {v v' : MorC n (suc n)} (rv : v ≡ v'){vₛ : is-section v} {v₁ : ∂₁ v ≡ A} {vₛ' : is-section v'} {v₁' : ∂₁ v' ≡ A'}  → IdStr Γ A A= u uₛ u₁ v vₛ v₁ ≡ IdStr Γ' A' A'= u' uₛ' u₁' v' vₛ' v₁'
  ap-irr-IdStr refl refl refl refl = refl

record CCatwithuu (ccat : CCat) (ccatuu : CCatwithUU ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu

  field
    uuStr  : (i : ℕ) (Γ : Ob n) → MorC n (suc n)
    uuStrₛ : {i : ℕ} {Γ : Ob n} → is-section (uuStr i Γ)
    uuStr₁ : {i : ℕ} {Γ : Ob n} → ∂₁ (uuStr i Γ) ≡ UUStr (suc i) Γ

  uuStr₀ : {i : ℕ} {Γ : Ob n} → ∂₀ (uuStr i Γ) ≡ Γ
  uuStr₀ {_} = is-section₀ uuStrₛ uuStr₁ ∙ UUStr=

  field
    uuStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} (g₁ : ∂₁ g ≡ Γ)
             → starTm g (uuStr i Γ) uuStr₀ g₁ ≡ uuStr i Δ

record CCatwithpi (ccat : CCat) (ccatuu : CCatwithUU ccat) (ccatel : CCatwithEl ccat ccatuu) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu
  open CCatwithEl ccatel

  field
    piStr  : (i : ℕ) (Γ : Ob n) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i Γ) (b : MorC (suc n) (suc (suc n))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)) → MorC n (suc n)
    piStrₛ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} → is-section (piStr i Γ a aₛ a₁ b bₛ b₁)
    piStr₁ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} → ∂₁ (piStr i Γ a aₛ a₁ b bₛ b₁) ≡ UUStr i Γ

  piStr₀ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} → ∂₀ (piStr i Γ a aₛ a₁ b bₛ b₁) ≡ Γ
  piStr₀ {_} = is-section₀ piStrₛ piStr₁ ∙ UUStr=

  field
    piStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ}
                                                {b : MorC (suc m) (suc (suc m))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} (g₁ : ∂₁ g ≡ Γ)
                                                (let a₀ = is-section₀ aₛ a₁ ∙ UUStr=) (let b₀ = is-section₀ bₛ b₁ ∙ UUStr=)                                                
             → starTm g (piStr i Γ a aₛ a₁ b bₛ b₁) piStr₀ g₁ ≡ piStr i Δ (starTm g a a₀ g₁)  ssₛ (starTm₁ g UUStr= a aₛ a₁ g₁ ∙ UUStrNat g g₀ g₁)
                                                                           (starTm+ g ElStr= b b₀ g₁) ssₛ (starTm+₁ g UUStr= ElStr= b bₛ b₁ g₁ ∙ UUStrNat (qq g (ElStr i Γ a aₛ a₁) ElStr= g₁) (qq₀ ∙ ElStrNat g g₀ g₁) qq₁)

record CCatwithlam (ccat : CCat) (ccatpi : CCatwithPi ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithPi ccatpi

  field
    lamStr  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (u : MorC (suc n) (suc (suc n))) (uₛ : is-section u) (u₁ : ∂₁ u ≡ B) → MorC n (suc n)
    lamStrₛ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} → is-section (lamStr Γ A A= B B= u uₛ u₁)
    lamStr₁ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} → ∂₁ (lamStr Γ A A= B B= u uₛ u₁) ≡ PiStr Γ A A= B B=

  lamStr₀ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} → ∂₀ (lamStr Γ A A= B B= u uₛ u₁) ≡ Γ
  lamStr₀ {_} = is-section₀ lamStrₛ lamStr₁ ∙ PiStr=

  field
    lamStrNat : {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {u : MorC (suc m) (suc (suc m))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} (g₁ : ∂₁ g ≡ Γ) (let u₀ = is-section₀ uₛ u₁ ∙ B=)
             → starTm g (lamStr Γ A A= B B= u uₛ u₁) lamStr₀ g₁  ≡ lamStr Δ (star g A A= g₁) (ft-star ∙ g₀) (star+ g B B= A= g₁) (ft-star ∙ qq₀) (starTm+ g A= u u₀ g₁) ssₛ (starTm+₁ g B= A= u uₛ u₁ g₁)

record CCatwithapp (ccat : CCat) (ccatpi : CCatwithPi ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithPi ccatpi

  field
    appStr  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (f : MorC n (suc n)) (fₛ : is-section f) (f₁ : ∂₁ f ≡ PiStr Γ A A= B B=) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) → MorC n (suc n)
    appStrₛ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {f : MorC n (suc n)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr Γ A A= B B=} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → is-section (appStr Γ A A= B B= f fₛ f₁ a aₛ a₁)
    appStr₁ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {f : MorC n (suc n)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr Γ A A= B B=} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → ∂₁ (appStr Γ A A= B B= f fₛ f₁ a aₛ a₁) ≡ star a B B= a₁

  appStr₀ :  {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ}  {B : Ob (suc (suc n))} {B= : ft B ≡ A} {f : MorC n (suc n)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr Γ A A= B B=} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → ∂₀ (appStr Γ A A= B B= f fₛ f₁ a aₛ a₁) ≡ Γ
  appStr₀ {_} {_} {_} {A=} {_} {_} {_} {_} {_} {_} {aₛ} {a₁} = is-section₀ appStrₛ appStr₁ ∙ ft-star ∙ is-section₀ aₛ a₁ ∙ A=

  field
    appStrNat : {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {f : MorC m (suc m)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr Γ A A= B B=}
                {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} (g₁ : ∂₁ g ≡ Γ)
                (let a₀ = is-section₀ aₛ a₁ ∙ A=) (let f₀ = is-section₀ fₛ f₁ ∙ PiStr=)
             → starTm g (appStr Γ A A= B B= f fₛ f₁ a aₛ a₁) appStr₀ g₁
                ≡ appStr Δ (star g A A= g₁)
                           (ft-star ∙ g₀)
                           (star+ g B B= A= g₁)
                           (ft-star ∙ qq₀)
                           (starTm g f f₀ g₁) ssₛ (starTm₁ g PiStr= f fₛ f₁ g₁ ∙ PiStrNat g g₀ g₁)
                           (starTm g a a₀ g₁) ssₛ (starTm₁ g A= a aₛ a₁ g₁)

record CCatwithsig (ccat : CCat) (ccatuu : CCatwithUU ccat) (ccatel : CCatwithEl ccat ccatuu) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu
  open CCatwithEl ccatel

  field
    sigStr  : (i : ℕ) (Γ : Ob n) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i Γ) (b : MorC (suc n) (suc (suc n))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)) → MorC n (suc n)
    sigStrₛ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} → is-section (sigStr i Γ a aₛ a₁ b bₛ b₁)
    sigStr₁ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} → ∂₁ (sigStr i Γ a aₛ a₁ b bₛ b₁) ≡ UUStr i Γ

  sigStr₀ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} → ∂₀ (sigStr i Γ a aₛ a₁ b bₛ b₁) ≡ Γ
  sigStr₀ {_} = is-section₀ sigStrₛ sigStr₁ ∙ UUStr=

  field
    sigStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ}
                                                 {b : MorC (suc m) (suc (suc m))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} (g₁ : ∂₁ g ≡ Γ)
                                                 (let a₀ = is-section₀ aₛ a₁ ∙ UUStr=) (let b₀ = is-section₀ bₛ b₁ ∙ UUStr=)                                                
             → starTm g (sigStr i Γ a aₛ a₁ b bₛ b₁) sigStr₀ g₁ ≡ sigStr i Δ (starTm g a a₀ g₁) ssₛ (starTm₁ g UUStr= a aₛ a₁ g₁ ∙ UUStrNat g g₀ g₁)
                                                                              (starTm+ g ElStr= b b₀ g₁) ssₛ (starTm+₁ g UUStr= ElStr= b bₛ b₁ g₁ ∙ UUStrNat (qq g (ElStr i Γ a aₛ a₁) ElStr= g₁) (qq₀ ∙ ElStrNat g g₀ g₁) qq₁)
                                                                           
record CCatwithpair (ccat : CCat) (ccatsig : CCatwithSig ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithSig ccatsig

  field
    pairStr  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) (b : MorC n (suc n)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ star a B B= a₁) → MorC n (suc n)
    pairStrₛ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B B= a₁} → is-section (pairStr Γ A A= B B= a aₛ a₁ b bₛ b₁)
    pairStr₁ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B B= a₁} → ∂₁ (pairStr Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ SigStr Γ A A= B B=

  pairStr₀ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B B= a₁} → ∂₀ (pairStr Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ Γ
  pairStr₀ {_} = is-section₀ pairStrₛ pairStr₁ ∙ SigStr=
  field
    pairStrNat : {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC m (suc m)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B B= a₁} (g₁ : ∂₁ g ≡ Γ)
                 (let a₀ = is-section₀ aₛ a₁ ∙ A=) (let b₀ = is-section₀ bₛ b₁ ∙ ft-star ∙ a₀)
             → starTm g (pairStr Γ A A= B B= a aₛ a₁ b bₛ b₁) pairStr₀ g₁ ≡ pairStr Δ (star g A A= g₁)
                                                                                      (ft-star ∙ g₀)
                                                                                      (star+ g B B= A= g₁)
                                                                                      (ft-star ∙ qq₀)
                                                                                      (starTm g a a₀ g₁) ssₛ (starTm₁ g A= a aₛ a₁ g₁)
                                                                                      (starTm g b b₀ g₁) ssₛ (starTm₁ g (ft-star ∙ a₀) b bₛ b₁ g₁ ∙ starstar g B B= A= g₁ a aₛ a₁)
                                                                                      
record CCatwithpr1 (ccat : CCat) (ccatsig : CCatwithSig ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithSig ccatsig

  field
    pr1Str  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ SigStr Γ A A= B B=) → MorC n (suc n)
    pr1Strₛ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} → is-section (pr1Str Γ A A= B B= u uₛ u₁)
    pr1Str₁ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} → ∂₁ (pr1Str Γ A A= B B= u uₛ u₁) ≡ A

  pr1Str₀ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} → ∂₀ (pr1Str Γ A A= B B= u uₛ u₁) ≡ Γ
  pr1Str₀ {_} {_} {_} {A=} = is-section₀ pr1Strₛ pr1Str₁ ∙ A=

  field
    pr1StrNat : {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} (g₁ : ∂₁ g ≡ Γ)
                (let u₀ = is-section₀ uₛ u₁ ∙ SigStr=)
             → starTm g (pr1Str Γ A A= B B= u uₛ u₁) pr1Str₀ g₁ ≡ pr1Str Δ (star g A A= g₁)
                                                                           (ft-star ∙ g₀)
                                                                           (star+ g B B= A= g₁)
                                                                           (ft-star ∙ qq₀)
                                                                           (starTm g u u₀ g₁) ssₛ (starTm₁ g SigStr= u uₛ u₁ g₁ ∙ SigStrNat g g₀ g₁)

record CCatwithpr2 (ccat : CCat) (ccatsig : CCatwithSig ccat) (ccatpr1 : CCatwithpr1 ccat ccatsig) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithSig ccatsig
  open CCatwithpr1 ccatpr1

  field
    pr2Str  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ SigStr Γ A A= B B=) → MorC n (suc n)
    pr2Strₛ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} → is-section (pr2Str Γ A A= B B= u uₛ u₁)
    pr2Str₁ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} → ∂₁ (pr2Str Γ A A= B B= u uₛ u₁) ≡ star (pr1Str Γ A A= B B= u uₛ u₁) B B= pr1Str₁

  pr2Str₀ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} → ∂₀ (pr2Str Γ A A= B B= u uₛ u₁) ≡ Γ
  pr2Str₀ {_} = is-section₀ pr2Strₛ pr2Str₁ ∙ ft-star ∙ pr1Str₀

  field
    pr2StrNat : {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} (g₁ : ∂₁ g ≡ Γ)
                (let u₀ = is-section₀ uₛ u₁ ∙ SigStr=)
             → starTm g (pr2Str Γ A A= B B= u uₛ u₁) pr2Str₀ g₁ ≡ pr2Str Δ (star g A A= g₁)
                                                                           (ft-star ∙ g₀)
                                                                           (star+ g B B= A= g₁)
                                                                           (ft-star ∙ qq₀)
                                                                           (starTm g u u₀ g₁) ssₛ (starTm₁ g SigStr= u uₛ u₁ g₁ ∙ SigStrNat g g₀ g₁)

record CCatwithnat (ccat : CCat) (ccatuu : CCatwithUU ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu

  field
    natStr  : (i : ℕ) (Γ : Ob n) → MorC n (suc n)
    natStrₛ : {i : ℕ} {Γ : Ob n} → is-section (natStr i Γ)
    natStr₁ : {i : ℕ} {Γ : Ob n} → ∂₁ (natStr i Γ) ≡ UUStr i Γ

  natStr₀ : {i : ℕ} {X : Ob n} → ∂₀ (natStr i X) ≡ X
  natStr₀ {_} = is-section₀ natStrₛ natStr₁ ∙ UUStr=

  field
    natStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} (g₁ : ∂₁ g ≡ Γ)
             → starTm g (natStr i Γ) natStr₀ g₁ ≡ natStr i Δ

record CCatwithzero (ccat : CCat) (ccatnat : CCatwithNat ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithNat ccatnat

  field
    zeroStr  : (Γ : Ob n) → MorC n (suc n)
    zeroStrₛ : {Γ : Ob n} → is-section (zeroStr Γ)
    zeroStr₁ : {Γ : Ob n} → ∂₁ (zeroStr Γ) ≡ NatStr Γ

  zeroStr₀ : {Γ : Ob n} → ∂₀ (zeroStr Γ) ≡ Γ
  zeroStr₀ {_} = is-section₀ zeroStrₛ zeroStr₁ ∙ NatStr=

  field
    zeroStrNat : {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} (g₁ : ∂₁ g ≡ Γ)
             → starTm g (zeroStr Γ) zeroStr₀ g₁ ≡ zeroStr Δ

record CCatwithsuc (ccat : CCat) (ccatnat : CCatwithNat ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithNat ccatnat

  field
    sucStr  : (Γ : Ob n) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ NatStr Γ) → MorC n (suc n)
    sucStrₛ : {Γ : Ob n} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr Γ} → is-section (sucStr Γ u uₛ u₁)
    sucStr₁ : {Γ : Ob n} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr Γ} → ∂₁ (sucStr Γ u uₛ u₁) ≡ NatStr Γ

  sucStr₀ : {Γ : Ob n} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr Γ} → ∂₀ (sucStr Γ u uₛ u₁) ≡ Γ
  sucStr₀ {_} = is-section₀ sucStrₛ sucStr₁ ∙ NatStr=
          

  field
    sucStrNat : {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr Γ} (let u₀ = is-section₀ uₛ u₁ ∙ NatStr=) (g₁ : ∂₁ g ≡ Γ)
             → starTm g (sucStr Γ u uₛ u₁) sucStr₀ g₁ ≡ sucStr Δ (starTm g u u₀ g₁) ssₛ (starTm₁ g NatStr= u uₛ u₁ g₁ ∙ NatStrNat g g₀ g₁)


  ap-irr-sucStr : {Γ Γ' : Ob n} (rΓ : Γ ≡ Γ') {u u' : MorC n (suc n)} (ru : u ≡ u') {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr Γ} {uₛ' : is-section u'} {u₁' : ∂₁ u' ≡ NatStr Γ'}
                → sucStr Γ u uₛ u₁ ≡ sucStr Γ' u' uₛ' u₁'
  ap-irr-sucStr refl refl = refl

record CCatwithnatelim (ccat : CCat) (ccatnat : CCatwithNat ccat) (ccatzero : CCatwithzero ccat ccatnat) (ccatsuc : CCatwithsuc ccat ccatnat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithNat ccatnat
  open CCatwithzero ccatzero
  open CCatwithsuc ccatsuc

  T-dS₁ : (Γ : Ob n) (P : Ob (suc (suc n))) (P= : ft P ≡ NatStr Γ) (dS : MorC (suc (suc n)) (suc (suc (suc n)))) → Ob (suc (suc (suc n)))
  T-dS₁ Γ P P= dS = star' (pp P)
                          (star' (sucStr (NatStr Γ) (varC last (NatStr Γ)) (varCₛ last _) (varCL₁ ∙ NatStrNat _ pp₀ _))
                                 (star' (qq' (pp (NatStr Γ)) (NatStr Γ) NatStr= (pp₁ ∙ NatStr=))
                                        P
                                        P= qq₁)
                                 (ft-star ∙ qq₀ ∙ NatStrNat _ pp₀ _) sucStr₁)
                          (ft-star ∙ sucStr₀) (pp₁ ∙ P=)

  field
    natelimStr  : (Γ : Ob n) (P : Ob (suc (suc n))) (P= : ft P ≡ NatStr Γ)
                  (dO : MorC n (suc n)) (dOₛ : is-section dO) (dO₁ : ∂₁ dO ≡ star (zeroStr Γ) P P= zeroStr₁)
                  (dS : MorC (suc (suc n)) (suc (suc (suc n)))) (dSₛ : is-section dS) (dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P= dS)
                  (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ NatStr Γ)
                  → MorC n (suc n)
    natelimStrₛ : ∀ {Γ P P= dO dOₛ dO₁ dS dSₛ} {dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P= dS} → ∀ {u uₛ u₁}
                → is-section (natelimStr {n = n} Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)
    natelimStr₁ : ∀ {Γ P P= dO dOₛ dO₁ dS dSₛ} {dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P= dS} → ∀ {u uₛ u₁}
                → ∂₁ (natelimStr {n = n} Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) ≡ star u P P= u₁

  natelimStr₀ : ∀ {Γ P P= dO dOₛ dO₁ dS dSₛ} {dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P= dS} → ∀ {u uₛ u₁}
                → ∂₀ (natelimStr {n = n} Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) ≡ Γ
  natelimStr₀ {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {uₛ} {u₁} = is-section₀ natelimStrₛ natelimStr₁ ∙ ft-star ∙ is-section₀ uₛ u₁ ∙ NatStr=

  field
    natelimStrNat : {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) → ∀ {Γ P P= dO dS u} {dOₛ : is-section dO} {dO₁ : ∂₁ dO ≡ star (zeroStr Γ) P P= zeroStr₁} {dSₛ : is-section dS} {dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P= dS} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr Γ} (g₁ : ∂₁ g ≡ Γ)
                    (let dO₀ = is-section₀ dOₛ dO₁ ∙ ft-star ∙ zeroStr₀)
                    (let dS₀ = is-section₀ dSₛ dS₁ ∙ ft-star ∙ pp₀)
                    (let u₀ = is-section₀ uₛ u₁ ∙ NatStr=)
                    (let nat = NatStrNat _ g₀ _)
                  → starTm g (natelimStr {n = m} Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) natelimStr₀ g₁
                  ≡ natelimStr Δ (star+ g P P= NatStr= g₁) (ft-star ∙ qq₀ ∙ nat)
                                 (starTm g dO dO₀ g₁) ssₛ (starTm₁ g (ft-star ∙ zeroStr₀) dO dOₛ dO₁ g₁ ∙ starstar g P P= NatStr= g₁ (zeroStr Γ) zeroStrₛ zeroStr₁ ∙ ap-irr-star (zeroStrNat _ g₀ g₁) refl)
                                 (starTm++ g P= NatStr= dS dS₀  g₁) ssₛ (starTm++₁ g (ft-star ∙ pp₀) P= NatStr= dS dSₛ dS₁ g₁ ∙
                                           star-pp P= (ft-star ∙ sucStr₀) qq₁ ∙ ap-irr-star refl
                                                                                            (starstar (qq g (NatStr Γ) NatStr= g₁)
                                                                                                      (star (qq (pp (NatStr Γ)) (NatStr Γ) NatStr= (pp₁ ∙ NatStr=)) P P= qq₁)
                                                                                                      (ft-star ∙ qq₀ ∙ NatStrNat (pp (NatStr Γ)) pp₀ (pp₁ ∙ NatStr=))
                                                                                                      NatStr= qq₁
                                                                                                      (sucStr (NatStr Γ) (varC last (NatStr Γ))
                                                                                                                         (varCₛ last (NatStr Γ))
                                                                                                                         (varCL₁ ∙ NatStrNat (pp (NatStr Γ)) pp₀ (pp₁ ∙ NatStr=)))
                                                                                                      sucStrₛ sucStr₁ ∙
                                                                                                      ap-irr-star (sucStrNat (qq g (NatStr Γ) NatStr= g₁) qq₀ qq₁ ∙
                                                                                                                              ap-irr-sucStr nat (star-varCL ∙ ap (varC last) (NatStrNat g g₀ g₁)))
                                                                                                                  (ap-irr-star (ap-irr-qq refl (! (NatStrNat (pp (NatStr Γ)) pp₀ (pp₁ ∙ NatStr=)))) refl ∙
                                                                                                                  star-qqpp P= NatStr= g₁  ∙ ap-irr-star (ap-irr-qq (ap pp nat) nat) refl)))
                                 (starTm g u u₀ g₁) ssₛ (starTm₁ g NatStr= u uₛ u₁ g₁ ∙ nat)

record CCatwithid (ccat : CCat) (ccatuu : CCatwithUU ccat) (ccatel : CCatwithEl ccat ccatuu) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu
  open CCatwithEl ccatel

  field
    idStr  : (i : ℕ) (Γ : Ob n) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i Γ) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ ElStr i Γ a aₛ a₁)
                     (v : MorC n (suc n)) (vₛ : is-section v) (v₁ : ∂₁ v ≡ ElStr i Γ a aₛ a₁) → MorC n (suc n)
    idStrₛ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i Γ a aₛ a₁}
                     {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i Γ a aₛ a₁} → is-section (idStr i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁)
    idStr₁ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i Γ a aₛ a₁}
                     {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i Γ a aₛ a₁} → ∂₁ (idStr i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ UUStr i Γ

  idStr₀ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i Γ a aₛ a₁}
                   {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i Γ a aₛ a₁} → ∂₀ (idStr i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ Γ
  idStr₀ {_} = is-section₀ idStrₛ idStr₁ ∙ UUStr=

  field
    idStrNat : {i : ℕ} {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i Γ a aₛ a₁}
                                                {v : MorC m (suc m)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i Γ a aₛ a₁} (g₁ : ∂₁ g ≡ Γ)
                                                (let a₀ = is-section₀ aₛ a₁ ∙ UUStr=) (let u₀ = is-section₀ uₛ u₁ ∙ ElStr=) (let v₀ = is-section₀ vₛ v₁ ∙ ElStr= )
             → starTm g (idStr i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) idStr₀ g₁ ≡ idStr i Δ (starTm g a a₀ g₁) ssₛ (starTm₁ g UUStr= a aₛ a₁ g₁ ∙ UUStrNat g g₀ g₁)
                                                                                  (starTm g u u₀ g₁) ssₛ (starTm₁ g ElStr= u uₛ u₁ g₁ ∙ ElStrNat g g₀ g₁)
                                                                                  (starTm g v v₀ g₁) ssₛ (starTm₁ g ElStr= v vₛ v₁ g₁ ∙ ElStrNat g g₀ g₁)

record CCatwithrefl (ccat : CCat) (ccatid : CCatwithId ccat) : Set₁ where
  open CCat ccat renaming (Mor to MorC)
  open CCatwithId ccatid

  field
    reflStr  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) → MorC n (suc n)
    reflStrₛ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → is-section (reflStr Γ A A= a aₛ a₁)
    reflStr₁ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → ∂₁ (reflStr Γ A A= a aₛ a₁) ≡ IdStr Γ A A= a aₛ a₁ a aₛ a₁

  reflStr₀ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ A} → ∂₀ (reflStr Γ A A= u uₛ u₁) ≡ Γ
  reflStr₀ {_} = is-section₀ reflStrₛ reflStr₁ ∙ IdStr=

  field
    reflStrNat : {n m : ℕ} (g : MorC n m) {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ A} (g₁ : ∂₁ g ≡ Γ)
                 (let u₀ = is-section₀ uₛ u₁ ∙ A=)
             → starTm g (reflStr Γ A A= u uₛ u₁) reflStr₀ g₁ ≡ reflStr Δ (star g A A= g₁) (ft-star ∙ g₀) (starTm g u u₀ g₁) ssₛ (starTm₁ g A= u uₛ u₁ g₁)



-- record CCatwithjj (ccat : CCat) (ccatid : CCatwithId ccat) (ccatrefl : CCatwithrefl ccat ccatid) : Set₁ where
--   open CCat ccat renaming (Mor to MorC)
--   open CCatwithId ccatid
--   open CCatwithrefl ccatrefl

--   T-d₁ : (A : Ob (suc n)) (P : Ob (suc (suc (suc (suc n)))))
--          (P= : ft P ≡ IdStr (star (pp (star (pp A) A pp₁)) (star (pp A) A pp₁) pp₁) (ss (pp (star (pp A) A pp₁))) ssₛ (ss₁' (pp₁ ∙ ft-star ∙ pp₀) ∙ star-comp pp₁) (ss (id (star (pp A) A pp₁))) ssₛ (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl)) (d : MorC (suc n) (suc (suc n))) → Ob (suc (suc n))
--   T-d₁ A P P= d =
--     star (reflStr (star (pp A) A pp₁)
--                   (ss (id A))
--                   ssₛ
--                   (ss₁ ∙ ap2-irr star (id-left' (pp₀ ∙ id₁) ∙ ap pp id₁) id₁))
--          (star (qq (ss (id A))
--                    (IdStr
--                      (star
--                        (pp (star (pp A) A pp₁))
--                        (star (pp A) A pp₁)
--                        pp₁)
--                      (ss (pp (star (pp A) A pp₁)))
--                       ssₛ
--                      (ss₁' (pp₁ ∙ ft-star ∙ pp₀) ∙ star-comp pp₁)
--                      (ss (id (star (pp A) A pp₁)))
--                       ssₛ
--                      (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl))
--                    (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl ∙ ! (IdStr= ∙ ft-star ∙ pp₀)))
--                P
--                (qq₁ ∙ ! P=))
--          (reflStr₁
--           ∙ ! (ft-star ∙ qq₀ ∙ (IdStrNat _ (ft-star ∙ pp₀ ∙ ! (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl)))
--               ∙ ap-irr-IdStr (star-pp' ssₛ)
--                              (star-varCL'' {p = varCL₁ ∙ ! pp₀} ∙ ap ss (ap2-irr comp (ap pp (! varCL₁)) refl ∙ ssₛ ∙ ap id (ss₀ ∙ id₀)))
--                              (star-varCL'' {p = varCL₁ ∙ ! id₀} ∙ ap ss (id-right' varCL₁) ∙ ss-of-section (ss (id A)) ssₛ)))

--   field
--     jjStr  : (A : Ob (suc n)) (P : Ob (suc (suc (suc (suc n)))))
--              (P= : ft P ≡ IdStr (star (pp (star (pp A) A pp₁)) (star (pp A) A pp₁) pp₁) (ss (pp (star (pp A) A pp₁))) ssₛ (ss₁' (pp₁ ∙ ft-star ∙ pp₀) ∙ star-comp pp₁) (ss (id (star (pp A) A pp₁))) ssₛ (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl))
--              (d : MorC (suc n) (suc (suc n))) (dₛ : is-section d)
--              (d₁ : ∂₁ d ≡ T-d₁ A P P= d)
--              (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A)
--              (b : MorC n (suc n)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ A)
--              (p : MorC n (suc n)) (pₛ : is-section p) (p₁ : ∂₁ p ≡ IdStr A a aₛ a₁ b bₛ b₁)
--              → MorC n (suc n)
--     jjStrₛ : ∀ {A P P= d a b p} {dₛ : is-section d} {d₁ : ∂₁ d ≡ T-d₁ A P P= d} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} {pₛ : is-section p} {p₁ : ∂₁ p ≡ IdStr A a aₛ a₁ b bₛ b₁}
--            → is-section (jjStr {n = n} A P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁)
--     jjStr₁ : ∀ {A P P= d a b p} {dₛ : is-section d} {d₁ : ∂₁ d ≡ T-d₁ A P P= d} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} {pₛ : is-section p} {p₁ : ∂₁ p ≡ IdStr A a aₛ a₁ b bₛ b₁}
--              (let wA = star (pp A) A pp₁) (let idthing = IdStr (star (pp (star (pp A) A pp₁)) (star (pp A) A pp₁) pp₁) (ss (pp (star (pp A) A pp₁))) ssₛ (ss₁' (pp₁ ∙ ft-star ∙ pp₀) ∙ star-comp pp₁) (ss (id (star (pp A) A pp₁))) ssₛ (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl))
--            → ∂₁ (jjStr {n = n} A P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁)
--              ≡ {!star' p
--                     (star' (qq b
--                               (star' (qq a
--                                         wA
--                                         (a₁ ∙ ! pp₀ ∙ ! ft-star))
--                                     idthing
--                                     (qq₁ ∙ ! pp₀ ∙ ! ft-star ∙ ! IdStr=))
--                               (b₁ ∙ {!TODO!} ∙ ! qq₀ ∙ ! ft-star))
--                           (star' (qq (qq a
--                                         wA
--                                         (a₁ ∙ ! pp₀ ∙ ! ft-star))
--                                     idthing
--                                     (qq₁ ∙ ! pp₀ ∙ ! ft-star ∙ ! IdStr=))
--                                 P
--                                 (qq₁ ∙ ! P=))
--                           (qq₁ ∙ ! qq₀ ∙ ! ft-star))
--                     (p₁ ∙ {!TODO!} ∙ ! qq₀ ∙ ! ft-star)!}

--   jjStr₀ : ∀ {A P P= d a b p} {dₛ : is-section d} {d₁ : ∂₁ d ≡ T-d₁ A P P= d} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} (pₛ : is-section p) (p₁ : ∂₁ p ≡ IdStr A a aₛ a₁ b bₛ b₁)
--          → ∂₀ (jjStr {n = n} A P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁) ≡ ft A
--   jjStr₀ pₛ p₁ = is-section₀ jjStrₛ jjStr₁ ∙ {!ft-star ∙ is-section₀ pₛ p₁ ∙ IdStr=!}



-- record StructuredCCat : Set₁ where
--   field
--     ccat : CCat
--     ccatUU : CCatwithUU ccat
--     ccatEl : CCatwithEl ccat ccatUU
--     ccatPi : CCatwithPi ccat
--     ccatSig : CCatwithSig ccat
--     ccatNat : CCatwithNat ccat
--     ccatId : CCatwithId ccat
--     ccatuu : CCatwithuu ccat ccatUU
--     ccatpi : CCatwithpi ccat ccatUU ccatEl
--     ccatlam : CCatwithlam ccat ccatPi
--     ccatapp : CCatwithapp ccat ccatPi
--     ccatsig : CCatwithsig ccat ccatUU ccatEl
--     ccatpair : CCatwithpair ccat ccatSig
--     ccatpr1 : CCatwithpr1 ccat ccatSig
--     ccatpr2 : CCatwithpr2 ccat ccatSig ccatpr1
--     ccatnat : CCatwithnat ccat ccatUU
--     ccatzero : CCatwithzero ccat ccatNat
--     ccatsuc : CCatwithsuc ccat ccatNat
--     ccatnatelim : CCatwithnatelim ccat ccatNat ccatzero ccatsuc
--     ccatid : CCatwithid ccat ccatUU ccatEl
--     ccatrefl : CCatwithrefl ccat ccatId
--     ccatjj : CCatwithjj ccat ccatId ccatrefl

--   open CCat ccat renaming (Mor to MorC)
--   open CCatwithUU ccatUU public
--   open CCatwithEl ccatEl public
--   open CCatwithPi ccatPi public
--   open CCatwithSig ccatSig public
--   open CCatwithNat ccatNat public
--   open CCatwithId ccatId public
--   open CCatwithuu ccatuu public
--   open CCatwithpi ccatpi public
--   open CCatwithlam ccatlam public
--   open CCatwithapp ccatapp public
--   open CCatwithsig ccatsig public
--   open CCatwithpair ccatpair public
--   open CCatwithpr1 ccatpr1 public
--   open CCatwithpr2 ccatpr2 public
--   open CCatwithnat ccatnat public
--   open CCatwithzero ccatzero public
--   open CCatwithsuc ccatsuc public
--   open CCatwithnatelim ccatnatelim public
--   open CCatwithid ccatid public
--   open CCatwithrefl ccatrefl public
--   open CCatwithjj ccatjj public

--   field
--     {- Additional structure corresponding to equality rules -}
--     betaPiStr : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A}
--             → appStr A B B= (lamStr A B B= u uₛ u₁) lamStrₛ lamStr₁ a aₛ a₁ ≡ starTm a u (is-section₀ uₛ refl ∙ ap ft u₁ ∙ B= ∙ ! a₁)
--     betaSig1Str : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B (a₁ ∙ ! B=)} → pr1Str A B B= (pairStr A B B= a aₛ a₁ b bₛ b₁) pairStrₛ pairStr₁ ≡ a
--     betaSig2Str : {A : Ob (suc n)} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B (a₁ ∙ ! B=)} → pr2Str A B B= (pairStr A B B= a aₛ a₁ b bₛ b₁) pairStrₛ pairStr₁ ≡ b

--     eluuStr : {i : ℕ} {X : Ob n} → ElStr (suc i) (uuStr i X) uuStrₛ (uuStr₁ ∙ ap (UUStr (suc i)) (! (uuStr₀ _))) ≡ UUStr i X
--     elpiStr : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)}
--             → ElStr i (piStr i a aₛ a₁ b bₛ b₁) piStrₛ (piStr₁ ∙ ap (UUStr i) (! (piStr₀ _))) ≡ PiStr (ElStr i a aₛ a₁) (ElStr i b bₛ (b₁ ∙ ap (UUStr i) (! (is-section₀ bₛ b₁ ∙ UUStr=)))) (ElStr= ∙ is-section₀ bₛ b₁ ∙ UUStr=)
--     elsigStr : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i a aₛ a₁)}
--             → ElStr i (sigStr i a aₛ a₁ b bₛ b₁) sigStrₛ (sigStr₁ ∙ ap (UUStr i) (! (sigStr₀ _))) ≡ SigStr (ElStr i a aₛ a₁) (ElStr i b bₛ (b₁ ∙ ap (UUStr i) (! (is-section₀ bₛ b₁ ∙ UUStr=)))) (ElStr= ∙ is-section₀ bₛ b₁ ∙ UUStr=)
--     elnatStr : {i : ℕ} {X : Ob n} → ElStr i (natStr i X) natStrₛ (natStr₁ ∙ ap (UUStr i) (! (natStr₀ _))) ≡ NatStr X
--     elidStr : {i : ℕ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i (∂₀ a)} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i a aₛ a₁}
--                       {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i a aₛ a₁} → ElStr i (idStr i a aₛ a₁ u uₛ u₁ v vₛ v₁) idStrₛ (idStr₁ ∙ ap (UUStr i) (! (idStr₀ _))) ≡ IdStr (ElStr i a aₛ a₁) u uₛ u₁ v vₛ v₁


-- {- Morphisms of contextual categories -}

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


-- {- Morphisms of structured contextual categories -}

-- record StructuredCCatMor (sC sD : StructuredCCat) : Set where
--   private
--     open StructuredCCat
--     C = ccat sC
--     D = ccat sD

--   field
--     ccat→ : CCatMor C D
    
--   open CCatMor ccat→
--   open CCat
  

--   Mor→ₛ : {n : ℕ} {u : Mor C n (suc n)} (uₛ : is-section C u) → is-section D (Mor→ u)
--   Mor→ₛ uₛ = ! (comp→ ∙ ap2-irr (comp D) (pp→ ∙ ap (pp D) ∂₁→) refl) ∙ ap Mor→ uₛ ∙ id→ ∙ ap (id D) ∂₀→

--   Mor→₁ : {n : ℕ} {u : Mor C n (suc n)} {X : Ob C (suc n)} (u₁ : ∂₁ C u ≡ X) → ∂₁ D (Mor→ u) ≡ Ob→ X
--   Mor→₁ u₁ = ! ∂₁→ ∙ ap Ob→ u₁

--   field
--     UUStr→ : {n : ℕ} (i : ℕ) (X : Ob C n) → Ob→ (UUStr sC i X) ≡ UUStr sD i (Ob→ X)
--     ElStr→ : (i : ℕ) (v : Mor C n (suc n)) (vₛ : is-section C v) (v₁ : ∂₁ C v ≡ UUStr sC i (∂₀ C v))
--            → Ob→ (ElStr sC i v vₛ v₁) ≡ ElStr sD i (Mor→ v) (Mor→ₛ vₛ) (Mor→₁ v₁ ∙ UUStr→ _ _ ∙ ap (UUStr sD i) ∂₀→)
--     PiStr→  : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) → Ob→ (PiStr sC A B B=) ≡ PiStr sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=)
--     SigStr→ : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) → Ob→ (SigStr sC A B B=) ≡ SigStr sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=)
--     NatStr→ : (X : Ob C n) → Ob→ (NatStr sC X) ≡ NatStr sD (Ob→ X)
--     IdStr→  : (A : Ob C (suc n)) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ A) (b : Mor C n (suc n)) (bₛ : is-section C b) (b₁ : ∂₁ C b ≡ A)
--             → Ob→ (IdStr sC A a aₛ a₁ b bₛ b₁) ≡ IdStr sD (Ob→ A) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁)


--     uuStr→ : (i : ℕ) (X : Ob C n)
--             → Mor→ (uuStr sC i X) ≡ uuStr sD i (Ob→ X)
--     piStr→ : (i : ℕ) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ UUStr sC i (∂₀ C a)) (b : Mor C (suc n) (suc (suc n))) (bₛ : is-section C b) (b₁ : ∂₁ C b ≡ UUStr sC i (ElStr sC i a aₛ a₁))
--             → Mor→ (piStr sC i a aₛ a₁ b bₛ b₁) ≡ piStr sD i (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ UUStr→ _ _ ∙ ap (UUStr sD i) ∂₀→) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁ ∙ UUStr→ _ _ ∙ ap (UUStr sD i) (ElStr→ _ _ _ _))
--     lamStr→ : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (u : Mor C (suc n) (suc (suc n))) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ B)
--             → Mor→ (lamStr sC A B B= u uₛ u₁) ≡ lamStr sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁)
--     appStr→ : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (f : Mor C n (suc n)) (fₛ : is-section C f) (f₁ : ∂₁ C f ≡ PiStr sC A B B=) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ A)
--             → Mor→ (appStr sC A B B= f fₛ f₁ a aₛ a₁) ≡ appStr sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ f) (Mor→ₛ fₛ) (Mor→₁ f₁ ∙ PiStr→ _ _ _) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁)
--     sigStr→ : (i : ℕ) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ UUStr sC i (∂₀ C a)) (b : Mor C (suc n) (suc (suc n))) (bₛ : is-section C b) (b₁ : ∂₁ C b ≡ UUStr sC i (ElStr sC i a aₛ a₁))
--             → Mor→ (sigStr sC i a aₛ a₁ b bₛ b₁) ≡ sigStr sD i (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ UUStr→ _ _ ∙ ap (UUStr sD i) ∂₀→) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁ ∙ UUStr→ _ _ ∙ ap (UUStr sD i) (ElStr→ _ _ _ _))
--     pairStr→ : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ A) (b : Mor C n (suc n)) (bₛ : is-section C b) (b₁ : ∂₁ C b ≡ star C a B (a₁ ∙ ! B=))
--             → Mor→ (pairStr sC A B B= a aₛ a₁ b bₛ b₁) ≡ pairStr sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁ ∙ star→)
--     pr1Str→ : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (u : Mor C n (suc n)) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ SigStr sC A B B=)
--             → Mor→ (pr1Str sC A B B= u uₛ u₁) ≡ pr1Str sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ SigStr→ _ _ _)
--     pr2Str→ : (A : Ob C (suc n)) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (u : Mor C n (suc n)) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ SigStr sC A B B=)
--             → Mor→ (pr2Str sC A B B= u uₛ u₁) ≡ pr2Str sD (Ob→ A) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ SigStr→ _ _ _)
--     natStr→ : (i : ℕ) (X : Ob C n)
--             → Mor→ (natStr sC i X) ≡ natStr sD i (Ob→ X)
--     zeroStr→ : (X : Ob C n)
--             → Mor→ (zeroStr sC X) ≡ zeroStr sD (Ob→ X)
--     sucStr→ : (u : Mor C n (suc n)) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ NatStr sC (∂₀ C u))
--             → Mor→ (sucStr sC u uₛ u₁) ≡ sucStr sD (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ NatStr→ _ ∙ ap (NatStr sD) ∂₀→)
--     idStr→ : (i : ℕ) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ UUStr sC i (∂₀ C a)) (u : Mor C n (suc n)) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ ElStr sC i a aₛ a₁)
--                      (v : Mor C n (suc n)) (vₛ : is-section C v) (v₁ : ∂₁ C v ≡ ElStr sC i a aₛ a₁)
--             → Mor→ (idStr sC i a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ idStr sD i (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ UUStr→ _ _ ∙ ap (UUStr sD i) ∂₀→) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ ElStr→ _ _ _ _) (Mor→ v) (Mor→ₛ vₛ) (Mor→₁ v₁ ∙ ElStr→ _ _ _ _)
--     reflStr→ : (A : Ob C (suc n)) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ A)
--             → Mor→ (reflStr sC A a aₛ a₁) ≡ reflStr sD (Ob→ A) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁)


-- module _ {sC sD : StructuredCCat} where
--   open StructuredCCatMor
--   open StructuredCCat
--   open CCatMor
--   open CCat

--   {- Equalities between morphisms between structured contextual categories -}

--   structuredCCatMorEq : {f g : StructuredCCatMor sC sD}
--                       → ({n : ℕ} (X : Ob (ccat sC) n) → Ob→ (ccat→ f) X ≡ Ob→ (ccat→ g) X)
--                       → ({n m : ℕ} (X : Mor (ccat sC) n m) → Mor→ (ccat→ f) X ≡ Mor→ (ccat→ g) X)
--                       → f ≡ g
--   structuredCCatMorEq h k = lemma (funextI (λ n → funext h)) (funextI (λ n → funextI (λ m → funext k)))  where

--     lemma : {f g : StructuredCCatMor sC sD}
--             → ((λ {n} → Ob→ (ccat→ f) {n}) ≡ (λ {n} → Ob→ (ccat→ g) {n}))
--             → ((λ {n m} → Mor→ (ccat→ f) {n} {m}) ≡ (λ {n m} → Mor→ (ccat→ g) {n} {m}))
--             → f ≡ g
--     lemma refl refl = refl
