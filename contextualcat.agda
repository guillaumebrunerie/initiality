{-# OPTIONS --rewriting --prop --without-K --no-auto-inline --no-fast-reduce #-}

open import common


{- Definition of contextual categories as algebras of an essentially algebraic theory -}

record CCat : Set₁ where
  no-eta-equality
  field
    -- objects
    Ob : ℕ → Set
    -- morphisms
    Mor : ℕ → ℕ → Set
    -- domain and codomain(prev (prev (prev k)))
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
    ss₁ : {f : Mor m (suc n)} {X : Ob (suc n)} (f₁ : ∂₁ f ≡ X) → ∂₁ (ss f) ≡ star (comp (pp X) f pp₀ f₁) X refl (comp₁ ∙ pp₁)
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
    qq-id : {X : Ob (suc n)} {Y : Ob n} {p : ft X ≡ Y} → qq (id Y) X p id₁ ≡ id X
    star-comp : {m n k : ℕ} {g : Mor m k} {f : Mor n m} {Y : Ob m} {f₁ : ∂₁ f ≡ Y} {g₀ : ∂₀ g ≡ Y} {X : Ob (suc k)} {Z : Ob k} {p : ft X ≡ Z} {g₁ : ∂₁ g ≡ Z} → star (comp g f g₀ f₁) X p (comp₁ ∙ g₁) ≡ star f (star g X p g₁) (ft-star ∙ g₀) f₁
    qq-comp : {m n k : ℕ} {g : Mor m k} {f : Mor n m} {Y : Ob m} {f₁ : ∂₁ f ≡ Y} {g₀ : ∂₀ g ≡ Y} {X : Ob (suc k)} {Z : Ob k} {p : ft X ≡ Z} {g₁ : ∂₁ g ≡ Z} → qq (comp g f g₀ f₁) X p (comp₁ ∙ g₁) ≡ comp (qq g X p g₁) (qq f (star g X p g₁) (ft-star ∙ g₀) f₁) qq₀ qq₁
    -- properties of s
    ss-pp : {m n : ℕ} {f : Mor m (suc n)} {X : Ob m} (f₀ : ∂₀ f ≡ X) {Y : Ob (suc n)} {f₁ : ∂₁ f ≡ Y} → comp (pp (star (comp (pp Y) f pp₀ f₁) Y refl (comp₁ ∙ pp₁))) (ss f) pp₀ (ss₁ f₁) ≡ id X
    ss-qq : {m n : ℕ} {f : Mor m (suc n)} {X : Ob (suc n)} {f₁ : ∂₁ f ≡ X} → f ≡ comp (qq (comp (pp X) f pp₀ f₁) X refl (comp₁ ∙ pp₁)) (ss f) qq₀ (ss₁ f₁)
    ss-comp : {m n k : ℕ} {U : Ob (suc k)} {X : Ob k} {p : ft U ≡ X} {g : Mor n k} {g₁ : ∂₁ g ≡ X} {f : Mor m (suc n)} {f₁ : ∂₁ f ≡ star g U p g₁} → ss f ≡ ss (comp (qq g U p g₁) f qq₀ f₁)

module CCat+ (C : CCat) where
  open CCat C public
  abstract
    ap-irr-comp : {g g' : Mor m k} (g= : g ≡ g') {f f' : Mor n m} (f= : f ≡ f') {X X' : Ob m} {g₀ : ∂₀ g ≡ X} {g₀' : ∂₀ g' ≡ X'} {f₁ : ∂₁ f ≡ X} {f₁' : ∂₁ f' ≡ X'} → comp g f g₀ f₁ ≡ comp g' f' g₀' f₁'
    ap-irr-comp refl refl {g₀ = g₀} {g₀'} = ap-irr2 (λ X y z → comp _ _ {X = X} y z) (! g₀ ∙ g₀')
  
    ap-irr-qq : {f f' : Mor m n} (f= : f ≡ f') {X X' : Ob (suc n)} (X= : X ≡ X') {Y Y' : Ob n} {q : ft X ≡ Y} {q' : ft X' ≡ Y'} {f₁ : ∂₁ f ≡ Y} {f₁' : ∂₁ f' ≡ Y'} → qq f X q f₁ ≡ qq f' X' q' f₁'
    ap-irr-qq refl refl {q = q} {q'} = ap-irr2 (λ Y y z → qq _ _ {Y = Y} y z) (! q ∙ q')

    ap-irr-star : {f f' : Mor m n} (f= : f ≡ f') {X X' : Ob (suc n)} (X= : X ≡ X') {Y Y' : Ob n} {q : ft X ≡ Y} {q' : ft X' ≡ Y'} {f₁ : ∂₁ f ≡ Y} {f₁' : ∂₁ f' ≡ Y'} → star f X q f₁ ≡ star f' X' q' f₁'
    ap-irr-star refl refl {q = q} {q'} = ap-irr2 (λ Y y z → star _ _ {Y = Y} y z) (! q ∙ q')

  {- Sections of [pp] -}


  abstract
    is-section : (u : Mor n (suc n)) → Prop
    is-section u = comp (pp (∂₁ u)) u pp₀ refl ≡ id (∂₀ u)
  
    is-section₀ : {u : Mor n (suc n)} {X : Ob (suc n)} (uₛ : is-section u) (u₁ : ∂₁ u ≡ X) → ∂₀ u ≡ ft X
    is-section₀ uₛ u₁ = ! id₁ ∙ ap ∂₁ (! uₛ) ∙ comp₁ ∙ pp₁ ∙ ap ft u₁

    ssₛ : {f : Mor m (suc n)} → is-section (ss f)
    ssₛ = ap-irr-comp (ap pp (ss₁ refl)) refl ∙ ss-pp refl ∙ ap id (! ss₀)  
 
    is-section= : {X : Ob (suc n)} {Y : Ob n} (X= : ft X ≡ Y) {u : Mor n (suc n)} (uₛ : is-section u) (u₁ : ∂₁ u ≡ X) → comp (pp X) u pp₀ u₁ ≡ id Y
    is-section= refl uₛ refl = uₛ ∙ ap id (is-section₀ uₛ refl)

    is-section→ : {u : Mor n (suc n)} (p : comp (pp (∂₁ u)) u pp₀ refl ≡ id (∂₀ u)) → is-section u
    is-section→ p = p

    ss-of-section : (u : Mor n (suc n)) (uₛ : is-section u) → ss u ≡ u
    ss-of-section u uₛ = ! (ss-qq ∙ (ap-irr-comp (ap-irr-qq (uₛ ∙ ap id (is-section₀ uₛ refl)) refl {q' = refl} ∙ qq-id) refl) ∙ id-right (ss₁ refl ∙ ap-irr-star (uₛ ∙ ap id (is-section₀ uₛ refl)) refl {q' = refl} ∙ star-id))

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
  star^ {n = suc n} (prev k) X+ X p q = star (qq^ k p q) X refl qq^₁

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

  abstract
    qq^=p : {k : Fin (suc n)} {X : Ob n} {X+ : Ob (suc (n -F' k))} {Y : Ob (n -F' k)} {p : ft X+ ≡ Y} {q : ft^ k X ≡ Y} {X' : Ob n} {q' : ft^ k X' ≡ Y} (X= : X ≡ X') → qq^ k p q ≡ qq^ k p q'
    qq^=p refl = refl

    star^=p : {k : Fin (suc n)} {X : Ob n} {X+ : Ob (suc (n -F' k))} {Y : Ob (n -F' k)} {p : ft X+ ≡ Y} {q : ft^ k X ≡ Y} {X' : Ob n} {q' : ft^ k X' ≡ Y} (X= : X ≡ X') → star^ k X+ X p q ≡ star^ k X+ X' p q'
    star^=p refl = refl

  {- Other helper functions -}

  star+ : (g : Mor n m) (X : Ob (suc (suc m))) {X' : Ob (suc m)} (X= : ft X ≡ X') {X'' : Ob m} (X'= : ft X' ≡ X'') (g₁ : ∂₁ g ≡ X'') → Ob (suc (suc n))
  star+ g X {X'} X= X'= g₁ = star (qq g X' X'= g₁) X X= qq₁

  star++ : (g : Mor n m) (X : Ob (suc (suc (suc m)))) {X' : Ob (suc (suc m))} (X= : ft X ≡ X') {X'' : Ob (suc m)} (X'= : ft X' ≡ X'') {X''' : Ob m} (X''= : ft X'' ≡ X''') (g₁ : ∂₁ g ≡ X''') → Ob (suc (suc (suc n)))
  star++ g X {X'} X= {X''} X'= {X'''} X''= g₁ = star+ (qq g X'' X''= g₁) X X= X'= qq₁
  
  star+++ : (g : Mor n m) (X : Ob (suc (suc (suc (suc m))))) {X' : Ob (suc (suc (suc m)))} (X= : ft X ≡ X') {X'' : Ob (suc (suc m))} (X'= : ft X' ≡ X'') {X''' : Ob (suc m)} (X''= : ft X'' ≡ X''') {X'''' : Ob m} (X'''= : ft X''' ≡ X'''') (g₁ : ∂₁ g ≡ X'''') → Ob (suc (suc (suc (suc n))))
  star+++ g X {X'} X= {X''} X'= {X'''} X''= {X''''} X'''= g₁ = star++ (qq g X''' X'''= g₁) X X= X'= X''= qq₁

  star++++ : (g : Mor n m) (X : Ob (suc (suc (suc (suc (suc m)))))) {X' : Ob (suc (suc (suc (suc m))))} (X= : ft X ≡ X') {X'' : Ob (suc (suc (suc m)))} (X'= : ft X' ≡ X'') {X''' : Ob (suc (suc m))} (X''= : ft X'' ≡ X''') {X'''' : Ob (suc m)} (X'''= : ft X''' ≡ X'''') {X''''' : Ob m} (X''''= : ft X'''' ≡ X''''') (g₁ : ∂₁ g ≡ X''''') → Ob (suc (suc (suc (suc (suc n)))))
  star++++ g X {X'} X= {X''} X'= {X'''} X''= {X''''} X'''= {X'''''} X''''= g₁ = star+++ (qq g X'''' X''''= g₁) X X= X'= X''= X'''= qq₁

  starTm : (g : Mor n m) {X : Ob m} (u : Mor m (suc m)) (u₀ : ∂₀ u ≡ X) (g₁ : ∂₁ g ≡ X) → Mor n (suc n)
  starTm g {X} u u₀ g₁ = ss (comp u g u₀ g₁)

  starTm+ : (g : Mor n m) {X : Ob (suc m)} {X' : Ob m} (X= : ft X ≡ X') (u : Mor (suc m) (suc (suc m))) (u₀ : ∂₀ u ≡ X) (g₁ : ∂₁ g ≡ X') → Mor (suc n) (suc (suc n))
  starTm+ g {X} X= u u₀ g₁ = starTm (qq g X X= g₁) u u₀ qq₁

  starTm++ : (g : Mor n m) {X : Ob (suc (suc m))} {X' : Ob (suc m)} (X= : ft X ≡ X') {X'' : Ob m} (X'= : ft X' ≡ X'') (u : Mor (suc (suc m)) (suc (suc (suc m)))) (u₀ : ∂₀ u ≡ X) (g₁ : ∂₁ g ≡ X'') → Mor (suc (suc n)) (suc (suc (suc n)))
  starTm++ g {X} {X'} X= {X''} X'= u u₀ g₁ = starTm+ (qq g X' X'= g₁) X= u u₀ qq₁

  abstract
    ap-irr-starTm : {f f' : Mor m n} (f= : f ≡ f') {u u' : Mor n (suc n)} (u= : u ≡ u') {Y Y' : Ob n} {u₀ : ∂₀ u ≡ Y} {u₀' : ∂₀ u' ≡ Y'} {f₁ : ∂₁ f ≡ Y} {f₁' : ∂₁ f' ≡ Y'} → starTm f u u₀ f₁ ≡ starTm f' u' u₀' f₁'
    ap-irr-starTm f= u= = ap ss (ap-irr-comp u= f=)

    starTm₁ : (g : Mor n m) {X : Ob (suc m)} {X' : Ob m} (X= : ft X ≡ X') (u : Mor m (suc m)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ X) (g₁ : ∂₁ g ≡ X') → ∂₁ (starTm g u (is-section₀ uₛ u₁ ∙ X=) g₁) ≡ star g X X= g₁
    starTm₁ g X= u uₛ u₁ g₁ = ss₁ (comp₁ ∙ u₁) ∙ ap-irr-star (! assoc ∙ ap-irr-comp (is-section= X= uₛ u₁) refl ∙ id-right g₁) refl 

    starTm+₁ : (g : Mor n m) {X : Ob (suc (suc m))} {X' : Ob (suc m)} (X= : ft X ≡ X') {X'' : Ob m} (X'= : ft X' ≡ X'') (u : Mor (suc m) (suc (suc m))) (uₛ : is-section u) (u₁ : ∂₁ u ≡ X) (g₁ : ∂₁ g ≡ X'') → ∂₁ (starTm+ g X'= u (is-section₀ uₛ u₁ ∙ X=) g₁) ≡ star+ g X X= X'= g₁
    starTm+₁ g {X' = X'} X= X'= u uₛ u₁ g₁ = starTm₁ (qq g X' X'= g₁) X= u uₛ u₁ qq₁

    starTm++₁ : (g : Mor n m) {X : Ob (suc (suc (suc m)))} {X' : Ob (suc (suc m))} (X= : ft X ≡ X') {X'' : Ob (suc m)} (X'= : ft X' ≡ X'') {X''' : Ob m} (X''= : ft X'' ≡ X''') (u : Mor (suc (suc m)) (suc (suc (suc m)))) (uₛ : is-section u) (u₁ : ∂₁ u ≡ X) (g₁ : ∂₁ g ≡ X''') → ∂₁ (starTm++ g X'= X''= u (is-section₀ uₛ u₁ ∙ X=) g₁) ≡ star++ g X X= X'= X''= g₁
    starTm++₁ g {X} {X'} X= {X''} X'= {X'''} X''= u uₛ u₁ g₁ = starTm+₁ (qq g X'' X''= g₁) X= X'= u uₛ u₁ qq₁

    star-pp : {n m : ℕ} {g : Mor n m} {A : Ob (suc m)} {B : Ob (suc m)} {X : Ob m} {A= : ft A ≡ X} {B= : ft B ≡ X} {g₁ : ∂₁ g ≡ X} {Y : Ob n} (g₀ : ∂₀ g ≡ Y)
           → star+ g (star (pp A) B B= (pp₁ ∙ A=)) (ft-star ∙ pp₀) A= g₁ ≡ star (pp (star g A A= g₁)) (star g B B= g₁) (ft-star ∙ g₀) (pp₁ ∙ ft-star ∙ g₀)
    star-pp refl = ! star-comp ∙ ap-irr-star pp-qq refl ∙ star-comp 

    star-pp' : {n : ℕ} {g : Mor n (suc n)} {A B : Ob (suc n)} {X : Ob n} (A= : ft A ≡ X) (B= : ft B ≡ X) (gₛ : is-section g) (g₁ : ∂₁ g ≡ A) 
             → star g (star (pp A) B B= (pp₁ ∙ A=)) (ft-star ∙ pp₀) g₁ ≡ B
    star-pp' {g = g} A= B= gₛ g₁ = ! star-comp ∙ ap-irr-star (is-section= A= gₛ g₁) refl {q' = B=} ∙ star-id

    star-qqpp : {n m : ℕ} {g : Mor n m} {B : Ob (suc (suc m))} {A : Ob (suc m)} {B= : ft B ≡ A} {X : Ob m} {A= : ft A ≡ X} {g₁ : ∂₁ g ≡ X} {Y : Ob n} (g₀ : ∂₀ g ≡ Y)
              → star++ g (star+ (pp A) B B= A= (pp₁ ∙ A=)) (ft-star ∙ qq₀) (ft-star ∙ pp₀) A= g₁
                ≡ star+ (pp (star g A A= g₁)) (star+ g B B= A= g₁) (ft-star ∙ qq₀) (ft-star ∙ g₀) (pp₁ ∙ ft-star ∙ g₀) 
    star-qqpp refl = ! star-comp ∙ ap-irr-star (! qq-comp ∙ ap-irr-qq pp-qq refl ∙ qq-comp) refl ∙ star-comp
 
    star-qqpp' : {n : ℕ} {g : Mor n (suc n)} {C : Ob (suc (suc n))} {A B : Ob (suc n)} (C= : ft C ≡ B) {X : Ob n} (A= : ft A ≡ X) (B= : ft B ≡ X) (gₛ : is-section g) (g₁ : ∂₁ g ≡ A) 
             → star+ g (star+ (pp A) C C= B= (pp₁ ∙ A=)) (ft-star ∙ qq₀) (ft-star ∙ pp₀) g₁ ≡ C
    star-qqpp' {g = g} C= A= B= gₛ g₁ = ! star-comp ∙ ap-irr-star (! qq-comp ∙ ap-irr-qq (is-section= A= gₛ g₁) refl {q' = B=} ∙ qq-id) refl {q' = C=} ∙ star-id

    -- star-qqpp' : {n m : ℕ} {g : Mor n m} {B : Ob (suc (suc m))} {A : Ob (suc m)} {B= : ft B ≡ A} {X : Ob m} {A= : ft A ≡ X}
    --            → {g₁ : ∂₁ g ≡ X} {C : Ob _} (C= : star (pp A) A A= (pp₁ ∙ A=) ≡ C)
    --            → star (qq (qq g A A= g₁) C (ap ft (! C=) ∙ ft-star ∙ pp₀) qq₁) (star (qq (pp A) A A= (pp₁ ∙ A=)) B B= qq₁) (ft-star ∙ qq₀ ∙ C=) qq₁
    --              ≡ star (qq (pp (star g A A= g₁)) (star g A A= g₁) ft-star (pp₁ ∙ ft-star)) (star (qq g A A= g₁) B B= qq₁) (ft-star ∙ qq₀) qq₁
    -- star-qqpp' refl = ! star-comp ∙ ap-irr-star (! qq-comp ∙ ap-irr-qq pp-qq refl ∙ qq-comp) refl ∙ star-comp

    star-qqqqpp :{n m : ℕ} {g : Mor n m} {C : Ob (suc (suc (suc m)))} {B : Ob (suc (suc m))} {C= : ft C ≡ B} {A : Ob (suc m)} {B= : ft B ≡ A} {X : Ob m} {A= : ft A ≡ X} {g₁ : ∂₁ g ≡ X} {Y : Ob n} (g₀ : ∂₀ g ≡ Y)
                       → star+++ g (star++ (pp A) C C= B= A= (pp₁ ∙ A=)) (ft-star ∙ qq₀) (ft-star ∙ qq₀) (ft-star ∙ pp₀) A= g₁ ≡ star++ (pp (star g A A= g₁)) (star++ g C C= B= A= g₁) (ft-star ∙ qq₀) (ft-star ∙ qq₀) (ft-star ∙ g₀) (pp₁ ∙ ft-star ∙ g₀)
    star-qqqqpp refl = ! star-comp ∙ ap-irr-star (! qq-comp ∙ ap-irr-qq (! qq-comp ∙ ap-irr-qq pp-qq refl ∙ qq-comp) refl ∙ qq-comp) refl ∙ star-comp 

    star-qqqqqqpp :{n m : ℕ} {g : Mor n m} {D : Ob (suc (suc (suc (suc m))))} {C : Ob (suc (suc (suc m)))} {D= : ft D ≡ C} {B : Ob (suc (suc m))} {C= : ft C ≡ B} {A : Ob (suc m)} {B= : ft B ≡ A} {X : Ob m} {A= : ft A ≡ X} {g₁ : ∂₁ g ≡ X} {Y : Ob n} (g₀ : ∂₀ g ≡ Y)
                       → star++++ g (star+++ (pp A) D D= C= B= A= (pp₁ ∙ A=)) (ft-star ∙ qq₀) (ft-star ∙ qq₀) (ft-star ∙ qq₀) (ft-star ∙ pp₀) A= g₁ ≡ star+++ (pp (star g A A= g₁)) (star+++ g D D= C= B= A= g₁) (ft-star ∙ qq₀) (ft-star ∙ qq₀) (ft-star ∙ qq₀) (ft-star ∙ g₀) (pp₁ ∙ ft-star ∙ g₀)
    star-qqqqqqpp refl = ! star-comp ∙ ap-irr-star (! qq-comp ∙ ap-irr-qq (! qq-comp ∙ ap-irr-qq (! qq-comp ∙ ap-irr-qq pp-qq refl ∙ qq-comp) refl ∙ qq-comp) refl ∙ qq-comp) refl ∙ star-comp 
    

    star-qqqqpp' : {n m : ℕ} {g : Mor n m} {B : Ob (suc (suc m))} {A : Ob (suc m)} {B= : ft B ≡ A} {X : Ob m} {A= : ft A ≡ X} {g₁ : ∂₁ g ≡ X} →
      star (qq (qq (qq g A A= g₁) B B= qq₁)
               (star (pp B) (star (pp A) A A= (pp₁ ∙ A=)) (ft-star ∙ pp₀) (pp₁ ∙ B=))
               (ft-star ∙ pp₀) qq₁)
           (star (qq (pp B)
                     (star (pp A) A A= (pp₁ ∙ A=))
                     (ft-star ∙ pp₀) (pp₁ ∙ B=))
                 (star (qq (pp A) A A= (pp₁ ∙ A=))
                       B B= qq₁)
                 (ft-star ∙ qq₀) qq₁)
           (ft-star ∙ qq₀) qq₁
      ≡
      star (qq (pp (star (qq g A A= g₁) B B= qq₁))
               (star (pp (star g A A= g₁)) (star g A A= g₁) ft-star (pp₁ ∙ ft-star))
               (ft-star ∙ pp₀) (pp₁ ∙ ft-star ∙ qq₀))
           (star (qq (pp (star g A A= g₁)) (star g A A= g₁) ft-star (pp₁ ∙ ft-star))
                 (star (qq g A A= g₁) B B= qq₁)
                 (ft-star ∙ qq₀) qq₁)
           (ft-star ∙ qq₀) qq₁
    star-qqqqpp' = ! star-comp ∙ ! (star-comp {g₀ = qq₀}) ∙ ap-irr-star (ap-irr-comp refl (! qq-comp) ∙ ! (qq-comp {g₀ = pp₀}) ∙ ap-irr-qq (ap-irr-comp refl pp-qq ∙ ! assoc ∙ ap-irr-comp pp-qq refl ∙ assoc {g₀ = pp₀ }) refl ∙ qq-comp ∙ ap-irr-comp refl qq-comp {g₀' = qq₀} ) refl ∙ star-comp ∙ star-comp 
    
    starstar : {g : Mor n m} {B : Ob (suc (suc m))} {A : Ob (suc m)} {B= : ft B ≡ A} {X : Ob m} (A= : ft A ≡ X) {g₁ : ∂₁ g ≡ X} {a : Mor m (suc m)} (aₛ : is-section a) {a₁ : ∂₁ a ≡ A}
             → star g (star a B B= a₁) (ft-star ∙ is-section₀ aₛ a₁ ∙ A=) g₁ ≡ star (starTm g a (is-section₀ aₛ a₁ ∙ A=) g₁) (star+ g B B= A= g₁) (ft-star ∙ qq₀) (starTm₁ g A= a aₛ a₁ g₁)
    starstar {g = g} {B} {B=} A= {g₁} {a} aₛ {a₁} = ! star-comp ∙ ap-irr-star (ss-qq ∙ ap-irr-comp (ap-irr-qq (! assoc ∙ ap-irr-comp (is-section= A= aₛ a₁) refl ∙ id-right g₁) refl) refl {g₀' = qq₀}) refl ∙ star-comp

    starstar+ : {g : Mor n m} {C : Ob (suc (suc (suc m)))} {B : Ob (suc (suc m))} {C= : ft C ≡ B} {A : Ob (suc m)} {B= : ft B ≡ A} {X : Ob m} (A= : ft A ≡ X) {g₁ : ∂₁ g ≡ X} {a : Mor m (suc m)} (aₛ : is-section a) {a₁ : ∂₁ a ≡ A}
              → star+ g (star+ a C C= B= a₁) (ft-star ∙ qq₀) (ft-star ∙ is-section₀ aₛ a₁ ∙ A=) g₁ ≡ star+ (starTm g a (is-section₀ aₛ a₁ ∙ A=) g₁) (star++ g C C= B= A= g₁) (ft-star ∙ qq₀ ) (ft-star ∙ qq₀) (starTm₁ g A= a aₛ a₁ g₁)
    starstar+ {g = g} {C} {B} {C=} {B= = B=} A= {g₁} {a} aₛ {a₁} = ! star-comp ∙ ap-irr-star (! qq-comp ∙ ap-irr-qq (ss-qq ∙ ap-irr-comp (ap-irr-qq (! assoc ∙ ap-irr-comp (is-section= A= aₛ a₁) refl ∙ id-right g₁) refl) refl {g₀' = qq₀}) refl ∙ qq-comp) refl ∙ star-comp

    starstar++ : {g : Mor n m} {D : Ob (suc (suc (suc (suc m))))} {C : Ob (suc (suc (suc m)))} {D= : ft D ≡ C} {B : Ob (suc (suc m))} {C= : ft C ≡ B} {A : Ob (suc m)} {B= : ft B ≡ A} {X : Ob m} (A= : ft A ≡ X) {g₁ : ∂₁ g ≡ X} {a : Mor m (suc m)} (aₛ : is-section a) {a₁ : ∂₁ a ≡ A}
                 → star++ g (star++ a D D= C= B= a₁) (ft-star ∙ qq₀) (ft-star ∙ qq₀) (ft-star ∙ is-section₀ aₛ a₁ ∙ A=) g₁ ≡ star++ (starTm g a (is-section₀ aₛ a₁ ∙ A=) g₁) (star+++ g D D= C= B= A= g₁) (ft-star ∙ qq₀) (ft-star ∙ qq₀) (ft-star ∙ qq₀) (starTm₁ g A= a aₛ a₁ g₁)
    starstar++ {g = g} {D} {C} {D=} {B} {C=} {B= = B=} A= {g₁} {a} aₛ {a₁} = ! star-comp ∙ ap-irr-star (! qq-comp ∙ ap-irr-qq (! qq-comp ∙ ap-irr-qq (ss-qq ∙ ap-irr-comp (ap-irr-qq (! assoc ∙ ap-irr-comp (is-section= A= aₛ a₁) refl ∙ id-right g₁) refl) refl {g₀' = qq₀}) refl ∙ qq-comp) refl ∙ qq-comp) refl ∙ star-comp


  pp^  : (k : Fin n) → Ob n → Mor n (n -F k)
  pp^₀ : (k : Fin n) (X : Ob n) → ∂₀ (pp^ k X) ≡ X

  pp^ last X = id X
  pp^ (prev last) X = pp X
  pp^ (prev k@(prev _)) X = comp (pp^ k (ft X)) (pp X) (pp^₀ k (ft X)) pp₁ -- (pp₁ ∙ ! (pp^₀ k (ft X)))

  pp^₀ last X = id₀
  pp^₀ (prev last) X = pp₀
  pp^₀ (prev k@(prev _)) X = comp₀ ∙ pp₀

  pp^prev  : {k : Fin n} {X : Ob (suc n)} {Y : Ob n} (p : ft X ≡ Y) → pp^ (prev k) X ≡ comp (pp^ k Y) (pp X) (pp^₀ k Y) (pp₁ ∙ p)
  pp^prev {k = last} refl = ! (id-right pp₁)
  pp^prev {k = prev k} refl = refl

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

  varCₛ : (k : Fin n) (X : Ob n) → is-section (varC k X)
  varCₛ k X = ssₛ

  varC₀ : {k : Fin n} {X : Ob n} → ∂₀ (varC k X) ≡ X
  varC₀ {k = k} {X} = ss₀ ∙ pp^₀ k X

  varCL₁ : {X : Ob (suc n)} {Y : Ob n} {X= : ft X ≡ Y} → ∂₁ (varC last X) ≡ star (pp X) X X= (pp₁ ∙ X=)
  varCL₁ = ss₁ id₁ ∙ ap-irr-star (id-left pp₀) refl

  varCL-qq : {X : Ob (suc n)} {Y : Ob n} (X= : ft X ≡ Y) → comp (qq (pp X) X X= (pp₁ ∙ X=)) (varC last X) qq₀ varCL₁ ≡ id X
  varCL-qq X= = ! (ss-qq ∙ ap-irr-comp (ap-irr-qq (id-left pp₀) refl) refl)

  varC+₁ : (k : Fin n) {X : Ob (suc n)} {Y : Ob n} (Y= : ft X ≡ Y) {Z : Ob (suc n)} (var₁ : ∂₁ (varC k Y) ≡ Z) → ∂₁ (varC (prev k) X) ≡ star (pp X) Z (! (is-section₀ (varCₛ k Y) var₁) ∙ varC₀) (pp₁ ∙ Y=)
  varC+₁ last refl refl = ss₁ pp₁ ∙ star-comp ∙ ap-irr-star refl (! varCL₁)
  varC+₁ (prev k) {X = X} {Y = Y} refl refl = ss₁ (comp₁ ∙ pp^₁ (prev k) Y) ∙ ap-irr-star (! assoc) refl ∙ star-comp ∙ (ap-irr-star refl (! (ss₁ (pp^₁ (prev k) Y))))

  abstract
    star-varCL : {g : Mor n m} {A : Ob (suc m)} {X : Ob m} {A= : ft A ≡ X} {g₁ : ∂₁ g ≡ X} → starTm (qq g A A= g₁) (varC last A) (ss₀ ∙ id₀) qq₁ ≡ varC last (star g A A= g₁)
    star-varCL {A = A} = ss-comp {U = A} ∙ ap ss (! assoc ∙ ap-irr-comp (! (ss-qq {f₁ = id₁})) refl ∙ id-right qq₁) ∙ ! (ss-comp {U = A} ∙ ap ss (id-left qq₀))

    star-varCL' : {g : Mor n (suc m)} {A : Ob (suc m)} {g₁ : ∂₁ g ≡ A} → starTm g (varC last A) (ss₀ ∙ id₀) g₁ ≡ ss g
    star-varCL' {g₁ = g₁} = ss-comp ∙ ap ss (! assoc ∙ ap-irr-comp (! (ss-qq {f₁ = id₁})) refl ∙ id-right g₁)

    star-varCL'' : {g : Mor m (suc k)} {f : Mor n m} {X : Ob m} {g₀ : ∂₀ g ≡ X} {f₁ : ∂₁ f ≡ X} → starTm f (ss g) (ss₀ ∙ g₀) f₁ ≡ ss (comp g f g₀ f₁)
    star-varCL'' = ss-comp ∙ ap ss (! assoc ∙ ap-irr-comp (! (ss-qq {f₁ = refl})) refl)

    starTm-comp : {m n k : ℕ} {g : Mor m k} {f : Mor n m} {Y : Ob m} (g₀ : ∂₀ g ≡ Y) {f₁ : ∂₁ f ≡ Y} {u : Mor k (suc k)} {X : Ob k} {u₀ : ∂₀ u ≡ X} {g₁ : ∂₁ g ≡ X}
                → starTm (comp g f g₀ f₁) u u₀ (comp₁ ∙ g₁) ≡ starTm f (starTm g u u₀ g₁) (ss₀ ∙ comp₀ ∙ g₀) f₁
    starTm-comp g₀ = ap ss (! assoc) ∙ ! (star-varCL'' {g₀ = comp₀ ∙ g₀})

    starTm-id : {X : Ob n} {u : Mor n (suc n)} (u₀ : ∂₀ u ≡ X) (uₛ : is-section u) → starTm (id X) u u₀ id₁ ≡ u
    starTm-id u₀ uₛ = ap ss (id-left u₀) ∙ ss-of-section _ uₛ
 
    star-varC+ : {g : Mor n m} {B : Ob (suc (suc m))} {A : Ob (suc m)} {X : Ob m} {B= : ft B ≡ A} {A= : ft A ≡ X} {g₁ : ∂₁ g ≡ X}
             → starTm (qq (qq g A A= g₁) B B= qq₁) (varC (prev last) B) (ss₀ ∙ pp₀) qq₁
               ≡ varC (prev last) (star (qq g A A= g₁) B B= qq₁)
    star-varC+ {A = A} {B= = B=} = ss-comp {U = A} ∙ ap ss (! assoc ∙ ap-irr-comp (! (ss-qq {f₁ = pp₁ ∙ B=})) refl ∙ pp-qq ∙ ap-irr-comp refl refl) ∙ ! (ss-comp {f₁ = pp₁ ∙ ft-star ∙ qq₀})

    star-varC+' : {a : Mor m (suc m)} {B : Ob (suc (suc m))} {A : Ob (suc m)} {B= : ft B ≡ A} (aₛ : is-section a) {a₁ : ∂₁ a ≡ A}
             → starTm (qq a B B= a₁) (varC (prev last) B) (varC₀ {k = prev last}) qq₁
               ≡ starTm (pp (star a B B= a₁)) a (is-section₀ aₛ a₁) (pp₁ ∙ ft-star ∙ is-section₀ aₛ a₁)
    star-varC+' {A = A} {B= = B=} _ = ss-comp ∙ ap ss (! assoc ∙ ap-irr-comp (! (ss-qq {f₁ = pp₁ ∙ B=}) ∙ refl) refl ∙ pp-qq ∙ ap-irr-comp refl refl)

    ss-id₁ : {X : Ob (suc n)} {Y : Ob n} {X= : ft X ≡ Y} → ∂₁ (ss (id X)) ≡ star (pp X) X X= (pp₁ ∙ X=)
    ss-id₁ = ss₁ id₁ ∙ ap-irr-star (id-left pp₀) refl

    star-varCL-star-qqpp : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} → star (varC last A) (star (qq (pp A) A A= (pp₁ ∙ A=)) B B= qq₁) (ft-star ∙ qq₀) varCL₁ ≡ B
    star-varCL-star-qqpp {B= = B=} = ! (star-comp {g₀ = qq₀}) ∙ ap-irr-star (ap-irr-comp (! (id-left qq₀) ∙ ap-irr-comp (ap-irr-qq refl refl) (ap id (ap-irr-star refl refl) ∙ ! qq-id) ∙ ! (qq-comp {g₁ = pp₁})) refl ∙ ! (ss-qq {f₁ = id₁})) refl ∙ star-id {p = B=}

    star-qqvarCL-star-qqqqpp : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {C : Ob (suc (suc (suc n)))} {C= : ft C ≡ B}
                           → star (qq (varC last A) (star (qq (pp A) A A= (pp₁ ∙ A=)) B B= qq₁) (ft-star ∙ qq₀) varCL₁)
                                  (star (qq (qq (pp A) A A= (pp₁ ∙ A=)) B B= qq₁)
                                        C
                                        C=
                                        qq₁)
                                  (ft-star ∙ qq₀)
                                  qq₁ ≡ C
    star-qqvarCL-star-qqqqpp {B= = B=} {C= = C=} = ! (star-comp {g₀ = qq₀}) ∙ ap-irr-star (! (qq-comp {g₀ = qq₀}) ∙ ap-irr-qq (ap-irr-comp (ap-irr-qq (! (id-left pp₀)) refl) refl ∙ ! (ss-qq {f₁ = id₁})) refl ∙ qq-id {p = B=}) refl ∙ star-id {p = C=}

  -- thing : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ}
  --       → starTm (qq (varC last A)
  --                    (star (qq (pp A) A A= (pp₁ ∙ A=)) (star (pp A) A A= (pp₁ ∙ A=)) (ft-star ∙ pp₀) qq₁)
  --                    (ft-star ∙ qq₀)
  --                    varCL₁)
  --                (varC (prev last) (star (qq (pp A) A A= (pp₁ ∙ A=)) (star (pp A) A A= (pp₁ ∙ A=)) (ft-star ∙ pp₀) qq₁))
  --                (ss₀ ∙ pp₀ ∙ refl)
  --                qq₁
  --         ≡ varC (prev last) (star (pp A) A A= (pp₁ ∙ A=))
  -- thing = {!!}

{- Contextual categories with structure corresponding to the type theory we are interested in -}

record CCatwithUU (ccat : CCat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)

  field
    UUStr  : (i : ℕ) (Γ : Ob n) → Ob (suc n)
    UUStr= : {i : ℕ} {Γ : Ob n} → ft (UUStr i Γ) ≡ Γ
    UUStrNat' : {i : ℕ} (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (g₁ : ∂₁ g ≡ Γ)
             → star g (UUStr i Γ) UUStr= g₁ ≡ UUStr i Δ
  UUStrNat : {i : ℕ} {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {g₁ : ∂₁ g ≡ Γ}
             → star g (UUStr i Γ) UUStr= g₁ ≡ UUStr i Δ
  UUStrNat g₀ {g₁ = g₁} = UUStrNat' _ _ g₀ _ g₁

record CCatwithEl (ccat : CCat) (ccatuu : CCatwithUU ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu

  field
    ElStr  : (i : ℕ) (Γ : Ob n) (v : MorC n (suc n)) (vₛ : is-section v) (v₁ : ∂₁ v ≡ UUStr i Γ) → Ob (suc n)
    ElStr= : {i : ℕ} {Γ : Ob n} {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ UUStr i Γ} → ft (ElStr i Γ v vₛ v₁) ≡ Γ
    ElStrNat' : {i : ℕ} (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (v : MorC m (suc m)) (vₛ : is-section v) (v₁ : ∂₁ v ≡ UUStr i Γ) (g₁ : ∂₁ g ≡ Γ)
             → star g (ElStr i Γ v vₛ v₁) ElStr= g₁ ≡ ElStr i Δ (starTm g v (is-section₀ vₛ v₁ ∙ UUStr=) g₁) ssₛ (starTm₁ g UUStr= v vₛ v₁ g₁ ∙ UUStrNat g₀)

  ElStrNat : {i : ℕ} {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {v : MorC m (suc m)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ UUStr i Γ} {g₁ : ∂₁ g ≡ Γ}
             → star g (ElStr i Γ v vₛ v₁) ElStr= g₁ ≡ ElStr i Δ (starTm g v (is-section₀ vₛ v₁ ∙ UUStr=) g₁) ssₛ (starTm₁ g UUStr= v vₛ v₁ g₁ ∙ UUStrNat g₀)
  ElStrNat g₀ {g₁ = g₁} = ElStrNat' _ _ g₀ _ _ _ _ g₁


record CCatwithPi (ccat : CCat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)

  field
    PiStr  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) → Ob (suc n)
    PiStr= : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} → ft (PiStr Γ A A= B B=) ≡ Γ
    PiStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (A : Ob (suc m)) (A= : ft A ≡ Γ) (B : Ob (suc (suc m))) (B= : ft B ≡ A) (g₁ : ∂₁ g ≡ Γ)
             → star g (PiStr Γ A A= B B=) PiStr= g₁ ≡ PiStr Δ (star g A A= g₁) (ft-star ∙ g₀) (star+ g B B= A= g₁) (ft-star ∙ qq₀)

  PiStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {g₁ : ∂₁ g ≡ Γ}
             → star g (PiStr Γ A A= B B=) PiStr= g₁ ≡ PiStr Δ (star g A A= g₁) (ft-star ∙ g₀) (star+ g B B= A= g₁) (ft-star ∙ qq₀)
  PiStrNat g₀ {g₁ = g₁} = PiStrNat' _ _ g₀ _ _ _ _ _ g₁


record CCatwithSig (ccat : CCat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)

  field
    SigStr  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) → Ob (suc n)
    SigStr= : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} → ft (SigStr Γ A A= B B=) ≡ Γ
    SigStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (A : Ob (suc m)) (A= : ft A ≡ Γ) (B : Ob (suc (suc m))) (B= : ft B ≡ A) (g₁ : ∂₁ g ≡ Γ)
             → star g (SigStr Γ A A= B B=) SigStr= g₁ ≡ SigStr Δ (star g A A= g₁) (ft-star ∙ g₀) (star+ g B B= A= g₁) (ft-star ∙ qq₀)

  SigStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {g₁ : ∂₁ g ≡ Γ}
             → star g (SigStr Γ A A= B B=) SigStr= g₁ ≡ SigStr Δ (star g A A= g₁) (ft-star ∙ g₀) (star+ g B B= A= g₁) (ft-star ∙ qq₀)
  SigStrNat g₀ {g₁ = g₁} = SigStrNat' _ _ g₀ _ _ _ _ _ g₁

record CCatwithEmpty (ccat : CCat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)

  field
    EmptyStr : (Γ : Ob n) → Ob (suc n)
    EmptyStr= : {Γ : Ob n} → ft (EmptyStr Γ) ≡ Γ
    EmptyStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) {g₁ : ∂₁ g ≡ Γ}
                 → star g (EmptyStr Γ) EmptyStr= g₁ ≡ EmptyStr Δ

  EmptyStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {g₁ : ∂₁ g ≡ Γ}
              → star g (EmptyStr Γ) EmptyStr= g₁ ≡ EmptyStr Δ
  EmptyStrNat g₀ = EmptyStrNat' _ _ g₀ _
 
record CCatwithUnit (ccat : CCat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)

  field
    UnitStr : (Γ : Ob n) → Ob (suc n)
    UnitStr= : {Γ : Ob n} → ft (UnitStr Γ) ≡ Γ
    UnitStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) {g₁ : ∂₁ g ≡ Γ}
                 → star g (UnitStr Γ) UnitStr= g₁ ≡ UnitStr Δ

  UnitStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {g₁ : ∂₁ g ≡ Γ}
              → star g (UnitStr Γ) UnitStr= g₁ ≡ UnitStr Δ
  UnitStrNat g₀ = UnitStrNat' _ _ g₀ _
   
record CCatwithNat (ccat : CCat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)

  field
    NatStr  : (Γ : Ob n) → Ob (suc n)
    NatStr= : {Γ : Ob n} → ft (NatStr Γ) ≡ Γ
    NatStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) {g₁ : ∂₁ g ≡ Γ}
             → star g (NatStr Γ) NatStr= g₁ ≡ NatStr Δ
             
  NatStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {g₁ : ∂₁ g ≡ Γ}
             → star g (NatStr Γ) NatStr= g₁ ≡ NatStr Δ
  NatStrNat g₀ = NatStrNat' _ _ g₀ _ 

record CCatwithId (ccat : CCat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)

  field
    IdStr   : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) (b : MorC n (suc n)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ A) → Ob (suc n)
    IdStr=  : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} → ft (IdStr Γ A A= a aₛ a₁ b bₛ b₁) ≡ Γ
    IdStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (A : Ob (suc m)) (A= : ft A ≡ Γ) (a : MorC m (suc m)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) (b : MorC m (suc m)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ A) (g₁ : ∂₁ g ≡ Γ)
             (let a₀ = is-section₀ aₛ a₁ ∙ A=) (let b₀ = is-section₀ bₛ b₁ ∙ A=)
             → star g (IdStr Γ A A= a aₛ a₁ b bₛ b₁) IdStr= g₁ ≡ IdStr Δ (star g A A= g₁) (ft-star ∙ g₀) (starTm g a a₀ g₁) ssₛ (starTm₁ g A= a aₛ a₁ g₁) (starTm g b b₀ g₁) ssₛ (starTm₁ g A= b bₛ b₁ g₁)
  abstract
    IdStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC m (suc m)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A} {g₁ : ∂₁ g ≡ Γ}
               (let a₀ = is-section₀ aₛ a₁ ∙ A=) (let b₀ = is-section₀ bₛ b₁ ∙ A=)
               → star g (IdStr Γ A A= a aₛ a₁ b bₛ b₁) IdStr= g₁ ≡ IdStr Δ (star g A A= g₁) (ft-star ∙ g₀) (starTm g a a₀ g₁) ssₛ (starTm₁ g A= a aₛ a₁ g₁) (starTm g b b₀ g₁) ssₛ (starTm₁ g A= b bₛ b₁ g₁)
    IdStrNat g₀ = IdStrNat' _ _ g₀ _ _ _ _ _ _ _ _ _ _

    ap-irr-IdStr : {Γ Γ' : Ob n} (rΓ : Γ ≡ Γ') {A A' : Ob (suc n)} (rA : A ≡ A') {A= : ft A ≡ Γ} {A'= : ft A' ≡ Γ'} {u u' : MorC n (suc n)} (ru : u ≡ u') {uₛ : is-section u} {u'ₛ : is-section u'} {u₁ : ∂₁ u ≡ A} {u'₁ : ∂₁ u' ≡ A'} {v v' : MorC n (suc n)} (rv : v ≡ v') {vₛ : is-section v} {v'ₛ : is-section v'} {v₁ : ∂₁ v ≡ A} {v'₁ : ∂₁ v' ≡ A'} → IdStr Γ A A= u uₛ u₁ v vₛ v₁ ≡ IdStr Γ' A' A'= u' u'ₛ u'₁ v' v'ₛ v'₁
    ap-irr-IdStr refl refl refl refl = refl

  T-ftP : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) → Ob (suc (suc (suc n)))
  T-ftP  Γ A A= = IdStr wA wwA (ft-star ∙ pp₀)
                        (varC (prev last) wA) (varCₛ (prev last) wA) (varC+₁ last (ft-star ∙ pp₀) varCL₁)
                        (varC last wA) (varCₛ last wA) varCL₁
                  where
                    wA = star (pp A) A A= (pp₁ ∙ A=)
                    wwA = star (pp wA) wA (ft-star ∙ pp₀) (pp₁ ∙ ft-star ∙ pp₀)

  abstract
    T-ftP= : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} → ft (T-ftP Γ A A=) ≡ star (pp A) A A= (pp₁ ∙ A=)
    T-ftP= = IdStr=
                                
    T-ftPNat : {g : MorC m n} {Δ : Ob m} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {g₁ : ∂₁ g ≡ Γ} → star++ g (T-ftP Γ A A=) T-ftP= (ft-star ∙ pp₀) A= g₁ ≡ T-ftP Δ (star g A A= g₁) (ft-star ∙ g₀)
    T-ftPNat g₀ =  IdStrNat qq₀ ∙ ap-irr-IdStr (star-pp g₀) (star-pp qq₀ ∙ ap-irr-star (ap pp (star-pp g₀)) (star-pp g₀)) (star-varC+ ∙ ap (varC (prev last)) (star-pp g₀)) (star-varCL ∙ ap (varC last) (star-pp g₀))
  
  T-jjStr₁ : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ)
             (P : Ob (suc (suc (suc (suc n))))) (P= : ft P ≡ T-ftP Γ A A=)
             (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A)
             (b : MorC n (suc n)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ A)
             (p : MorC n (suc n)) (pₛ : is-section p) (p₁ : ∂₁ p ≡ IdStr Γ A A= a aₛ a₁ b bₛ b₁)
             → Ob (suc n)
  T-jjStr₁ Γ A A= P P= a aₛ a₁ b bₛ b₁ p pₛ p₁ = let wA = star (pp A) A A= (pp₁ ∙ A=)
                                                     [wA][a] = star-pp' A= A= aₛ a₁
                                                     [wA][b] = star-pp' A= A= bₛ b₁
                                                     a₀ = is-section₀ aₛ a₁ ∙ A=
                                                     b₀ = is-section₀ bₛ b₁ ∙ A=
                                                     p₀ = is-section₀ pₛ p₁ ∙ IdStr=
                                                 in
                                                       star p (star+ b (star++ a P P= T-ftP= (ft-star ∙ pp₀) a₁)
                                                                       (ft-star ∙ qq₀) (ft-star ∙ qq₀) (b₁ ∙ ! [wA][a]))
                                                              (ft-star ∙ qq₀)
                                                              (p₁ ∙ ! (ap-irr-star refl (IdStrNat (qq₀ ∙ [wA][a]) ∙
                                                                                         ap-irr-IdStr refl (star-pp a₀ ∙ ap-irr-star (ap pp [wA][a]) [wA][a]) {A'= = ft-star ∙ pp₀}
                                                                                                           (star-varC+' aₛ ∙ ap-irr-starTm (ap pp [wA][a]) refl) {u'ₛ = ssₛ} {u'₁ = starTm₁ (pp A) A= a aₛ a₁ (pp₁ ∙ A=)}
                                                                                                      (star-varCL ∙ ap (varC last) [wA][a]) {v'ₛ = ssₛ} {v'₁ = varCL₁}) ∙
                                                               IdStrNat b₀ ∙ ap-irr-IdStr refl [wA][b] (! (starTm-comp pp₀) ∙ ap-irr-starTm (is-section= A= bₛ b₁) refl ∙ starTm-id a₀ aₛ)
                                                                                                       (star-varCL' ∙ ss-of-section _ bₛ)))

  



record CCatwithuu (ccat : CCat) (ccatuu : CCatwithUU ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu

  field
    uuStr  : (i : ℕ) (Γ : Ob n) → MorC n (suc n)
    uuStrₛ : {i : ℕ} {Γ : Ob n} → is-section (uuStr i Γ)
    uuStr₁ : {i : ℕ} {Γ : Ob n} → ∂₁ (uuStr i Γ) ≡ UUStr (suc i) Γ

  uuStr₀ : {i : ℕ} {Γ : Ob n} → ∂₀ (uuStr i Γ) ≡ Γ
  uuStr₀ {_} = is-section₀ uuStrₛ uuStr₁ ∙ UUStr=

  field
    uuStrNat' : {i : ℕ} (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (g₁ : ∂₁ g ≡ Γ)
             → starTm g (uuStr i Γ) uuStr₀ g₁ ≡ uuStr i Δ


  uuStrNat : {i : ℕ} {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {g₁ : ∂₁ g ≡ Γ}
             → starTm g (uuStr i Γ) uuStr₀ g₁ ≡ uuStr i Δ
  uuStrNat g₀ = uuStrNat' _ _ g₀ _ _


record CCatwithpi (ccat : CCat) (ccatuu : CCatwithUU ccat) (ccatel : CCatwithEl ccat ccatuu) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu
  open CCatwithEl ccatel


  field
    piStr  : (i : ℕ) (Γ : Ob n) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i Γ) (b : MorC (suc n) (suc (suc n))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)) → MorC n (suc n)
    piStrₛ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} → is-section (piStr i Γ a aₛ a₁ b bₛ b₁)
    piStr₁ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} → ∂₁ (piStr i Γ a aₛ a₁ b bₛ b₁) ≡ UUStr i Γ

  piStr₀ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC(suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} → ∂₀ (piStr i Γ a aₛ a₁ b bₛ b₁) ≡ Γ
  piStr₀ {_} = is-section₀ piStrₛ piStr₁ ∙ UUStr=

  field
    piStrNat' : {i : ℕ} (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (a : MorC m (suc m)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i Γ)
                                                (b : MorC (suc m) (suc (suc m))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)) (g₁ : ∂₁ g ≡ Γ)
                                                (let a₀ = is-section₀ aₛ a₁ ∙ UUStr=) (let b₀ = is-section₀ bₛ b₁ ∙ UUStr=)
             → starTm g (piStr i Γ a aₛ a₁ b bₛ b₁) piStr₀ g₁ ≡ piStr i Δ (starTm g a a₀ g₁) ssₛ (starTm₁ g UUStr= a aₛ a₁ g₁ ∙ UUStrNat g₀)
                                                                           (starTm+ g ElStr= b b₀ g₁) ssₛ (starTm+₁ g UUStr= ElStr= b bₛ b₁ g₁ ∙ UUStrNat (qq₀ ∙ ElStrNat g₀))

  piStrNat : {i : ℕ} {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ}
                                                {b : MorC (suc m) (suc (suc m))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} {g₁ : ∂₁ g ≡ Γ}
                                                (let a₀ = is-section₀ aₛ a₁ ∙ UUStr=) (let b₀ = is-section₀ bₛ b₁ ∙ UUStr=)
             → starTm g (piStr i Γ a aₛ a₁ b bₛ b₁) piStr₀ g₁ ≡ piStr i Δ (starTm g a a₀ g₁) ssₛ (starTm₁ g UUStr= a aₛ a₁ g₁ ∙ UUStrNat g₀)
                                                                           (starTm+ g ElStr= b b₀ g₁) ssₛ (starTm+₁ g UUStr= ElStr= b bₛ b₁ g₁ ∙ UUStrNat (qq₀ ∙ ElStrNat g₀))
  piStrNat g₀ {g₁ = g₁} = piStrNat' _ _ g₀ _ _ _ _ _ _ _ g₁

record CCatwithlam (ccat : CCat) (ccatpi : CCatwithPi ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithPi ccatpi

  field
    lamStr  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (u : MorC (suc n) (suc (suc n))) (uₛ : is-section u) (u₁ : ∂₁ u ≡ B) → MorC n (suc n)
    lamStrₛ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} → is-section (lamStr Γ A A= B B= u uₛ u₁)
    lamStr₁ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} → ∂₁ (lamStr Γ A A= B B= u uₛ u₁) ≡ PiStr Γ A A= B B=

  lamStr₀ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC(suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} → ∂₀ (lamStr Γ A A= B B= u uₛ u₁) ≡ Γ
  lamStr₀ {_} = is-section₀ lamStrₛ lamStr₁ ∙ PiStr=
   
  field
    lamStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (A : Ob (suc m)) (A= : ft A ≡ Γ) (B : Ob (suc (suc m))) (B= : ft B ≡ A) (u : MorC (suc m) (suc (suc m))) (uₛ : is-section u) (u₁ : ∂₁ u ≡ B) (g₁ : ∂₁ g ≡ Γ) (let u₀ = is-section₀ uₛ u₁ ∙ B=)
             → starTm g (lamStr Γ A A= B B= u uₛ u₁) lamStr₀ g₁ ≡ lamStr Δ (star g A A= g₁) (ft-star ∙ g₀) (star+ g B B= A= g₁) (ft-star ∙ qq₀) (starTm+ g A= u u₀ g₁) ssₛ (starTm+₁ g B= A= u uₛ u₁ g₁)

  lamStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {u : MorC (suc m) (suc (suc m))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} {g₁ : ∂₁ g ≡ Γ} (let u₀ = is-section₀ uₛ u₁ ∙ B=)
             → starTm g (lamStr Γ A A= B B= u uₛ u₁) lamStr₀ g₁ ≡ lamStr Δ (star g A A= g₁) (ft-star ∙ g₀) (star+ g B B= A= g₁) (ft-star ∙ qq₀) (starTm+ g A= u u₀ g₁) ssₛ (starTm+₁ g B= A= u uₛ u₁ g₁)
  lamStrNat g₀ = lamStrNat' _ _ g₀ _ _ _ _ _ _ _ _ _

record CCatwithapp (ccat : CCat) (ccatpi : CCatwithPi ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithPi ccatpi
 
  field
    appStr  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (f : MorC n (suc n)) (fₛ : is-section f) (f₁ : ∂₁ f ≡ PiStr Γ A A= B B=) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) → MorC n (suc n)
    appStrₛ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {f : MorC n (suc n)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr Γ A A= B B=} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → is-section (appStr Γ A A= B B= f fₛ f₁ a aₛ a₁)
    appStr₁ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {f : MorC n (suc n)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr Γ A A= B B=} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → ∂₁ (appStr Γ A A= B B= f fₛ f₁ a aₛ a₁) ≡ star a B B= a₁

  appStr₀ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {f : MorC n (suc n)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr Γ A A= B B=} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → ∂₀ (appStr Γ A A= B B= f fₛ f₁ a aₛ a₁) ≡ Γ
  appStr₀ {_} {_} {_} {A=} {_} {_} {_} {_} {_} {_} {aₛ} {a₁} = is-section₀ appStrₛ appStr₁ ∙ ft-star ∙ is-section₀ aₛ a₁ ∙ A=
  
  field
    appStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (A : Ob (suc m)) (A= : ft A ≡ Γ) (B : Ob (suc (suc m))) (B= : ft B ≡ A) (f : MorC m (suc m)) (fₛ : is-section f) (f₁ : ∂₁ f ≡ PiStr Γ A A= B B=)
                (a : MorC m (suc m)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) (g₁ : ∂₁ g ≡ Γ)
                (let a₀ = is-section₀ aₛ a₁ ∙ A=) (let f₀ = is-section₀ fₛ f₁ ∙ PiStr=)
             → starTm g (appStr Γ A A= B B= f fₛ f₁ a aₛ a₁) appStr₀ g₁
                ≡ appStr Δ (star g A A= g₁)
                           (ft-star ∙ g₀)
                           (star+ g B B= A= g₁)
                           (ft-star ∙ qq₀)
                           (starTm g f f₀ g₁) ssₛ (starTm₁ g PiStr= f fₛ f₁ g₁ ∙ PiStrNat g₀)
                           (starTm g a a₀ g₁) ssₛ (starTm₁ g A= a aₛ a₁ g₁)


  appStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {f : MorC m (suc m)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr Γ A A= B B=}
               {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {g₁ : ∂₁ g ≡ Γ}
                (let a₀ = is-section₀ aₛ a₁ ∙ A=) (let f₀ = is-section₀ fₛ f₁ ∙ PiStr=)
             → starTm g (appStr Γ A A= B B= f fₛ f₁ a aₛ a₁) appStr₀ g₁
                ≡ appStr Δ (star g A A= g₁)
                           (ft-star ∙ g₀)
                           (star+ g B B= A= g₁)
                           (ft-star ∙ qq₀)
                           (starTm g f f₀ g₁) ssₛ (starTm₁ g PiStr= f fₛ f₁ g₁ ∙ PiStrNat g₀)
                           (starTm g a a₀ g₁) ssₛ (starTm₁ g A= a aₛ a₁ g₁)
  appStrNat g₀ = appStrNat' _ _ g₀ _ _ _ _ _ _ _ _ _ _ _ _


record CCatwithsig (ccat : CCat) (ccatuu : CCatwithUU ccat) (ccatel : CCatwithEl ccat ccatuu) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu
  open CCatwithEl ccatel

  field
    sigStr  : (i : ℕ) (Γ : Ob n) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i Γ) (b : MorC (suc n) (suc (suc n))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)) → MorC n (suc n)
    sigStrₛ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} → is-section (sigStr i Γ a aₛ a₁ b bₛ b₁)
    sigStr₁ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} → ∂₁ (sigStr i Γ a aₛ a₁ b bₛ b₁) ≡ UUStr i Γ

  sigStr₀ : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC(suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} → ∂₀ (sigStr i Γ a aₛ a₁ b bₛ b₁) ≡ Γ
  sigStr₀ {_} = is-section₀ sigStrₛ sigStr₁ ∙ UUStr=

  field
    sigStrNat' : {i : ℕ} (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (a : MorC m (suc m)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i Γ)
                                                 (b : MorC (suc m) (suc (suc m))) (bₛ : is-section b) (b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)) (g₁ : ∂₁ g ≡ Γ)
                                                 (let a₀ = is-section₀ aₛ a₁ ∙ UUStr=) (let b₀ = is-section₀ bₛ b₁ ∙ UUStr=)
             → starTm g (sigStr i Γ a aₛ a₁ b bₛ b₁) sigStr₀ g₁ ≡ sigStr i Δ (starTm g a a₀ g₁) ssₛ (starTm₁ g UUStr= a aₛ a₁ g₁ ∙ UUStrNat g₀)
                                                                              (starTm+ g ElStr= b b₀ g₁) ssₛ (starTm+₁ g UUStr= ElStr= b bₛ b₁ g₁ ∙ UUStrNat (qq₀ ∙ ElStrNat g₀))
  sigStrNat : {i : ℕ} {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ}
                                                 {b : MorC (suc m) (suc (suc m))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} {g₁ : ∂₁ g ≡ Γ}
                                                 (let a₀ = is-section₀ aₛ a₁ ∙ UUStr=) (let b₀ = is-section₀ bₛ b₁ ∙ UUStr=)
             → starTm g (sigStr i Γ a aₛ a₁ b bₛ b₁) sigStr₀ g₁ ≡ sigStr i Δ (starTm g a a₀ g₁) ssₛ (starTm₁ g UUStr= a aₛ a₁ g₁ ∙ UUStrNat g₀)
                                                                              (starTm+ g ElStr= b b₀ g₁) ssₛ (starTm+₁ g UUStr= ElStr= b bₛ b₁ g₁ ∙ UUStrNat (qq₀ ∙ ElStrNat g₀))
  sigStrNat g₀ = sigStrNat' _ _ g₀ _ _ _ _ _ _ _ _



record CCatwithpair (ccat : CCat) (ccatsig : CCatwithSig ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithSig ccatsig

  field
    pairStr  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) (b : MorC n (suc n)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ star a B B= a₁) → MorC n (suc n)
    pairStrₛ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B B= a₁} → is-section (pairStr Γ A A= B B= a aₛ a₁ b bₛ b₁)
    pairStr₁ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B B= a₁} → ∂₁ (pairStr Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ SigStr Γ A A= B B=

  pairStr₀ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B B= a₁} → ∂₀ (pairStr Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ Γ
  pairStr₀ {_} = is-section₀ pairStrₛ pairStr₁ ∙ SigStr=
  
  field
    pairStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (A : Ob (suc m)) (A= : ft A ≡ Γ) (B : Ob (suc (suc m))) (B= : ft B ≡ A) (a : MorC m (suc m)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) (b : MorC m (suc m)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ star a B B= a₁) (g₁ : ∂₁ g ≡ Γ)
                 (let a₀ = is-section₀ aₛ a₁ ∙ A=) (let b₀ = is-section₀ bₛ b₁ ∙ ft-star ∙ a₀)
             → starTm g (pairStr Γ A A= B B= a aₛ a₁ b bₛ b₁) pairStr₀ g₁ ≡ pairStr Δ (star g A A= g₁)
                                                                                      (ft-star ∙ g₀)
                                                                                      (star+ g B B= A= g₁)
                                                                                      (ft-star ∙ qq₀)
                                                                                      (starTm g a a₀ g₁) ssₛ (starTm₁ g A= a aₛ a₁ g₁)
                                                                                      (starTm g b b₀ g₁) ssₛ (starTm₁ g (ft-star ∙ a₀) b bₛ b₁ g₁ ∙ starstar A= aₛ)


  pairStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC m (suc m)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B B= a₁} {g₁ : ∂₁ g ≡ Γ}
                 (let a₀ = is-section₀ aₛ a₁ ∙ A=) (let b₀ = is-section₀ bₛ b₁ ∙ ft-star ∙ a₀)
             → starTm g (pairStr Γ A A= B B= a aₛ a₁ b bₛ b₁) pairStr₀ g₁ ≡ pairStr Δ (star g A A= g₁)
                                                                                      (ft-star ∙ g₀)
                                                                                      (star+ g B B= A= g₁)
                                                                                      (ft-star ∙ qq₀)
                                                                                      (starTm g a a₀ g₁) ssₛ (starTm₁ g A= a aₛ a₁ g₁)
                                                                                      (starTm g b b₀ g₁) ssₛ (starTm₁ g (ft-star ∙ a₀) b bₛ b₁ g₁ ∙ starstar A= aₛ)
  pairStrNat g₀ = pairStrNat' _ _ g₀ _ _ _ _ _ _ _ _ _ _ _ _


record CCatwithpr1 (ccat : CCat) (ccatsig : CCatwithSig ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithSig ccatsig

  field
    pr1Str  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ SigStr Γ A A= B B=) → MorC n (suc n)
    pr1Strₛ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} → is-section (pr1Str Γ A A= B B= u uₛ u₁)
    pr1Str₁ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} → ∂₁ (pr1Str Γ A A= B B= u uₛ u₁) ≡ A

  pr1Str₀ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} → ∂₀ (pr1Str Γ A A= B B= u uₛ u₁) ≡ Γ
  pr1Str₀ {_} {_} {_} {A=} = is-section₀ pr1Strₛ pr1Str₁ ∙ A=

  field
    pr1StrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (A : Ob (suc m)) (A= : ft A ≡ Γ) (B : Ob (suc (suc m))) (B= : ft B ≡ A) (u : MorC m (suc m)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ SigStr Γ A A= B B=) (g₁ : ∂₁ g ≡ Γ)
                (let u₀ = is-section₀ uₛ u₁ ∙ SigStr=)
             → starTm g (pr1Str Γ A A= B B= u uₛ u₁) pr1Str₀ g₁ ≡ pr1Str Δ (star g A A= g₁)
                                                                           (ft-star ∙ g₀)
                                                                           (star+ g B B= A= g₁)
                                                                           (ft-star ∙ qq₀)
                                                                           (starTm g u u₀ g₁) ssₛ (starTm₁ g SigStr= u uₛ u₁ g₁ ∙ SigStrNat g₀)

  pr1StrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} {g₁ : ∂₁ g ≡ Γ}
                (let u₀ = is-section₀ uₛ u₁ ∙ SigStr=)
             → starTm g (pr1Str Γ A A= B B= u uₛ u₁) pr1Str₀ g₁ ≡ pr1Str Δ (star g A A= g₁)
                                                                           (ft-star ∙ g₀)
                                                                           (star+ g B B= A= g₁)
                                                                           (ft-star ∙ qq₀)
                                                                           (starTm g u u₀ g₁) ssₛ (starTm₁ g SigStr= u uₛ u₁ g₁ ∙ SigStrNat g₀)
  pr1StrNat g₀ = pr1StrNat' _ _ g₀ _ _ _ _ _ _ _ _ _


record CCatwithpr2 (ccat : CCat) (ccatsig : CCatwithSig ccat) (ccatpr1 : CCatwithpr1 ccat ccatsig) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithSig ccatsig
  open CCatwithpr1 ccatpr1

  field
    pr2Str  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ SigStr Γ A A= B B=) → MorC n (suc n)
    pr2Strₛ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} → is-section (pr2Str Γ A A= B B= u uₛ u₁)
    pr2Str₁ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} → ∂₁ (pr2Str Γ A A= B B= u uₛ u₁) ≡ star (pr1Str Γ A A= B B= u uₛ u₁) B B= pr1Str₁

  pr2Str₀ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} → ∂₀ (pr2Str Γ A A= B B= u uₛ u₁) ≡ Γ
  pr2Str₀ {_} = is-section₀ pr2Strₛ pr2Str₁ ∙ ft-star ∙ pr1Str₀

  field
    pr2StrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (A : Ob (suc m)) (A= : ft A ≡ Γ) (B : Ob (suc (suc m))) (B= : ft B ≡ A) (u : MorC m (suc m)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ SigStr Γ A A= B B=) (g₁ : ∂₁ g ≡ Γ)
                (let u₀ = is-section₀ uₛ u₁ ∙ SigStr=)
             → starTm g (pr2Str Γ A A= B B= u uₛ u₁) pr2Str₀ g₁ ≡ pr2Str Δ (star g A A= g₁)
                                                                           (ft-star ∙ g₀)
                                                                           (star+ g B B= A= g₁)
                                                                           (ft-star ∙ qq₀)
                                                                           (starTm g u u₀ g₁) ssₛ (starTm₁ g SigStr= u uₛ u₁ g₁ ∙ SigStrNat g₀)

  pr2StrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {B : Ob (suc (suc m))} {B= : ft B ≡ A} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=} {g₁ : ∂₁ g ≡ Γ}
                (let u₀ = is-section₀ uₛ u₁ ∙ SigStr=)
             → starTm g (pr2Str Γ A A= B B= u uₛ u₁) pr2Str₀ g₁ ≡ pr2Str Δ (star g A A= g₁)
                                                                           (ft-star ∙ g₀)
                                                                           (star+ g B B= A= g₁)
                                                                           (ft-star ∙ qq₀)
                                                                           (starTm g u u₀ g₁) ssₛ (starTm₁ g SigStr= u uₛ u₁ g₁ ∙ SigStrNat g₀)
  pr2StrNat g₀ = pr2StrNat' _ _ g₀ _ _ _ _ _ _ _ _ _


record CCatwithempty (ccat : CCat) (ccatuu : CCatwithUU ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu

  field
    emptyStr : (i : ℕ) (Γ : Ob n) → MorC n (suc n)
    emptyStrₛ : {i : ℕ} {Γ : Ob n} → is-section (emptyStr i Γ)
    emptyStr₁ : {i : ℕ} {Γ : Ob n} → ∂₁ (emptyStr i Γ) ≡ UUStr i Γ

  emptyStr₀ : {i : ℕ} {Γ : Ob n} → ∂₀ (emptyStr i Γ) ≡ Γ
  emptyStr₀ {_} = is-section₀ emptyStrₛ emptyStr₁ ∙ UUStr=

  field
    emptyStrNat' : {i : ℕ} (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (g₁ : ∂₁ g ≡ Γ)
                 → starTm g (emptyStr i Γ) emptyStr₀ g₁ ≡ emptyStr i Δ

  emptyStrNat : {i : ℕ} {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {g₁ : ∂₁ g ≡ Γ}
              → starTm g (emptyStr i Γ) emptyStr₀ g₁ ≡ emptyStr i Δ
  emptyStrNat g₀ = emptyStrNat' _ _ g₀ _ _


record CCatwithemptyelim (ccat : CCat) (ccatempty : CCatwithEmpty ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithEmpty ccatempty

  field
    emptyelimStr  : (Γ : Ob n) (A : Ob (suc (suc n))) (A= : ft A ≡ EmptyStr Γ) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ EmptyStr Γ) → MorC n (suc n)
    emptyelimStrₛ : {Γ : Ob n} {A : Ob (suc (suc n))} {A= : ft A ≡ EmptyStr Γ} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ EmptyStr Γ} → is-section (emptyelimStr Γ A A= u uₛ u₁)
    emptyelimStr₁ : {Γ : Ob n} {A : Ob (suc (suc n))} {A= : ft A ≡ EmptyStr Γ} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ EmptyStr Γ} → ∂₁ (emptyelimStr Γ A A= u uₛ u₁) ≡ star u A A= u₁

  emptyelimStr₀ : {Γ : Ob n} {A : Ob (suc (suc n))} {A= : ft A ≡ EmptyStr Γ} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ EmptyStr Γ} → ∂₀ (emptyelimStr Γ A A= u uₛ u₁) ≡ Γ
  emptyelimStr₀ {_} {_} {_} {_} {_} {uₛ} {u₁} = is-section₀ emptyelimStrₛ emptyelimStr₁ ∙ ft-star ∙ is-section₀ uₛ u₁ ∙ EmptyStr=

  field
    emptyelimStrNat' : (g : MorC m n) (Δ : Ob m) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob n) (A : Ob (suc (suc n))) (A= : ft A ≡ EmptyStr Γ) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ EmptyStr Γ) (g₁ : ∂₁ g ≡ Γ)
                     → starTm g (emptyelimStr Γ A A= u uₛ u₁) emptyelimStr₀ g₁ ≡ emptyelimStr Δ (star+ g A A= EmptyStr= g₁) (ft-star ∙ qq₀ ∙ EmptyStrNat g₀) (starTm g u (is-section₀ uₛ u₁ ∙ EmptyStr=) g₁) ssₛ (starTm₁ g EmptyStr= u uₛ u₁ g₁ ∙ EmptyStrNat g₀)

  emptyelimStrNat : {g : MorC m n} {Δ : Ob m} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob n} {A : Ob (suc (suc n))} {A= : ft A ≡ EmptyStr Γ} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ EmptyStr Γ} {g₁ : ∂₁ g ≡ Γ}
                   → starTm g (emptyelimStr Γ A A= u uₛ u₁) emptyelimStr₀ g₁ ≡ emptyelimStr Δ (star+ g A A= EmptyStr= g₁) (ft-star ∙ qq₀ ∙ EmptyStrNat g₀) (starTm g u (is-section₀ uₛ u₁ ∙ EmptyStr=) g₁) ssₛ (starTm₁ g EmptyStr= u uₛ u₁ g₁ ∙ EmptyStrNat g₀)
  emptyelimStrNat g₀ = emptyelimStrNat' _ _ g₀ _ _ _ _ _ _ _

record CCatwithunit (ccat : CCat) (ccatuu : CCatwithUU ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu

  field
    unitStr  : (i : ℕ) (Γ : Ob n) → MorC n (suc n)
    unitStrₛ : {i : ℕ} {Γ : Ob n} → is-section (unitStr i Γ)
    unitStr₁ : {i : ℕ} {Γ : Ob n} → ∂₁ (unitStr i Γ) ≡ UUStr i Γ

  unitStr₀ : {i : ℕ} {Γ : Ob n} → ∂₀ (unitStr i Γ) ≡ Γ
  unitStr₀ {_} = is-section₀ unitStrₛ unitStr₁ ∙ UUStr=

  field
    unitStrNat' : {i : ℕ} (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (g₁ : ∂₁ g ≡ Γ)
                 → starTm g (unitStr i Γ) unitStr₀ g₁ ≡ unitStr i Δ

  unitStrNat : {i : ℕ} {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {g₁ : ∂₁ g ≡ Γ}
              → starTm g (unitStr i Γ) unitStr₀ g₁ ≡ unitStr i Δ
  unitStrNat g₀ = unitStrNat' _ _ g₀ _ _

record CCatwithtt (ccat : CCat) (ccatUnit : CCatwithUnit ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithUnit ccatUnit

  field
    ttStr  : (Γ : Ob n) → MorC n (suc n)
    ttStrₛ : {Γ : Ob n} → is-section (ttStr Γ)
    ttStr₁ : {Γ : Ob n} → ∂₁ (ttStr Γ) ≡ UnitStr Γ


  ttStr₀ : {Γ : Ob n} → ∂₀ (ttStr Γ) ≡ Γ
  ttStr₀ {_} = is-section₀ ttStrₛ ttStr₁ ∙ UnitStr=

  field
    ttStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (g₁ : ∂₁ g ≡ Γ)
             → starTm g (ttStr Γ) ttStr₀ g₁ ≡ ttStr Δ

  ttStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {g₁ : ∂₁ g ≡ Γ}
             → starTm g (ttStr Γ) ttStr₀ g₁ ≡ ttStr Δ
  ttStrNat g₀ = ttStrNat' _ _ g₀ _ _

record CCatwithunitelim (ccat : CCat) (ccatUnit : CCatwithUnit ccat) (ccattt : CCatwithtt ccat ccatUnit) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithUnit ccatUnit
  open CCatwithtt ccattt

  field
    unitelimStr  : (Γ : Ob n) (A : Ob (suc (suc n))) (A= : ft A ≡ UnitStr Γ)
                   (dtt : MorC n (suc n)) (dttₛ : is-section dtt) (dtt₁ : ∂₁ dtt ≡ star (ttStr Γ) A A= ttStr₁)
                   (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ UnitStr Γ)
                   → MorC n (suc n)
    unitelimStrₛ : {Γ : Ob n} {A : Ob (suc (suc n))} {A= : ft A ≡ UnitStr Γ}
                   {dtt : MorC n (suc n)} {dttₛ : is-section dtt} {dtt₁ : ∂₁ dtt ≡ star (ttStr Γ) A A= ttStr₁}
                   {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ UnitStr Γ}
                   → is-section (unitelimStr Γ A A= dtt dttₛ dtt₁ u uₛ u₁)
    unitelimStr₁ : {Γ : Ob n} {A : Ob (suc (suc n))} {A= : ft A ≡ UnitStr Γ}
                   {dtt : MorC n (suc n)} {dttₛ : is-section dtt} {dtt₁ : ∂₁ dtt ≡ star (ttStr Γ) A A= ttStr₁}
                   {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ UnitStr Γ}
                   → ∂₁ (unitelimStr Γ A A= dtt dttₛ dtt₁ u uₛ u₁) ≡ star u A A= u₁

  unitelimStr₀ : {Γ : Ob n} {A : Ob (suc (suc n))} {A= : ft A ≡ UnitStr Γ}
                 {dtt : MorC n (suc n)} {dttₛ : is-section dtt} {dtt₁ : ∂₁ dtt ≡ star (ttStr Γ) A A= ttStr₁}
                 {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ UnitStr Γ}
                 → ∂₀ (unitelimStr Γ A A= dtt dttₛ dtt₁ u uₛ u₁) ≡ Γ
  unitelimStr₀ {_} {_} {_} {_} {_} {_} {_} {_} {uₛ} {u₁} = is-section₀ unitelimStrₛ unitelimStr₁ ∙ ft-star ∙ is-section₀ uₛ u₁ ∙ UnitStr=

  field
    unitelimStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (A : Ob (suc (suc m))) (A= : ft A ≡ UnitStr Γ) (dtt : MorC m (suc m)) (dttₛ : is-section dtt) (dtt₁ : ∂₁ dtt ≡ star (ttStr Γ) A A= ttStr₁) (u : MorC m (suc m)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ UnitStr Γ) (g₁ : ∂₁ g ≡ Γ)
                    → starTm g (unitelimStr Γ A A= dtt dttₛ dtt₁ u uₛ u₁) unitelimStr₀ g₁ ≡ unitelimStr Δ (star+ g A A= UnitStr= g₁) (ft-star ∙ qq₀ ∙ UnitStrNat g₀) (starTm g dtt (is-section₀ dttₛ dtt₁ ∙ ft-star ∙ ttStr₀) g₁) ssₛ (starTm₁ g (ft-star ∙ ttStr₀) dtt dttₛ dtt₁ g₁ ∙ starstar UnitStr= ttStrₛ ∙ ap-irr-star (ttStrNat g₀) refl) (starTm g u (is-section₀ uₛ u₁ ∙ UnitStr=) g₁) ssₛ (starTm₁ g UnitStr= u uₛ u₁ g₁ ∙ UnitStrNat g₀)

  unitelimStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc (suc m))} {A= : ft A ≡ UnitStr Γ} {dtt : MorC m (suc m)} {dttₛ : is-section dtt} {dtt₁ : ∂₁ dtt ≡ star (ttStr Γ) A A= ttStr₁} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ UnitStr Γ} {g₁ : ∂₁ g ≡ Γ}
                 → starTm g (unitelimStr Γ A A= dtt dttₛ dtt₁ u uₛ u₁) unitelimStr₀ g₁ ≡ unitelimStr Δ (star+ g A A= UnitStr= g₁) (ft-star ∙ qq₀ ∙ UnitStrNat g₀) (starTm g dtt (is-section₀ dttₛ dtt₁ ∙ ft-star ∙ ttStr₀) g₁) ssₛ (starTm₁ g (ft-star ∙ ttStr₀) dtt dttₛ dtt₁ g₁ ∙ starstar UnitStr= ttStrₛ ∙ ap-irr-star (ttStrNat g₀) refl) (starTm g u (is-section₀ uₛ u₁ ∙ UnitStr=) g₁) ssₛ (starTm₁ g UnitStr= u uₛ u₁ g₁ ∙ UnitStrNat g₀)
  unitelimStrNat g₀ = unitelimStrNat' _ _ g₀ _ _ _ _ _ _ _ _ _ _
  

record CCatwithnat (ccat : CCat) (ccatuu : CCatwithUU ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithUU ccatuu
 
  field
    natStr  : (i : ℕ) (Γ : Ob n) → MorC n (suc n)
    natStrₛ : {i : ℕ} {Γ : Ob n} → is-section (natStr i Γ)
    natStr₁ : {i : ℕ} {Γ : Ob n} → ∂₁ (natStr i Γ) ≡ UUStr i Γ

  natStr₀ : {i : ℕ} {X : Ob n} → ∂₀ (natStr i X) ≡ X
  natStr₀ {_} = is-section₀ natStrₛ natStr₁ ∙ UUStr=

  field
    natStrNat' : {i : ℕ} (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (g₁ : ∂₁ g ≡ Γ)
             → starTm g (natStr i Γ) natStr₀ g₁ ≡ natStr i Δ

  natStrNat : {i : ℕ} {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {g₁ : ∂₁ g ≡ Γ}
             → starTm g (natStr i Γ) natStr₀ g₁ ≡ natStr i Δ
  natStrNat g₀ = natStrNat' _ _ g₀ _ _

record CCatwithzero (ccat : CCat) (ccatnat : CCatwithNat ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithNat ccatnat

  field
    zeroStr  : (Γ : Ob n) → MorC n (suc n)
    zeroStrₛ : {Γ : Ob n} → is-section (zeroStr Γ)
    zeroStr₁ : {Γ : Ob n} → ∂₁ (zeroStr Γ) ≡ NatStr Γ

  zeroStr₀ : {Γ : Ob n} → ∂₀ (zeroStr Γ) ≡ Γ
  zeroStr₀ {_} = is-section₀ zeroStrₛ zeroStr₁ ∙ NatStr=

  field
    zeroStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (g₁ : ∂₁ g ≡ Γ)
             → starTm g (zeroStr Γ) zeroStr₀ g₁ ≡ zeroStr Δ

  zeroStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {g₁ : ∂₁ g ≡ Γ}
             → starTm g (zeroStr Γ) zeroStr₀ g₁ ≡ zeroStr Δ
  zeroStrNat g₀ = zeroStrNat' _ _ g₀ _ _


record CCatwithsuc (ccat : CCat) (ccatnat : CCatwithNat ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithNat ccatnat

  field
    sucStr  : (Γ : Ob n) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ NatStr Γ) → MorC n (suc n)
    sucStrₛ : {Γ : Ob n} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr Γ} → is-section (sucStr Γ u uₛ u₁)
    sucStr₁ : {Γ : Ob n} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr Γ} → ∂₁ (sucStr Γ u uₛ u₁) ≡ NatStr Γ

  sucStr₀ : {Γ : Ob n} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr Γ} → ∂₀ (sucStr Γ u uₛ u₁) ≡ Γ
  sucStr₀ {_} = is-section₀ sucStrₛ sucStr₁ ∙ NatStr=
          

  field
    sucStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (u : MorC m (suc m)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ NatStr Γ) (g₁ : ∂₁ g ≡ Γ) (let u₀ = is-section₀ uₛ u₁ ∙ NatStr=)
             → starTm g (sucStr Γ u uₛ u₁) sucStr₀ g₁ ≡ sucStr Δ (starTm g u u₀ g₁) ssₛ (starTm₁ g NatStr= u uₛ u₁ g₁ ∙ NatStrNat g₀)

  sucStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr Γ} {g₁ : ∂₁ g ≡ Γ} (let u₀ = is-section₀ uₛ u₁ ∙ NatStr=)
             → starTm g (sucStr Γ u uₛ u₁) sucStr₀ g₁ ≡ sucStr Δ (starTm g u u₀ g₁) ssₛ (starTm₁ g NatStr= u uₛ u₁ g₁ ∙ NatStrNat g₀)
  sucStrNat g₀ = sucStrNat' _ _ g₀ _ _ _ _ _

  ap-irr-sucStr : {Γ Γ' : Ob n} (rΓ : Γ ≡ Γ') {u u' : MorC n (suc n)} (ru : u ≡ u') {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr Γ} {uₛ' : is-section u'} {u₁' : ∂₁ u' ≡ NatStr Γ'}
                → sucStr Γ u uₛ u₁ ≡ sucStr Γ' u' uₛ' u₁'
  ap-irr-sucStr refl refl = refl


  T-dS₁ : (Γ : Ob n) (P : Ob (suc (suc n))) (P= : ft P ≡ NatStr Γ) → Ob (suc (suc (suc n)))
  T-dS₁ Γ P P= = star (sucStr P (varC (prev last) P) (varCₛ (prev last) P) (varC+₁ last P= (varCL₁ ∙ NatStrNat pp₀) ∙ NatStrNat pp₀))
                      (star+ (pp P) (star+ (pp (NatStr Γ)) P P= NatStr= (pp₁ ∙ NatStr=)) (ft-star ∙ qq₀) (ft-star ∙ pp₀) (pp₁ ∙ P=))
                      (ft-star ∙ qq₀) (sucStr₁ ∙ ! (NatStrNat (comp₀ {g₀ = pp₀} ∙ pp₀)) ∙ star-comp)


  abstract
    T-dS₁= :  {Γ : Ob n} {P : Ob (suc (suc n))} {P= : ft P ≡ NatStr Γ} → ft (T-dS₁ Γ P P=) ≡ P
    T-dS₁= = ft-star ∙ sucStr₀
          
    ap-irr-T-dS₁ : {Γ Γ' : Ob n} (Γ= : Γ ≡ Γ') {P P' : Ob (suc (suc n))} (P= : P ≡ P') {ftP : ft P ≡ NatStr Γ} {ftP' : ft P' ≡ NatStr Γ'} → T-dS₁ Γ P ftP ≡ T-dS₁ Γ' P' ftP'
    ap-irr-T-dS₁ refl refl  = refl

    T-dS₁Nat : {g : MorC m n} {Δ : Ob m} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob n} {P : Ob (suc (suc n))} {P= : ft P ≡ NatStr Γ} {g₁ : ∂₁ g ≡ Γ} → star++ g (T-dS₁ Γ P P=) T-dS₁= P= NatStr= g₁ ≡ T-dS₁ Δ (star+ g P P= NatStr= g₁) (ft-star ∙ qq₀ ∙ NatStrNat g₀)
    T-dS₁Nat g₀ = starstar (ft-star ∙ pp₀) sucStrₛ ∙ ap-irr-star (sucStrNat qq₀ ∙ ap-irr-sucStr refl star-varC+)
                                                                 (star-qqqqpp' ∙ ap-irr-star (ap-irr-qq refl (ap-irr-star (ap pp (NatStrNat g₀)) (NatStrNat g₀)))
                                                                                             (ap-irr-star (ap-irr-qq (ap pp (NatStrNat g₀)) (NatStrNat g₀)) refl))
                                                       
record CCatwithnatelim (ccat : CCat) (ccatnat : CCatwithNat ccat) (ccatzero : CCatwithzero ccat ccatnat) (ccatsuc : CCatwithsuc ccat ccatnat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithNat ccatnat
  open CCatwithzero ccatzero
  open CCatwithsuc ccatsuc

  field
    natelimStr  : (Γ : Ob n) (P : Ob (suc (suc n))) (P= : ft P ≡ NatStr Γ)
                  (dO : MorC n (suc n)) (dOₛ : is-section dO) (dO₁ : ∂₁ dO ≡ star (zeroStr Γ) P P= zeroStr₁)
                  (dS : MorC (suc (suc n)) (suc (suc (suc n)))) (dSₛ : is-section dS) (dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P=)
                  (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ NatStr Γ)
                  → MorC n (suc n)
    natelimStrₛ : ∀ {Γ P P= dO dOₛ dO₁ dS dSₛ} {dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P=} → ∀ {u uₛ u₁}
                → is-section (natelimStr {n = n} Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)
    natelimStr₁ : ∀ {Γ P P= dO dOₛ dO₁ dS dSₛ} {dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P=} → ∀ {u uₛ u₁}
                → ∂₁ (natelimStr {n = n} Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) ≡ star u P P= u₁
  
  natelimStr₀ : ∀ {Γ P P= dO dOₛ dO₁ dS dSₛ} {dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P=} → ∀ {u uₛ u₁}
                → ∂₀ (natelimStr {n = n} Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) ≡ Γ
  natelimStr₀ {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {uₛ} {u₁} = is-section₀ natelimStrₛ natelimStr₁ ∙ ft-star ∙ is-section₀ uₛ u₁ ∙ NatStr=

  field
    natelimStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (P : Ob (suc (suc m))) (P= : ft P ≡ NatStr Γ) (dO : MorC m (suc m)) (dOₛ : is-section dO) (dO₁ : ∂₁ dO ≡ star (zeroStr Γ) P P= zeroStr₁) (dS : MorC (suc (suc m)) (suc (suc (suc m)))) (dSₛ : is-section dS) (dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P=) (u : MorC m (suc m)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ NatStr Γ) (g₁ : ∂₁ g ≡ Γ)
                    (let dO₀ = is-section₀ dOₛ dO₁ ∙ ft-star ∙ zeroStr₀)
                    (let dS₀ = is-section₀ dSₛ dS₁ ∙ T-dS₁=)
                    (let u₀ = is-section₀ uₛ u₁ ∙ NatStr=)
                    (let nat = NatStrNat g₀)
                  → starTm g (natelimStr {n = m} Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) natelimStr₀ g₁
                  ≡ natelimStr Δ (star+ g P P= NatStr= g₁) (ft-star ∙ qq₀ ∙ nat)
                                 (starTm g dO dO₀ g₁) ssₛ (starTm₁ g (ft-star ∙ zeroStr₀) dO dOₛ dO₁ g₁ ∙ starstar NatStr= zeroStrₛ ∙ ap-irr-star (zeroStrNat g₀ {g₁ = g₁}) refl)
                                 (starTm++ g P= NatStr= dS dS₀ g₁) ssₛ (starTm++₁ g T-dS₁= P= NatStr= dS dSₛ dS₁ g₁ ∙ T-dS₁Nat g₀)
                                 (starTm g u u₀ g₁) ssₛ (starTm₁ g NatStr= u uₛ u₁ g₁ ∙ nat)
                                 
                                   
  abstract 
    natelimStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {P : Ob (suc (suc m))} {P= : ft P ≡ NatStr Γ} {dO : MorC m (suc m)} {dOₛ : is-section dO} {dO₁ : ∂₁ dO ≡ star (zeroStr Γ) P P= zeroStr₁} {dS : MorC (suc (suc m)) (suc (suc (suc m)))} {dSₛ : is-section dS} {dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P=} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr Γ} {g₁ : ∂₁ g ≡ Γ}
                    (let dO₀ = is-section₀ dOₛ dO₁ ∙ ft-star ∙ zeroStr₀)
                    (let dS₀ = is-section₀ dSₛ dS₁ ∙ T-dS₁=)
                    (let u₀ = is-section₀ uₛ u₁ ∙ NatStr=)
                    (let nat = NatStrNat g₀)
                  → starTm g (natelimStr {n = m} Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) natelimStr₀ g₁
                  ≡ natelimStr Δ (star+ g P P= NatStr= g₁) (ft-star ∙ qq₀ ∙ nat)
                                 (starTm g dO dO₀ g₁) ssₛ (starTm₁ g (ft-star ∙ zeroStr₀) dO dOₛ dO₁ g₁ ∙ starstar NatStr= zeroStrₛ ∙ ap-irr-star (zeroStrNat g₀ {g₁ = g₁}) refl)
                                 (starTm++ g P= NatStr= dS dS₀  g₁) ssₛ (starTm++₁ g T-dS₁= P= NatStr= dS dSₛ dS₁ g₁ ∙ T-dS₁Nat g₀)
                                 (starTm g u u₀ g₁) ssₛ (starTm₁ g NatStr= u uₛ u₁ g₁ ∙ nat)
    natelimStrNat {g = g} {Δ} g₀ {Γ} {P} {P=} {dO} {dOₛ} {dO₁} {dS} {dSₛ} {dS₁} {u} {uₛ} {u₁} {g₁} = natelimStrNat' g Δ g₀ Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁ g₁


  Tm-substdS : (Γ : Ob n) (P : Ob (suc (suc n))) (P= : ft P ≡ NatStr Γ) (dO : MorC n (suc n)) (dOₛ : is-section dO) (dO₁ : ∂₁ dO ≡ star (zeroStr Γ) P P= zeroStr₁) (dS : MorC (suc (suc n)) (suc (suc (suc n)))) (dSₛ : is-section dS) (dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P=) (u : MorC n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ NatStr Γ) → MorC n (suc n)
  Tm-substdS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁ =
             starTm (natelimStr Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) (starTm (qq u P P= u₁) dS (is-section₀ dSₛ dS₁ ∙ T-dS₁=) qq₁) (ss₀ ∙ comp₀ ∙ qq₀) natelimStr₁


record CCatwithid (ccat : CCat) (ccatuu : CCatwithUU ccat) (ccatel : CCatwithEl ccat ccatuu) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
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
    idStrNat' : {i : ℕ} (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (a : MorC m (suc m)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ UUStr i Γ) (u : MorC m (suc m)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ ElStr i Γ a aₛ a₁)
                                                (v : MorC m (suc m)) (vₛ : is-section v) (v₁ : ∂₁ v ≡ ElStr i Γ a aₛ a₁) (g₁ : ∂₁ g ≡ Γ)
                                                (let a₀ = is-section₀ aₛ a₁ ∙ UUStr=) (let u₀ = is-section₀ uₛ u₁ ∙ ElStr=) (let v₀ = is-section₀ vₛ v₁ ∙ ElStr= )
             → starTm g (idStr i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) idStr₀ g₁ ≡ idStr i Δ (starTm g a a₀ g₁) ssₛ (starTm₁ g UUStr= a aₛ a₁ g₁ ∙ UUStrNat g₀)
                                                                                  (starTm g u u₀ g₁) ssₛ (starTm₁ g ElStr= u uₛ u₁ g₁ ∙ ElStrNat g₀)
                                                                                  (starTm g v v₀ g₁) ssₛ (starTm₁ g ElStr= v vₛ v₁ g₁ ∙ ElStrNat g₀)

  idStrNat : {i : ℕ} {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i Γ a aₛ a₁}
                                                {v : MorC m (suc m)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i Γ a aₛ a₁} {g₁ : ∂₁ g ≡ Γ}
                                                (let a₀ = is-section₀ aₛ a₁ ∙ UUStr=) (let u₀ = is-section₀ uₛ u₁ ∙ ElStr=) (let v₀ = is-section₀ vₛ v₁ ∙ ElStr= )
             → starTm g (idStr i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) idStr₀ g₁ ≡ idStr i Δ (starTm g a a₀ g₁) ssₛ (starTm₁ g UUStr= a aₛ a₁ g₁ ∙ UUStrNat g₀)
                                                                                  (starTm g u u₀ g₁) ssₛ (starTm₁ g ElStr= u uₛ u₁ g₁ ∙ ElStrNat g₀)
                                                                                  (starTm g v v₀ g₁) ssₛ (starTm₁ g ElStr= v vₛ v₁ g₁ ∙ ElStrNat g₀)
  idStrNat g₀ = idStrNat' _ _ g₀ _ _ _ _ _ _ _ _ _ _ _





record CCatwithrefl {ccat : CCat} (ccatid : CCatwithId ccat) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithId ccatid

  field
    reflStr  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A) → MorC n (suc n)
    reflStrₛ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → is-section (reflStr Γ A A= a aₛ a₁)
    reflStr₁ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} → ∂₁ (reflStr Γ A A= a aₛ a₁) ≡ IdStr Γ A A= a aₛ a₁ a aₛ a₁



  reflStr₀ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ A} → ∂₀ (reflStr Γ A A= u uₛ u₁) ≡ Γ
  reflStr₀ {_} = is-section₀ reflStrₛ reflStr₁ ∙ IdStr=

  field
    reflStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (A : Ob (suc m)) (A= : ft A ≡ Γ) (u : MorC m (suc m)) (uₛ : is-section u) (u₁ : ∂₁ u ≡ A) (g₁ : ∂₁ g ≡ Γ)
                 (let u₀ = is-section₀ uₛ u₁ ∙ A=)
             → starTm g (reflStr Γ A A= u uₛ u₁) reflStr₀ g₁ ≡ reflStr Δ (star g A A= g₁) (ft-star ∙ g₀) (starTm g u u₀ g₁) ssₛ (starTm₁ g A= u uₛ u₁ g₁)
  abstract
    reflStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {u : MorC m (suc m)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ A} {g₁ : ∂₁ g ≡ Γ}
                    (let u₀ = is-section₀ uₛ u₁ ∙ A=)
               → starTm g (reflStr Γ A A= u uₛ u₁) reflStr₀ g₁ ≡ reflStr Δ (star g A A= g₁) (ft-star ∙ g₀) (starTm g u u₀ g₁) ssₛ (starTm₁ g A= u uₛ u₁ g₁)
    reflStrNat g₀ = reflStrNat' _ _ g₀ _ _ _ _ _ _ _
  
    ap-irr-reflStr : {n : ℕ} {Γ Γ' : _} (Γ-eq : Γ ≡ Γ') {A A' : _} (A-eq : A ≡ A') {A= : _} {A=' : _} {a : _} {a' : _} (a-eq : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} → reflStr {n = n} Γ A A= a aₛ a₁ ≡ reflStr {n = n} Γ' A' A=' a' aₛ' a₁'
    ap-irr-reflStr refl refl refl = refl



  T-d₁ : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (P : Ob (suc (suc (suc (suc n))))) (P= : ft P ≡ T-ftP Γ A A=) → Ob (suc (suc n))
  T-d₁ Γ A A= P P= = star (reflStr A wA eq1 (varC last A) (varCₛ last A) varCL₁)
                          (star+ (varC last A)
                                 (star++ (varC last A) wP eq2 eq3 eq4 varCL₁)
                          eq5 eq6 eq7)
                          eq8 eq9
    where
      abstract
        eq1 = ft-star ∙ pp₀
        eq2 = ft-star ∙ qq₀
        eq3 = ft-star ∙ qq₀
        eq4 = ft-star ∙ qq₀
        eq5 = ft-star ∙ qq₀
        eq6 = ft-star ∙ qq₀
        eq7 = varCL₁ ∙ ! star-varCL-star-qqpp
        eq8 = ft-star ∙ qq₀
        eq9 = reflStr₁ ∙ ! (ap-irr-star refl (! star-comp ∙ ap-irr-star (! (qq-comp {g₀ = qq₀}) ∙ ap-irr-qq (ap-irr-comp (ap-irr-qq (! (id-left pp₀)) refl) refl ∙ ! ss-qq) refl {q' = ft-star ∙ pp₀} ∙ qq-id) refl {q' = T-ftP=} ∙ star-id) ∙ IdStrNat (varC₀ {k = last}) {g₁ = varCL₁} ∙
                           ap-irr-IdStr refl (! star-comp ∙ ap-irr-star (is-section= (ft-star ∙ pp₀) (varCₛ last _) varCL₁ ) refl {q' = ft-star ∙ pp₀}∙ star-id)
                                             (star-varCL'' ∙ ap ss (is-section= (ft-star ∙ pp₀) (varCₛ last _) varCL₁))
                                             (star-varCL' ∙ ss-of-section _ (varCₛ last _)))
        eq10 = ft-star ∙ pp₀
       -- eq11 = ft-star ∙ pp₀
        eq12 = ft-star ∙ pp₀
 
      wA = star (pp A) A A= (pp₁ ∙ A=)
      wwA = star+ (pp A) wA eq10 A= (pp₁ ∙ A=)
      -- widA = star++ (pp A) (T-ftP Γ A A=) T-ftP= eq11 A= (pp₁ ∙ A=)
      wP = star+++ (pp A) P {X' = T-ftP Γ A A=} P= {X'' = wA} T-ftP= {X''' = A} eq12 {X'''' = Γ} A= (pp₁ ∙ A=)

  abstract
  
    ap-irr-T-d₁ : {Γ Γ' : Ob n} (Γ= : Γ ≡ Γ') {A A' : Ob (suc n)} (A= : A ≡ A') {ftA : ft A ≡ Γ} {ftA' : ft A' ≡ Γ'} {P P' : Ob (suc (suc (suc (suc n))))} (P= : P ≡ P') {ftP : ft P ≡ T-ftP Γ A ftA} {ftP' : ft P' ≡ T-ftP Γ' A' ftA'} → T-d₁ Γ A ftA P ftP ≡ T-d₁ Γ' A' ftA' P' ftP'
    ap-irr-T-d₁ refl refl refl = refl
    
    T-d₁= : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {P : Ob (suc (suc (suc (suc n))))} {P= : ft P ≡ T-ftP Γ A A=} → ft (T-d₁ Γ A A= P P=) ≡ A
    T-d₁= = ft-star ∙ reflStr₀

    T-d₁Nat : {g : MorC m n} {Δ : Ob m} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {P : Ob (suc (suc (suc (suc n))))} {P= : ft P ≡ T-ftP Γ A A=}   {g₁ : ∂₁ g ≡ Γ} → star+ g (T-d₁ Γ A A= P P=) T-d₁= A= g₁ ≡ T-d₁ Δ (star g A A= g₁) (ft-star ∙ g₀) (star+++ g P P= T-ftP= (ft-star ∙ pp₀) A= g₁) (ft-star ∙ qq₀ ∙ T-ftPNat g₀)
    T-d₁Nat g₀ = starstar (ft-star ∙ varC₀ {k = last}) reflStrₛ ∙
                 ap-irr-star (reflStrNat qq₀ ∙ ap-irr-reflStr refl (star-pp g₀) star-varCL)
                             (starstar+ (ft-star ∙ varC₀ {k = last}) (varCₛ last _) ∙
                             ap-irr-star (ap-irr-qq star-varCL (starstar+ (ft-star ∙ pp₀) (varCₛ last _)
                                                               ∙ ap-irr-star (ap-irr-qq star-varCL (star-qqpp g₀ ∙ ap-irr-star refl (star-pp g₀)))
                                                                             (star-qqqqpp g₀ ∙ ap-irr-star (ap-irr-qq refl (star-pp g₀)) (T-ftPNat g₀))))
                                         (starstar++ (ft-star ∙ pp₀) (varCₛ last _)
                                          ∙ ap-irr-star (ap-irr-qq (ap-irr-qq star-varCL (star-qqpp g₀ ∙ ap-irr-star refl (star-pp g₀)))
                                                                   (star-qqqqpp g₀ ∙ ap-irr-star (ap-irr-qq refl (star-pp g₀)) (T-ftPNat g₀)))
                                                        (star-qqqqqqpp g₀ ∙ ap-irr-star (ap-irr-qq (ap-irr-qq refl (star-pp g₀)) (T-ftPNat g₀)) refl)))




record CCatwithjj (ccat : CCat) (ccatId : CCatwithId ccat) (ccatrefl : CCatwithrefl ccatId) : Set₁ where
  no-eta-equality
  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithId ccatId
  open CCatwithrefl ccatrefl

  field
    jjStr  : (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (P : Ob (suc (suc (suc (suc n))))) (P= : ft P ≡ T-ftP Γ A A=)
             (d : MorC (suc n) (suc (suc n))) (dₛ : is-section d) (d₁ : ∂₁ d ≡ T-d₁ Γ A A= P P=)
             (a : MorC n (suc n)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A)
             (b : MorC n (suc n)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ A)
             (p : MorC n (suc n)) (pₛ : is-section p) (p₁ : ∂₁ p ≡ IdStr Γ A A= a aₛ a₁ b bₛ b₁)
             → MorC n (suc n)
    jjStrₛ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {P : Ob (suc (suc (suc (suc n))))} {P= : ft P ≡ T-ftP Γ A A=}
             {d : MorC (suc n) (suc (suc n))} {dₛ : is-section d} {d₁ : ∂₁ d ≡ T-d₁ Γ A A= P P=}
             {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A}
             {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A}
             {p : MorC n (suc n)} {pₛ : is-section p} {p₁ : ∂₁ p ≡ IdStr Γ A A= a aₛ a₁ b bₛ b₁}
           → is-section (jjStr {n = n} Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁)
    jjStr₁ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {P : Ob (suc (suc (suc (suc n))))} {P= : ft P ≡ T-ftP Γ A A=}
             {d : MorC (suc n) (suc (suc n))} {dₛ : is-section d} {d₁ : ∂₁ d ≡ T-d₁ Γ A A= P P=}
             {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A}
             {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A}
             {p : MorC n (suc n)} {pₛ : is-section p} {p₁ : ∂₁ p ≡ IdStr Γ A A= a aₛ a₁ b bₛ b₁}             
           → ∂₁ (jjStr Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁)
             ≡ T-jjStr₁ Γ A A= P P= a aₛ a₁ b bₛ b₁ p pₛ p₁

  jjStr₀ : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {P : Ob (suc (suc (suc (suc n))))} {P= : ft P ≡ T-ftP Γ A A=}
             {d : MorC (suc n) (suc (suc n))} {dₛ : is-section d} {d₁ : ∂₁ d ≡ T-d₁ Γ A A= P P=}
             {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A}
             {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A}
             {p : MorC n (suc n)} {pₛ : is-section p} {p₁ : ∂₁ p ≡ IdStr Γ A A= a aₛ a₁ b bₛ b₁}
         → ∂₀ (jjStr {n = n} Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁) ≡ Γ
  jjStr₀ {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {pₛ} {p₁} = is-section₀ jjStrₛ jjStr₁ ∙ ft-star ∙ is-section₀ pₛ p₁ ∙ IdStr=

  field
    jjStrNat' : (g : MorC n m) (Δ : Ob n) (g₀ : ∂₀ g ≡ Δ) (Γ : Ob m) (A : Ob (suc m)) (A= : ft A ≡ Γ) (P : Ob (suc (suc (suc (suc m))))) (P= : ft P ≡ T-ftP Γ A A=)
                (d : MorC (suc m) (suc (suc m))) (dₛ : is-section d) (d₁ : ∂₁ d ≡ T-d₁ Γ A A= P P=)
                (a : MorC m (suc m)) (aₛ : is-section a) (a₁ : ∂₁ a ≡ A)
                (b : MorC m (suc m)) (bₛ : is-section b) (b₁ : ∂₁ b ≡ A)
                (p : MorC m (suc m)) (pₛ : is-section p) (p₁ : ∂₁ p ≡ IdStr Γ A A= a aₛ a₁ b bₛ b₁) (g₁ : ∂₁ g ≡ Γ)
                (let d₀ = is-section₀ dₛ d₁ ∙ T-d₁=) (let a₀ = is-section₀ aₛ a₁ ∙ A=) (let b₀ = is-section₀ bₛ b₁ ∙ A=) (let p₀ = is-section₀ pₛ p₁ ∙ IdStr=) →
                starTm g (jjStr Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁) jjStr₀ g₁ ≡ jjStr Δ (star g A A= g₁) (ft-star ∙ g₀)
                                                                                                 (star+++ g P P= T-ftP= (ft-star ∙ pp₀) A= g₁) (ft-star ∙ qq₀ ∙ T-ftPNat g₀)
                                                                                                 (starTm+ g A= d d₀ g₁) ssₛ (starTm+₁ g T-d₁= A= d dₛ d₁ g₁ ∙ T-d₁Nat g₀)
                                                                                                 (starTm g a a₀ g₁) ssₛ (starTm₁ g A= a aₛ a₁ g₁)
                                                                                                 (starTm g b b₀ g₁) ssₛ (starTm₁ g A= b bₛ b₁ g₁)
                                                                                                 (starTm g p p₀ g₁) ssₛ (starTm₁ g IdStr= p pₛ p₁ g₁ ∙ IdStrNat g₀)

  abstract 
    jjStrNat : {g : MorC n m} {Δ : Ob n} (g₀ : ∂₀ g ≡ Δ) {Γ : Ob m} {A : Ob (suc m)} {A= : ft A ≡ Γ} {P : Ob (suc (suc (suc (suc m))))} {P= : ft P ≡ T-ftP Γ A A=}
               {d : MorC (suc m) (suc (suc m))} {dₛ : is-section d} {d₁ : ∂₁ d ≡ T-d₁ Γ A A= P P=}
               {a : MorC m (suc m)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A}
               {b : MorC m (suc m)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ A}
               {p : MorC m (suc m)} {pₛ : is-section p} {p₁ : ∂₁ p ≡ IdStr Γ A A= a aₛ a₁ b bₛ b₁} {g₁ : ∂₁ g ≡ Γ}
               (let d₀ = is-section₀ dₛ d₁ ∙ T-d₁=) (let a₀ = is-section₀ aₛ a₁ ∙ A=) (let b₀ = is-section₀ bₛ b₁ ∙ A=) (let p₀ = is-section₀ pₛ p₁ ∙ IdStr=) →
               starTm g (jjStr Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁) jjStr₀ g₁ ≡ jjStr Δ (star g A A= g₁) (ft-star ∙ g₀)
                                                                                                (star+++ g P P= T-ftP= (ft-star ∙ pp₀) A= g₁) (ft-star ∙ qq₀ ∙ T-ftPNat g₀)
                                                                                                (starTm+ g A= d d₀ g₁) ssₛ (starTm+₁ g T-d₁= A= d dₛ d₁ g₁ ∙ T-d₁Nat g₀) 
                                                                                                (starTm g a a₀ g₁) ssₛ (starTm₁ g A= a aₛ a₁ g₁)
                                                                                                (starTm g b b₀ g₁) ssₛ (starTm₁ g A= b bₛ b₁ g₁)
                                                                                                (starTm g p p₀ g₁) ssₛ (starTm₁ g IdStr= p pₛ p₁ g₁ ∙ IdStrNat g₀)
    jjStrNat {g = g} {Δ} g₀ {Γ} {A} {A=} {P} {P=} {d} {dₛ} {d₁} {a} {aₛ} {a₁} {b} {bₛ} {b₁} {p} {pₛ} {p₁} {g₁} = jjStrNat' g Δ g₀ Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁ g₁
                

T-lhsEtaPi : {ccat : CCat} (ccatPi : CCatwithPi ccat) (ccatlam : CCatwithlam ccat ccatPi) (ccatapp : CCatwithapp ccat ccatPi) (let open CCat+ ccat) (let open CCatwithPi ccatPi)
           (Γ : Ob n) (A : Ob (suc n)) (A= : ft A ≡ Γ) (B : Ob (suc (suc n))) (B= : ft B ≡ A) (f : Mor n (suc n)) (fₛ : is-section f) (f₁ : ∂₁ f ≡ PiStr Γ A A= B B=) → Mor n (suc n)
T-lhsEtaPi {ccat = ccat} ccatPi ccatlam ccatapp Γ A A= B B= f fₛ f₁ =
  let open CCat+ ccat
      open CCatwithPi ccatPi
      open CCatwithlam ccatlam
      open CCatwithapp ccatapp
  in
  lamStr Γ A A= B B= (appStr A (star (pp A) A A= (pp₁ ∙ A=)) (ft-star ∙ pp₀)
                               (star (qq (pp A) A A= (pp₁ ∙ A=)) B B= qq₁) (ft-star ∙ qq₀)
                               (starTm (pp A) f (is-section₀ fₛ f₁ ∙ PiStr=) (pp₁ ∙ A=)) ssₛ (starTm₁ (pp A) PiStr= f fₛ f₁ (pp₁ ∙ A=) ∙ PiStrNat pp₀)
                               (varC last A) (varCₛ last A) varCL₁)
                     appStrₛ
                     (appStr₁ ∙ star-varCL-star-qqpp)


record StructuredCCat : Set₁ where
  no-eta-equality
  field
    ccat : CCat
    ccatUU : CCatwithUU ccat
    ccatEl : CCatwithEl ccat ccatUU
    ccatPi : CCatwithPi ccat
    ccatSig : CCatwithSig ccat
    ccatEmpty : CCatwithEmpty ccat
    ccatUnit : CCatwithUnit ccat
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
    ccatempty : CCatwithempty ccat ccatUU
    ccatemptyelim : CCatwithemptyelim ccat ccatEmpty
    ccatunit : CCatwithunit ccat ccatUU
    ccattt : CCatwithtt ccat ccatUnit
    ccatunitelim : CCatwithunitelim ccat ccatUnit ccattt
    ccatnat : CCatwithnat ccat ccatUU
    ccatzero : CCatwithzero ccat ccatNat
    ccatsuc : CCatwithsuc ccat ccatNat 
    ccatnatelim : CCatwithnatelim ccat ccatNat ccatzero ccatsuc
    ccatid : CCatwithid ccat ccatUU ccatEl
    ccatrefl : CCatwithrefl ccatId
    ccatjj : CCatwithjj ccat ccatId ccatrefl

  open CCat+ ccat renaming (Mor to MorC)
  open CCatwithUU ccatUU public
  open CCatwithEl ccatEl public
  open CCatwithPi ccatPi public
  open CCatwithSig ccatSig public
  open CCatwithEmpty ccatEmpty public
  open CCatwithUnit ccatUnit public
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
  open CCatwithempty ccatempty public
  open CCatwithemptyelim ccatemptyelim public
  open CCatwithunit ccatunit public
  open CCatwithtt ccattt public
  open CCatwithunitelim ccatunitelim public
  open CCatwithnat ccatnat public
  open CCatwithzero ccatzero public
  open CCatwithsuc ccatsuc public
  open CCatwithnatelim ccatnatelim public
  open CCatwithid ccatid public
  open CCatwithrefl ccatrefl public
  open CCatwithjj ccatjj public

  field
    {- Additional structure corresponding to equality rules -}
    betaPiStr : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC (suc n) (suc (suc n))} {uₛ : is-section u} {u₁ : ∂₁ u ≡ B} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A}
            → appStr Γ A A= B B= (lamStr Γ A A= B B= u uₛ u₁) lamStrₛ lamStr₁ a aₛ a₁ ≡ starTm a u (is-section₀ uₛ u₁ ∙ B=) a₁
    betaSig1Str : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B B= a₁} → pr1Str Γ A A= B B= (pairStr Γ A A= B B= a aₛ a₁ b bₛ b₁) pairStrₛ pairStr₁ ≡ a
    betaSig2Str : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A} {b : MorC n (suc n)} {bₛ : is-section b} {b₁ : ∂₁ b ≡ star a B B= a₁} → pr2Str Γ A A= B B= (pairStr Γ A A= B B= a aₛ a₁ b bₛ b₁) pairStrₛ pairStr₁ ≡ b

    betaUnitStr : {Γ : Ob n} {A : Ob (suc (suc n))} {A= : ft A ≡ UnitStr Γ} {dtt : MorC n (suc n)} {dttₛ : is-section dtt} {dtt₁ : ∂₁ dtt ≡ star (ttStr Γ) A A= ttStr₁}
                → unitelimStr Γ A A= dtt dttₛ dtt₁ (ttStr Γ) ttStrₛ ttStr₁ ≡ dtt

    betaNatZeroStr : {Γ : Ob n} {P : Ob (suc (suc n))} {P= : ft P ≡ NatStr Γ}
                     {dO : MorC n (suc n)} {dOₛ : is-section dO} {dO₁ : ∂₁ dO ≡ star (zeroStr Γ) P P= zeroStr₁}
                     {dS : MorC (suc (suc n)) (suc (suc (suc n)))} {dSₛ : is-section dS} {dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P=}
                   → natelimStr Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ (zeroStr Γ) zeroStrₛ zeroStr₁ ≡ dO
    betaNatSucStr : {Γ : Ob n} {P : Ob (suc (suc n))} {P= : ft P ≡ NatStr Γ}
                    {dO : MorC n (suc n)} {dOₛ : is-section dO} {dO₁ : ∂₁ dO ≡ star (zeroStr Γ) P P= zeroStr₁}
                    {dS : MorC (suc (suc n)) (suc (suc (suc n)))} {dSₛ : is-section dS} {dS₁ : ∂₁ dS ≡ T-dS₁ Γ P P=}
                    {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ NatStr Γ}
                  → natelimStr Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ (sucStr Γ u uₛ u₁) sucStrₛ sucStr₁ ≡ Tm-substdS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁

    betaIdStr : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {P : Ob (suc (suc (suc (suc n))))} {P= : ft P ≡ T-ftP Γ A A=}
                {d : MorC (suc n) (suc (suc n))} {dₛ : is-section d} {d₁ : ∂₁ d ≡ T-d₁ Γ A A= P P=}
                {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ A}
              → jjStr Γ A A= P P= d dₛ d₁ a aₛ a₁ a aₛ a₁ (reflStr Γ A A= a aₛ a₁) reflStrₛ reflStr₁ ≡ starTm a d (is-section₀ dₛ d₁ ∙ T-d₁=) a₁

    etaPiStr : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {f : MorC n (suc n)} {fₛ : is-section f} {f₁ : ∂₁ f ≡ PiStr Γ A A= B B=}
             → f ≡ T-lhsEtaPi ccatPi ccatlam ccatapp Γ A A= B B= f fₛ f₁
    etaSigStr : {Γ : Ob n} {A : Ob (suc n)} {A= : ft A ≡ Γ} {B : Ob (suc (suc n))} {B= : ft B ≡ A} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ SigStr Γ A A= B B=}
             → u ≡ pairStr Γ A A= B B= (pr1Str Γ A A= B B= u uₛ u₁) pr1Strₛ pr1Str₁ (pr2Str Γ A A= B B= u uₛ u₁) pr2Strₛ pr2Str₁

    eluuStr : {i : ℕ} {Γ : Ob n} → ElStr (suc i) Γ (uuStr i Γ) uuStrₛ uuStr₁ ≡ UUStr i Γ
    elpiStr : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)} 
            → ElStr i Γ (piStr i Γ a aₛ a₁ b bₛ b₁) piStrₛ piStr₁ ≡ PiStr Γ (ElStr i Γ a aₛ a₁) ElStr= (ElStr i (ElStr i Γ a aₛ a₁) b bₛ b₁) ElStr=
    elsigStr : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {b : MorC (suc n) (suc (suc n))} {bₛ : is-section b} {b₁ : ∂₁ b ≡ UUStr i (ElStr i Γ a aₛ a₁)}
            → ElStr i Γ (sigStr i Γ a aₛ a₁ b bₛ b₁) sigStrₛ sigStr₁ ≡ SigStr Γ (ElStr i Γ a aₛ a₁) ElStr= (ElStr i (ElStr i Γ a aₛ a₁) b bₛ b₁) ElStr=
    elemptyStr : {i : ℕ} {Γ : Ob n} → ElStr i Γ (emptyStr i Γ) emptyStrₛ emptyStr₁ ≡ EmptyStr Γ
    elunitStr : {i : ℕ} {Γ : Ob n} → ElStr i Γ (unitStr i Γ) unitStrₛ unitStr₁ ≡ UnitStr Γ
    elnatStr : {i : ℕ} {Γ : Ob n} → ElStr i Γ (natStr i Γ) natStrₛ natStr₁ ≡ NatStr Γ
    elidStr : {i : ℕ} {Γ : Ob n} {a : MorC n (suc n)} {aₛ : is-section a} {a₁ : ∂₁ a ≡ UUStr i Γ} {u : MorC n (suc n)} {uₛ : is-section u} {u₁ : ∂₁ u ≡ ElStr i Γ a aₛ a₁}
                      {v : MorC n (suc n)} {vₛ : is-section v} {v₁ : ∂₁ v ≡ ElStr i Γ a aₛ a₁} → ElStr i Γ (idStr i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) idStrₛ idStr₁ ≡ IdStr Γ (ElStr i Γ a aₛ a₁) ElStr= u uₛ u₁ v vₛ v₁
