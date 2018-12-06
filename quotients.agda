{-# OPTIONS --rewriting --prop --without-K #-}

open import common

{- PathOver -}

-- This is the proof-irrelevant PathOver, over a relevant equality. Using irrelevant equality for
-- [p] makes it impossible to define [PathOver-refl-from] without K.
data PathOver {l l'} {A : Set l} (B : A → Set l') {a : A} : {a' : A} (p : a ≡R a') → B a → B a' → Prop (l ⊔ l') where
  reflo : {u : B a} → PathOver B reflR u u

{- Equivalence relations -}

record EquivRel (A : Set) : Set₁ where
  field
    _≃_ : A → A → Prop
    ref : (a : A) → a ≃ a
    sym : {a b : A} → a ≃ b → b ≃ a
    tra : {a b c : A} → a ≃ b → b ≃ c → a ≃ c
open EquivRel {{…}} public

{- Quotients -}

postulate
  _//_ : (A : Set) (R : EquivRel A) → Set

module _ {A : Set} {R : EquivRel A} where

  instance
    _ = R

  postulate
    {- Introduction rules -}

    proj : A → A // R
    eqR : {a b : A} (r : a ≃ b) → proj a ≡R proj b

    {- Dependent elimination rule -}

    //-elim : ∀ {l} {B : A // R → Set l} (proj* : (a : A) → B (proj a)) (eq* : {a b : A} (r : a ≃ b) → PathOver B (eqR r) (proj* a) (proj* b))
            → (x : A // R) → B x

    {- Reduction rule -}

    //-beta : ∀ {l} {B : A // R → Set l} {proj* : (a : A) → B (proj a)} {eq* : {a b : A} (r : a ≃ b) → PathOver B (eqR r) (proj* a) (proj* b)} {a : A}
            → //-elim proj* eq* (proj a) ↦ proj* a
    {-# REWRITE //-beta #-}

  eq : {a b : A} (r : a ≃ b) → proj a ≡ proj b
  eq r = squash≡ (eqR r)


{- Lemmas about PathOver -}

PathOver-refl-to : ∀ {l l'} {A : Set l} {B : A → Set l'} {a : A} {u u' : B a}
                 → u ≡ u'
                 → PathOver B reflR u u'
PathOver-refl-to refl = reflo

PathOver-refl-from : ∀ {l l'} {A : Set l} {B : A → Set l'} {a : A} {u u' : B a}
                 → PathOver B reflR u u'
                 → u ≡ u'
PathOver-refl-from reflo = refl

PathOver-Box : ∀ {l l'} {A : Set l} (B : A → Prop l') {a a' : A} (p : a ≡R a') (u : Box (B a)) (u' : Box (B a')) → PathOver (λ x → Box (B x)) p u u'
PathOver-Box B reflR u u' = reflo

PathOver-Cst : ∀ {l l'} {A : Set l} (B : Set l') {a a' : A} (p : a ≡R a') {u v : B}
             → u ≡ v → PathOver (λ _ → B) p u v
PathOver-Cst B reflR refl = reflo

PathOver-Prop→ : ∀ {l l' l''} {A : Set l} {B : A → Prop l'} {C : A → Set l''}
                  {a a' : A} {p : a ≡R a'} {u : B a → C a} {u' : B a' → C a'}
                  → ((y : B a) (y' : B a') → PathOver C p (u y) (u' y'))
                  → PathOver (λ x → (B x → C x)) p u u'
PathOver-Prop→ {p = reflR} f = PathOver-refl-to (funextP λ x → PathOver-refl-from (f x x))

PathOver-Prop→Cst : ∀ {l l' l''} {A : Set l} {B : A → Prop l'} {C : Set l''}
                  {a a' : A} {p : a ≡R a'} {u : B a → C} {u' : B a' → C}
                  → ((y : B a) (y' : B a') → u y ≡ u' y')
                  → PathOver (λ x → (B x → C)) p u u'
PathOver-Prop→Cst {p = reflR} f = PathOver-refl-to (funextP λ x → f x x)

PathOver-CstPi : ∀ {l l' l''} {A : Set l} {B : Set l'} {C : A → B → Set l''}
                  {a a' : A} {p : a ≡R a'} {u : (b : B) → C a b} {u' : (b : B) → C a' b}
                  → ((y : B) → PathOver (λ x → C x y) p (u y) (u' y))
                  → PathOver (λ x → ((y : B) → C x y)) p u u'
PathOver-CstPi {p = reflR} f = PathOver-refl-to (funext (λ y → PathOver-refl-from (f y)))

PathOver-CstPropPi : ∀ {l l' l''} {A : Set l} {B : Prop l'} {C : A → B → Set l''}
                  {a a' : A} {p : a ≡R a'} {u : (b : B) → C a b} {u' : (b : B) → C a' b}
                  → ((y : B) → PathOver (λ x → C x y) p (u y) (u' y))
                  → PathOver (λ x → ((y : B) → C x y)) p u u'
PathOver-CstPropPi {p = reflR} f = PathOver-refl-to (funextP (λ y → PathOver-refl-from (f y)))

PathOver-→ : ∀ {l l' l''} {A : Set l} {B : A → Set l'} {C : A → Set l''}
                  {a a' : A} {p : a ≡R a'} {u : B a → C a} {u' : B a' → C a'}
                  → ((y : B a) (y' : B a') (r : PathOver B p y y') → PathOver C p (u y) (u' y'))
                  → PathOver (λ x → (B x → C x)) p u u'
PathOver-→ {p = reflR} f = PathOver-refl-to (funext λ x → PathOver-refl-from (f x x reflo))

PathOver-→Cst : ∀ {l l' l''} {A : Set l} {B : A → Set l'} {C : Set l''}
                  {a a' : A} {p : a ≡R a'} {u : B a → C} {u' : B a' → C}
                  → ((y : B a) (y' : B a') (r : PathOver B p y y') → u y ≡ u' y')
                  → PathOver (λ x → (B x → C)) p u u'
PathOver-→Cst {p = reflR} f = PathOver-refl-to (funext (λ x → f x x reflo))

record ΣP {l l'} (A : Set l) (B : A → Prop l') : Set (l ⊔ l') where
  constructor _,_
  field
    fst : A
    snd : B fst
open ΣP public

uncurry : ∀ {l l' l''} {A : Set l} {B : A → Prop l'} (C : (a : A) → B a → Set l'') → ΣP A B → Set l''
uncurry C ab = C (fst ab) (snd ab)

pair≡P : ∀ {l l'} {A : Set l} {B : A → Prop l'} {a a' : A} (p : a ≡R a') {b : B a} {b' : B a'} → _≡R_ {A = ΣP A B} (a , b) (a' , b')
pair≡P reflR = reflR

-- postulate
--   pair≡R : ∀ {l l'} {A : Set l} {B : A → Set l'} {a a' : A} (p : a ≡R a') {b : B a} {b' : B a'} (q : PathOver B p b b') → _≡R_ {A = ΣP A B} (a , b) (a' , b')
--   pair≡R-rew : ∀ {l l'} {A : Set l} {B : A → Set l'} {a : A} {b : B a} → pair≡R (reflR {a = a}) (reflo {B = B} {u = b}) ↦ reflR
-- {-# REWRITE pair≡R-rew #-}

-- PathOver-Pi : ∀ {l l' l''} {A : Set l} {B : A → Set l'} {C : (a : A) → B a → Set l''}
--                   {a a' : A} {p : a ≡R a'} {u : (b : B a) → C a b} {u' : (b' : B a') → C a' b'}
--                   → ((y : B a) (y' : B a') (r : PathOver B p y y') → PathOver (uncurry C) (pair≡R p r) (u y) (u' y'))
--                   → PathOver (λ x → ((y : B x) → C x y)) p u u'
-- PathOver-Pi {p = reflR} f = PathOver-refl-to (funext (λ x → PathOver-refl-from (f x x reflo)))

PathOver-PropPi : ∀ {l l' l''} {A : Set l} {B : A → Prop l'} {C : (a : A) → B a → Set l''}
                  {a a' : A} {p : a ≡R a'} {u : (b : B a) → C a b} {u' : (b' : B a') → C a' b'}
                  → ((y : B a) (y' : B a') → PathOver (uncurry C) (pair≡P p) (u y) (u' y'))
                  → PathOver (λ x → ((y : B x) → C x y)) p u u'
PathOver-PropPi {p = reflR} f = PathOver-refl-to (funextP (λ x → PathOver-refl-from (f x x)))


{- Elimination rules that we actually use (most of the time) -}

module _ {A : Set} {R : EquivRel A} where

  private
   instance
    _ = R

  -- Non-dependent elimination
  //-rec : ∀ {l} {B : Set l} (proj* : A → B) (eq* : {a b : A} (r : a ≃ b) → proj* a ≡ proj* b) → A // R → B
  //-rec proj* eq* = //-elim proj* λ r → PathOver-Cst _ (eqR r) (eq* r)

  -- Dependent elimination into a Prop
  //-elimP : ∀ {l} {B : A // R → Prop l} (proj* : (a : A) → B (proj a)) → (x : A // R) → B x
  //-elimP {B = B} proj* x = unbox (//-elim {B = λ x → Box (B x)} (λ a → box (proj* a)) (λ r → PathOver-Box (λ z → B z) (eqR r) (box (proj* _)) (box (proj* _))) x)

  -- Dependent elimination in a dependent type of the form x.((y : B) → C x y) with B a Set
  //-elim-PiS : ∀ {l l'} {B : Set l} {C : A // R → B → Set l'} (proj* : (a : A) (b : B) → C (proj a) b) (eq* : {a b : A} (r : a ≃ b) (y : B) → PathOver (λ x → C x y) (eqR r) (proj* a y) (proj* b y)) → (x : A // R) → (y : B) → C x y
  //-elim-PiS proj* eq* = //-elim proj* (λ r → PathOver-CstPi (eq* r))

  -- Dependent elimination in a dependent type of the form x.(B x → C) with B a Prop
  //-elim-PiP : ∀ {l l'} {B : A // R → Prop l} {C : Set l'} (proj* : (a : A) (b : B (proj a)) → C) (eq* : {a a' : A} (r : a ≃ a') (y : B (proj a)) (y' : B (proj a')) → proj* a y ≡ proj* a' y') → (x : A // R) → (y : B x) → C
  //-elim-PiP proj* eq* = //-elim proj* (λ r → PathOver-Prop→Cst (eq* r))

  -- Dependent elimination in a dependent type of the form x.(B x → C x) with B a Prop
  //-elim-PiP2 : ∀ {l l'} {B : A // R → Prop l} {C : A // R → Set l'} (proj* : (a : A) (b : B (proj a)) → C (proj a)) (eq* : {a a' : A} (r : a ≃ a') (y : B (proj a)) (y' : B (proj a')) → PathOver C (eqR r) (proj* a y) (proj* a' y')) → (x : A // R) → (y : B x) → C x
  //-elim-PiP2 proj* eq* = //-elim proj* (λ r → PathOver-Prop→ (eq* r))

  -- Dependent elimination in a dependent type of the form x.((y : B x) → C x y) with B a Prop
  //-elim-PiP3 : ∀ {l l'} {B : A // R → Prop l} {C : (x : A // R) → B x → Set l'} (proj* : (a : A) (b : B (proj a)) → C (proj a) b) (eq* : {a a' : A} (r : a ≃ a') (y : B (proj a)) (y' : B (proj a')) → PathOver (uncurry C) (pair≡P (eqR r)) (proj* a y) (proj* a' y')) → (x : A // R) → (y : B x) → C x y
  //-elim-PiP3 proj* eq* = //-elim proj* (λ r → PathOver-PropPi (eq* r))

  -- Not sure
  //-elimP-PiP : ∀ {l l'} {X : Set l} {B : A // R → X → Prop l} {x₀ x₁ : X} {p : x₀ ≡R x₁} {C : Set l'} {u : (x : A // R) → B x x₀ → C} {v : (x : A // R) → B x x₁ → C}
                 (proj* : (a : A) (y : B (proj a) x₀) (y' : B (proj a) x₁) → u (proj a) y ≡ v (proj a) y')
                 → (x : A // R) → PathOver (λ y → (B x y → C)) p (u x) (v x)
  //-elimP-PiP proj* = //-elimP (λ a → PathOver-Prop→Cst (proj* a))

{- Effectiveness of quotients, this uses propositional extensionality -}

module _ {A : Set} {R : EquivRel A} where

  private
    instance
      _ = R

    -- The "Codes" fibration
    _≃'_ : (a : A) (c : A // R) → Prop
    _≃'_ a = //-rec (λ b → a ≃ b) (λ r → prop-ext (λ z → tra {A = A} z r) (λ z → tra {A = A} z (sym {A = A} r)))

    reflect' : {a : A} (c : A // R) → proj a ≡ c → a ≃' c
    reflect' {a} c refl = ref a

  reflect : {a b : A} → proj a ≡ proj b → a ≃ b
  reflect {b = b} p = reflect' (proj b) p
