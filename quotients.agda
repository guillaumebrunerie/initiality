{-# OPTIONS --irrelevant-projections --rewriting --prop #-}

open import common

{- Equivalence relations -}

record EquivRel (A : Set) : Set₁ where
  field
    _≃_ : A → A → Prop
    .ref : (a : A) → a ≃ a
    .sym : {a b : A} → a ≃ b → b ≃ a
    .tra : {a b c : A} → a ≃ b → b ≃ c → a ≃ c

{- Function extensionality -}

postulate
  funext : {A B : Set} {f g : A → B} (h : (x : A) → f x ≡ g x) → f ≡ g
  funextI : {A B : Set} {f g : .A → B} (h : (x : A) → f x ≡ g x) → f ≡ g

{- Quotients -}

postulate
  _//_ : (A : Set) (R : EquivRel A) → Set

module _ {A : Set} {R : EquivRel A} where
  open EquivRel R

  postulate
    {- Introduction rules -}

    proj : A → A // R
    eq : {a b : A} (r : a ≃ b) → proj a ≡ proj b

    {- Elimination rules -}

    //-rec : ∀ {l} (B : Set l) (d : A → B) (eq* : (a b : A) (r : a ≃ b) → d a ≡ d b) → A // R → B
    //-elimId : {B : Set} (f g : A // R → B) (d : (a : A) → f (proj a) ≡ g (proj a)) → (x : A // R) → f x ≡ g x

    //-elimPiIdCst : {B : Set} {f g : A // R → B} {C : Set}
                → (d : (a : A) .(p : f (proj a) ≡ g (proj a)) → C)
                → .((a b : A) (r : a ≃ b) (p : f (proj a) ≡ g (proj a)) (q : f (proj b) ≡ g (proj b)) → d a p ≡ d b q)
                → ((x : A // R) .(p : f x ≡ g x) → C)

    //-elimPiIdId : {B : Set} {f g : A // R → B} {C : Set} {h k : (x : A // R) .(p : f x ≡ g x) → C}
                → ((a : A) .(p : f (proj a) ≡ g (proj a)) → h (proj a) p ≡ k (proj a) p)
                → ((x : A // R) .(p : f x ≡ g x) → h x p ≡ k x p)

    //-elimPiIdIdId : {B B' : Set} {f g : A // R → B} {f' g' : A // R → B'} {C : Set} {h k : (x : A // R) .(p : f x ≡ g x) .(p' : f' x ≡ g' x) → C}
                → .((a : A) .(p : f (proj a) ≡ g (proj a)) .(p' : f' (proj a) ≡ g' (proj a)) → h (proj a) p p' ≡ k (proj a) p p')
                → ((x : A // R) .(p : f x ≡ g x) .(p' : f' x ≡ g' x) → h x p p' ≡ k x p p')

    //-elimPiIdIdIdR : {B B' : Set} {f g : A // R → B} {f' g' : (x : A // R) (p : f x ≡ g x) → B'} {C : Set} {h k : (x : A // R) (p : f x ≡ g x) (p' : f' x p ≡ g' x p) → C}
                → .((a : A) (p : f (proj a) ≡ g (proj a)) (p' : f' (proj a) p ≡ g' (proj a) p) → h (proj a) p p' ≡ k (proj a) p p')
                → ((x : A // R) (p : f x ≡ g x) (p' : f' x p ≡ g' x p) → h x p p' ≡ k x p p')

    {- Reduction rules -}

    //-beta : ∀ {l} {B : Set l} {d : A → B} {eq* : (a b : A) (r : a ≃ b) → d a ≡ d b} {a : A}
            → //-rec B d eq* (proj a) ≡R d a

    //-betaPiIdCst : {B C : Set} {f g : A // R → B}
                → {d : (a : A) .(_ : f (proj a) ≡ g (proj a)) → C}
                → {eq* : (a b : A) (r : a ≃ b) (p : f (proj a) ≡ g (proj a)) (q : f (proj b) ≡ g (proj b)) → d a p ≡ d b q}
                → {a : A} {p : f (proj a) ≡ g (proj a)} → //-elimPiIdCst {f = f} {g = g} d eq* (proj a) p ≡R d a p

{-# REWRITE //-beta #-}
{-# REWRITE //-betaPiIdCst #-}

{- Other helper functions (iterated elimination principles) -}

module _ {A A' : Set} {R : EquivRel A} {R' : EquivRel A'}
         {B : Set} {f g : A // R → A' // R' → B}
         {P : Set}
         (d : (a : A) (a' : A') .(p : f (proj a) (proj a') ≡ g (proj a) (proj a')) → P)
         (eq* : (a b : A) (r : EquivRel._≃_ R a b) (a' b' : A') (r' : EquivRel._≃_ R' a' b') .(p : f (proj a) (proj a') ≡ g (proj a) (proj a')) .(q : f (proj b) (proj b') ≡ g (proj b) (proj b')) → d a a' p ≡ d b b' q) where

  //-elimPiCstIdCst : (x : A // R) (y : A' // R') .(p : f x y ≡ g x y) → P
  //-elimPiCstIdCst x = //-elimPiIdCst (λ a' → aux a' x) (λ a b r → eq-aux a b r x) where

    aux : (a' : A') (x : A // R) .(p : f x (proj a') ≡ g x (proj a')) → P
    aux a' = //-elimPiIdCst (λ a → d a a') (λ a b r p q → eq* a b r a' a' (EquivRel.ref R' a') p q)

    eq-aux : (a' b' : A') (r' : EquivRel._≃_ R' a' b') (x : A // R) .(p : f x (proj a') ≡ g x (proj a')) .(q : f x (proj b') ≡ g x (proj b')) → aux a' x p ≡ aux b' x q
    eq-aux a' b' r' = //-elimPiIdIdId (λ a p p' → eq* a a (EquivRel.ref R a) a' b' r' p p')

module _ {A A' : Set} {R : EquivRel A} {R' : EquivRel A'}
         {B C : Set} {f g : A // R → A' // R' → B}
         {h k : (x : A // R) (y : A' // R') .(p : f x y ≡ g x y) → C}
         (d : (a : A) (a' : A') .(p : f (proj a) (proj a') ≡ g (proj a) (proj a')) → h (proj a) (proj a') p ≡ k (proj a) (proj a') p) where

  //-elimPiCstIdId : (x : A // R) (y : A' // R') .(p : f x y ≡ g x y) → h x y p ≡ k x y p
  //-elimPiCstIdId x = //-elimPiIdId (λ a' → aux a' x) where

    aux : (a' : A') (x : A // R) .(p : f x (proj a') ≡ g x (proj a')) → h x (proj a') p ≡ k x (proj a') p
    aux a' = //-elimPiIdId (λ a → d a a')

module _ {A A' : Set} {R : EquivRel A} {R' : EquivRel A'}
         {B B' C : Set} {f g : A // R → A' // R' → B} {f' g' : (x : A // R) (y : A' // R') (p : f x y ≡ g x y) → B'}
         {h k : (x : A // R) (y : A' // R') (p : f x y ≡ g x y) (p' : f' x y p ≡ g' x y p) → C}
         (d : (a : A) (a' : A') (p : f (proj a) (proj a') ≡ g (proj a) (proj a')) (p' : f' (proj a) (proj a') p ≡ g' (proj a) (proj a') p) → h (proj a) (proj a') p p' ≡ k (proj a) (proj a') p p') where

  //-elimPiCstIdIdId : (x : A // R) (y : A' // R') (p : f x y ≡ g x y) (p' : f' x y p ≡ g' x y p) → h x y p p' ≡ k x y p p'
  //-elimPiCstIdIdId x = //-elimPiIdIdIdR (λ a' → aux a' x) where

    aux : (a' : A') (x : A // R) (p : f x (proj a') ≡ g x (proj a')) (p' : f' x (proj a') p ≡ g' x (proj a') p) → h x (proj a') p p' ≡ k x (proj a') p p'
    aux a' = //-elimPiIdIdIdR (λ a → d a a')

module _ {A A' A'' : Set} {R : EquivRel A} {R' : EquivRel A'} {R'' : EquivRel A''}
         {B B' C : Set} {f g : A // R → A' // R' → A'' // R'' → B} {f' g' : (x : A // R) (y : A' // R') (z : A'' // R'') (p : f x y z ≡ g x y z) → B'}
         {h k : (x : A // R) (y : A' // R') (z : A'' // R'') (p : f x y z ≡ g x y z) (p' : f' x y z p ≡ g' x y z p) → C}
         (d : (a : A) (a' : A') (a'' : A'') (p : f (proj a) (proj a') (proj a'') ≡ g (proj a) (proj a') (proj a'')) (p' : f' (proj a) (proj a') (proj a'') p ≡ g' (proj a) (proj a') (proj a'') p) → h (proj a) (proj a') (proj a'') p p' ≡ k (proj a) (proj a') (proj a'') p p') where

  //-elimPiCstCstIdIdId : (x : A // R) (y : A' // R') (z : A'' // R'') (p : f x y z ≡ g x y z) (p' : f' x y z p ≡ g' x y z p) → h x y z p p' ≡ k x y z p p'
  //-elimPiCstCstIdIdId x = //-elimPiCstIdIdId (λ a' a'' → aux a' a'' x) where

    aux : (a' : A') (a'' : A'') (x : A // R) (p : f x (proj a') (proj a'') ≡ g x (proj a') (proj a'')) (p' : f' x (proj a') (proj a'') p ≡ g' x (proj a') (proj a'') p) → h x (proj a') (proj a'') p p' ≡ k x (proj a') (proj a'') p p'
    aux a' a'' = //-elimPiIdIdIdR (λ a → d a a' a'')

{- Effectiveness of quotients, using propositional extensionality -}

postulate
  prop-ext : {A B : Prop} .(f : A → B) .(g : B → A) → A ≡ B

module _ {A : Set} {R : EquivRel A} where
  open EquivRel R

  _≃'_ : (a : A) (c : A // R) → Prop
  _≃'_ a = //-rec _ (λ b → a ≃ b) (λ b c r → prop-ext (λ z → tra z r) λ z → tra z (sym r))

  .reflect' : {a : A} (c : A // R) → proj a ≡ c → a ≃' c
  reflect' {a} c refl = ref a

  .reflect : {a b : A} → proj a ≡ proj b → a ≃ b
  reflect {b = b} p = reflect' (proj b) p
