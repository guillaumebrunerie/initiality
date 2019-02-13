{-# OPTIONS --rewriting --prop --without-K --allow-unsolved-metas #-}

open import common hiding (_>>=_; return)
open import typetheory
open import syntx
open import contextualcat

module _ (sC : StructuredCCat) where

_>>=_ = common._>>=_ {M = Partial}
return = common.return {M = Partial}

open StructuredCCat sC
open CCat ccat renaming (Mor to MorC; id to idC)


ap-irr-ElStr : {n : ℕ} {i : ℕ} {Γ Γ' : _} (Γ-eq : Γ ≡ Γ') {v v' : _} (v-eq : v ≡ v') {vₛ : _} {vₛ' : _} {v₁ : _} {v₁' : _} → ElStr {n = n} i Γ v vₛ v₁ ≡ ElStr i Γ' v' vₛ' v₁'
ap-irr-ElStr refl refl = refl

ap-irr-PiStr : {n : ℕ} {Γ Γ' : _} (Γ-eq : Γ ≡ Γ') {A A' : _} (A-eq : A ≡ A') {A= : _} {A=' : _} {B B' : _} (B-eq : B ≡ B') {B= : _} {B=' : _} → PiStr {n = n} Γ A A= B B= ≡ PiStr Γ' A' A=' B' B='
ap-irr-PiStr refl refl refl = refl

ap-irr-piStr : {n : ℕ} {i : ℕ} {X X' : _} (X-eq : X ≡ X') {a a' : _} (a-eq : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} {b b' : _} (b-eq : b ≡ b') {bₛ : _} {bₛ' : _} {b₁ : _} {b₁' : _} → piStr {n = n} i X a aₛ a₁ b bₛ b₁ ≡ piStr i X' a' aₛ' a₁' b' bₛ' b₁'
ap-irr-piStr refl refl refl = refl

ap-irr-lamStr : {n : ℕ} {X X' : _} (X-eq : X ≡ X') {A A' : _} (A-eq : A ≡ A') {A= : _} {A=' : _} {B B' : _} (B-eq : B ≡ B') {B= : _} {B=' : _} {u u' : _} (u-eq : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} → lamStr {n = n} X A A= B B= u uₛ u₁ ≡ lamStr X A' A=' B' B=' u' uₛ' u₁'
ap-irr-lamStr refl refl refl refl = refl

ap-irr-appStr : {n : ℕ} {X X' : _} (X-eq : X ≡ X') {A A' : _} (A-eq : A ≡ A') {A= : _} {A=' : _} {B B' : _} (B-eq : B ≡ B') {B= : _} {B=' : _} {f f' : _} (f-eq : f ≡ f') {fₛ : _} {fₛ' : _} {f₁ : _} {f₁' : _} {a a' : _} (a-eq : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} → appStr {n = n} X A A= B B= f fₛ f₁ a aₛ a₁ ≡ appStr X' A' A=' B' B=' f' fₛ' f₁' a' aₛ' a₁'
ap-irr-appStr refl refl refl refl refl = refl

ap-irr-SigStr : {n : ℕ} {Γ Γ' : _} (Γ-eq : Γ ≡ Γ') {A A' : _} (A-eq : A ≡ A') {A= : _} {A=' : _} {B B' : _} (B-eq : B ≡ B') {B= : _} {B=' : _} → SigStr {n = n} Γ A A= B B= ≡ SigStr Γ' A' A=' B' B='
ap-irr-SigStr refl refl refl = refl

ap-irr-sigStr : {n : ℕ} {i : ℕ} {X X' : _} (X-eq : X ≡ X') {a a' : _} (a-eq : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} {b b' : _} (b-eq : b ≡ b') {bₛ : _} {bₛ' : _} {b₁ : _} {b₁' : _} → sigStr {n = n} i X a aₛ a₁ b bₛ b₁ ≡ sigStr i X' a' aₛ' a₁' b' bₛ' b₁'
ap-irr-sigStr refl refl refl = refl

ap-irr-pairStr : {n : ℕ} {X X' : _} (X-eq : X ≡ X') {A A' : _} (A-eq : A ≡ A') {A= : _} {A=' : _} {B B' : _} (B-eq : B ≡ B') {B= : _} {B=' : _} {a a' : _} (a-eq : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} {b b' : _} (b-eq : b ≡ b') {bₛ : _} {bₛ' : _} {b₁ : _} {b₁' : _} → pairStr {n = n} X A A= B B= a aₛ a₁ b bₛ b₁ ≡ pairStr X' A' A=' B' B=' a' aₛ' a₁' b' bₛ' b₁'
ap-irr-pairStr refl refl refl refl refl = refl

ap-irr-pr1Str : {n : ℕ} {X X' : _} (X-eq : X ≡ X') {A A' : _} (A-eq : A ≡ A') {A= : _} {A=' : _} {B B' : _} (B-eq : B ≡ B') {B= : _} {B=' : _} {u u' : _} (u-eq : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} → pr1Str {n = n} X A A= B B= u uₛ u₁ ≡ pr1Str X' A' A=' B' B=' u' uₛ' u₁'
ap-irr-pr1Str refl refl refl refl = refl

ap-irr-pr2Str : {n : ℕ} {X X' : _} (X-eq : X ≡ X') {A A' : _} (A-eq : A ≡ A') {A= : _} {A=' : _} {B B' : _} (B-eq : B ≡ B') {B= : _} {B=' : _} {u u' : _} (u-eq : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} → pr2Str {n = n} X A A= B B= u uₛ u₁ ≡ pr2Str X' A' A=' B' B=' u' uₛ' u₁'
ap-irr-pr2Str refl refl refl refl = refl

-- ap-irr-sucStr : {n : ℕ} {Γ Γ' : _} (Γ-eq : Γ ≡ Γ') {v v' : _} (v-eq : v ≡ v') {vₛ : _} {vₛ' : _} {v₁ : _} {v₁' : _} → sucStr {n = n} Γ v vₛ v₁ ≡ sucStr Γ' v' vₛ' v₁'
-- ap-irr-sucStr refl refl = refl

ap-irr-natelimStr : {n : ℕ} {X X' : _} (X-eq : X ≡ X') {P P' : _} (P-eq : P ≡ P') {dO dO' : _} (dO-eq : dO ≡ dO') {dS dS' : _} (dS-eq : dS ≡ dS') {u u' : _} (u-eq : u ≡ u') → ∀ {P= P'=} → {dS₁ : _} {dS'₁ : _} → ∀ {dOₛ dO₁ dSₛ uₛ u₁ dO'ₛ dO'₁ dS'ₛ u'ₛ u'₁}
  → natelimStr {n = n} X P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁ ≡ natelimStr X' P' P'= dO' dO'ₛ dO'₁ dS' dS'ₛ dS'₁ u' u'ₛ u'₁
ap-irr-natelimStr refl refl refl refl refl = refl

ap-irr-idStr : {n : ℕ} {i : ℕ} {X X' : _} (X-eq : X ≡ X') {a a' : _} (a-eq : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} {u u' : _} (u-eq : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} {v v' : _} (v-eq : v ≡ v') {vₛ : _} {vₛ' : _} {v₁ : _} {v₁' : _} → idStr {n = n} i X a aₛ a₁ u uₛ u₁ v vₛ v₁ ≡ idStr {n = n} i X' a' aₛ' a₁' u' uₛ' u₁' v' vₛ' v₁'
ap-irr-idStr refl refl refl refl = refl

ap-irr-reflStr : {n : ℕ} {Γ Γ' : _} (Γ-eq : Γ ≡ Γ') {A A' : _} (A-eq : A ≡ A') {A= : _} {A=' : _} {a : _} {a' : _} (a-eq : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} → reflStr {n = n} Γ A A= a aₛ a₁ ≡ reflStr {n = n} Γ' A' A=' a' aₛ' a₁'
ap-irr-reflStr refl refl refl = refl


{- Partial interpretation of types and terms -}

⟦_⟧Ty : TyExpr n → (X : Ob n) → Partial (Ob (suc n))
⟦_⟧Tm : TmExpr n → (X : Ob n) → Partial (MorC n (suc n))

⟦ uu i ⟧Ty X = return (UUStr i X)
⟦ el i v ⟧Ty X = do
  [v] ← ⟦ v ⟧Tm X
  [v]ₛ ← assume (is-section [v])
  [v]₁ ← assume (∂₁ [v] ≡ UUStr i X)
  return (ElStr i X [v] (unbox [v]ₛ) (unbox [v]₁))
⟦ pi A B ⟧Ty X = do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [B] ← ⟦ B ⟧Ty [A]
  [B]= ← assume (ft [B] ≡ [A])
  return (PiStr X [A] (unbox [A]=) [B] (unbox [B]=))
⟦ sig A B ⟧Ty X = do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [B] ← ⟦ B ⟧Ty [A]
  [B]= ← assume (ft [B] ≡ [A])
  return (SigStr X [A] (unbox [A]=) [B] (unbox [B]=))
⟦ nat ⟧Ty X = return (NatStr X)
⟦ id A u v ⟧Ty X = do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ [A])
  [v] ← ⟦ v ⟧Tm X
  [v]ₛ ← assume (is-section [v])
  [v]₁ ← assume (∂₁ [v] ≡ [A])
  return (IdStr X [A] (unbox [A]=) [u] (unbox [u]ₛ) (unbox [u]₁) [v] (unbox [v]ₛ) (unbox [v]₁))


⟦ var k ⟧Tm X = return (varC k X)
⟦ uu i ⟧Tm X = return (uuStr i X)
⟦ pi i a b ⟧Tm X = do
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ UUStr i X)
  [b] ← ⟦ b ⟧Tm (ElStr i X [a] (unbox [a]ₛ) (unbox [a]₁))
  [b]ₛ ← assume (is-section [b])
  [b]₁ ← assume (∂₁ [b] ≡ UUStr i (ElStr i X [a] (unbox [a]ₛ) (unbox [a]₁)))
  return (piStr i X [a] (unbox [a]ₛ) (unbox [a]₁) [b] (unbox [b]ₛ) (unbox [b]₁))
⟦ lam A B u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [B] ← ⟦ B ⟧Ty [A]
  [B]= ← assume (ft [B] ≡ [A])
  [u] ← ⟦ u ⟧Tm [A]
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ [B])
  return (lamStr X [A] (unbox [A]=) [B] (unbox [B]=) [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ app A B f a ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [B] ← ⟦ B ⟧Ty [A]
  [B]= ← assume (ft [B] ≡ [A])
  [f] ← ⟦ f ⟧Tm X
  [f]ₛ ← assume (is-section [f])
  [f]₁ ← assume (∂₁ [f] ≡ PiStr X [A] (unbox [A]=) [B] (unbox [B]=))
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ [A])
  return (appStr X [A] (unbox [A]=) [B] (unbox [B]=) [f] (unbox [f]ₛ) (unbox [f]₁) [a] (unbox [a]ₛ) (unbox [a]₁))
⟦ sig i a b ⟧Tm X = do
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ UUStr i X)
  [b] ← ⟦ b ⟧Tm (ElStr i X [a] (unbox [a]ₛ) (unbox [a]₁))
  [b]ₛ ← assume (is-section [b])
  [b]₁ ← assume (∂₁ [b] ≡ UUStr i (ElStr i X [a] (unbox [a]ₛ) (unbox [a]₁)))
  return (sigStr i X [a] (unbox [a]ₛ) (unbox [a]₁) [b] (unbox [b]ₛ) (unbox [b]₁))
⟦ pair A B u v ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [B] ← ⟦ B ⟧Ty [A]
  [B]= ← assume (ft [B] ≡ [A])
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ [A])
  [v] ← ⟦ v ⟧Tm X
  [v]ₛ ← assume (is-section [v])
  [v]₁ ← assume (∂₁ [v] ≡ star [u] [B] (unbox [B]=) (unbox [u]₁))
  return (pairStr X [A] (unbox [A]=) [B] (unbox [B]=) [u] (unbox [u]ₛ) (unbox [u]₁) [v] (unbox [v]ₛ) (unbox [v]₁))
⟦ pr1 A B u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [B] ← ⟦ B ⟧Ty [A]
  [B]= ← assume (ft [B] ≡ [A])
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ SigStr X [A] (unbox [A]=) [B] (unbox [B]=))
  return (pr1Str X [A] (unbox [A]=) [B] (unbox [B]=) [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ pr2 A B u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [B] ← ⟦ B ⟧Ty [A]
  [B]= ← assume (ft [B] ≡ [A])
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ SigStr X [A] (unbox [A]=) [B] (unbox [B]=))
  return (pr2Str X [A] (unbox [A]=) [B] (unbox [B]=) [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ nat i ⟧Tm X = return (natStr i X)
⟦ zero ⟧Tm X = return (zeroStr X)
⟦ suc u ⟧Tm X = do
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ NatStr X)
  return (sucStr X [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ natelim P dO dS u ⟧Tm X = do
  [P] ← ⟦ P ⟧Ty (NatStr X)
  [P]= ← assume (ft [P] ≡ NatStr X)
  [dO]  ← ⟦ dO ⟧Tm X
  [dO]ₛ ← assume (is-section [dO])
  [dO]₁ ← assume (∂₁ [dO] ≡ star (zeroStr X) [P] _ _)
  [dS]  ← ⟦ dS ⟧Tm [P]
  [dS]ₛ ← assume (is-section [dS])
  [dS]₁ ← assume (∂₁ [dS] ≡ typing-dS₁.T-dS₁ ccat ccatNat ccatzero ccatsuc X [P] (unbox [P]=) [dS])
  [u]  ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ NatStr X)
  return (natelimStr X [P] (unbox [P]=) [dO] (unbox [dO]ₛ) (unbox [dO]₁) [dS] (unbox [dS]ₛ) (unbox [dS]₁) [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ id i a u v ⟧Tm X = do
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ UUStr i X)
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ ElStr i X [a] (unbox [a]ₛ) (unbox [a]₁))
  [v] ← ⟦ v ⟧Tm X
  [v]ₛ ← assume (is-section [v])
  [v]₁ ← assume (∂₁ [v] ≡ ElStr i X [a] (unbox [a]ₛ) (unbox [a]₁))
  return (idStr i X [a] (unbox [a]ₛ) (unbox [a]₁) [u] (unbox [u]ₛ) (unbox [u]₁) [v] (unbox [v]ₛ) (unbox [v]₁))
⟦ refl A u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ [A])
  return (reflStr X [A] (unbox [A]=) [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ jj A P d a b p ⟧Tm X = {!!} {- do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [P] ← ⟦ P ⟧Ty (T-ftP X [A] (unbox [A]=)) 
  [P]= ← assume (ft [P] ≡ _)
  [d] ← ⟦ d ⟧Tm [A]
  [d]ₛ ← assume (is-section [d])
  [d]₁ ← assume (∂₁ [d] ≡ {!!})
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ [A])
  [b] ← ⟦ b ⟧Tm X
  [b]ₛ ← assume (is-section [b])
  [b]₁ ← assume (∂₁ [b] ≡ [A])
  [p] ← ⟦ p ⟧Tm X
  [p]ₛ ← assume (is-section [p])
  [p]₁ ← assume (∂₁ [p] ≡ IdStr X [A] (unbox [A]=) [a] (unbox [a]ₛ) (unbox [a]₁) [b] (unbox [b]ₛ) (unbox [b]₁))
  return (jjStr X [A] (unbox [A]=) [P] (unbox [P]=) [d] (unbox [d]ₛ) (unbox [d]₁) [a] (unbox [a]ₛ) (unbox [a]₁) [b] (unbox [b]ₛ) (unbox [b]₁) [p] (unbox [p]ₛ) (unbox [p]₁))-}

{- Partial interpretation of contexts and context morphisms -}

⟦_⟧Ctx : (Γ : Ctx n) → Partial (Ob n)
⟦ ◇ ⟧Ctx = return pt
⟦ Γ , A ⟧Ctx = do
  [Γ] ← ⟦ Γ ⟧Ctx
  [A] ← ⟦ A ⟧Ty [Γ]
  return [A]

⟦_⟧Mor : (δ : Mor n m) (X : Ob n) (Y : Ob m) → Partial (MorC n m)
⟦ ◇ ⟧Mor X Y = return (ptmor X)
⟦ δ , u ⟧Mor X Y = do
  [δ] ← ⟦ δ ⟧Mor X (ft Y)
  [u] ← ⟦ u ⟧Tm X
  [δ]₁ ← assume (∂₁ [δ] ≡ ft Y)
  [u]₁ ← assume (∂₁ [u] ≡ star [δ] Y refl (unbox [δ]₁))
  return (comp (qq [δ] Y refl (unbox [δ]₁)) [u] qq₀ (unbox [u]₁))


{- Basic properties of the partial interpretation functions -}

⟦⟧Tmₛ : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → is-section (⟦ u ⟧Tm X $ uᵈ)
⟦⟧Tmₛ (var k) = varCₛ k _
⟦⟧Tmₛ (uu i) = uuStrₛ
⟦⟧Tmₛ (pi i a b) = piStrₛ
⟦⟧Tmₛ (lam A B u) = lamStrₛ
⟦⟧Tmₛ (app A B f a) = appStrₛ
⟦⟧Tmₛ (sig i a b) = sigStrₛ
⟦⟧Tmₛ (pair A B u v) = pairStrₛ
⟦⟧Tmₛ (pr1 A B u) = pr1Strₛ
⟦⟧Tmₛ (pr2 A B u) = pr2Strₛ
⟦⟧Tmₛ (nat i) = natStrₛ
⟦⟧Tmₛ zero = zeroStrₛ
⟦⟧Tmₛ (suc u) = sucStrₛ
⟦⟧Tmₛ (natelim P d0 dS u) = natelimStrₛ
⟦⟧Tmₛ (id i a u v) = idStrₛ
⟦⟧Tmₛ (refl A u) = reflStrₛ
⟦⟧Tmₛ (jj A P d a b p) = {!!} {-jjStrₛ-}

⟦⟧Ty-ft : {X : Ob n} (A : TyExpr n) {Aᵈ : isDefined (⟦ A ⟧Ty X)} → ft (⟦ A ⟧Ty X $ Aᵈ) ≡ X
⟦⟧Ty-ft (uu i) = UUStr=
⟦⟧Ty-ft (el i v) = ElStr=
⟦⟧Ty-ft (pi A B)  = PiStr=
⟦⟧Ty-ft (sig A B) = SigStr=
⟦⟧Ty-ft nat = NatStr=
⟦⟧Ty-ft (id A u v) = IdStr=

⟦⟧Tm₀ : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → ∂₀ (⟦ u ⟧Tm X $ uᵈ) ≡ X
⟦⟧Tm₀ (var k) = varC₀
⟦⟧Tm₀ (uu i) = uuStr₀
⟦⟧Tm₀ (pi i a b) = piStr₀
⟦⟧Tm₀ (lam A B u) = lamStr₀
⟦⟧Tm₀ (app A B f a) = appStr₀
⟦⟧Tm₀ (sig i a b) = sigStr₀
⟦⟧Tm₀ (pair A B u v) = pairStr₀
⟦⟧Tm₀ (pr1 A B u) = pr1Str₀
⟦⟧Tm₀ (pr2 A B u) = pr2Str₀
⟦⟧Tm₀ (nat i) = natStr₀
⟦⟧Tm₀ zero = zeroStr₀
⟦⟧Tm₀ (suc u) = sucStr₀
⟦⟧Tm₀ (natelim P d0 dS u) = natelimStr₀
⟦⟧Tm₀ (id i a u v) = idStr₀
⟦⟧Tm₀ (refl A u) = reflStr₀
⟦⟧Tm₀ (jj A P d a b p) = {!!} {-jjStr₀-}

⟦⟧Tm₁-ft : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} {Z : Ob (suc n)} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Z) → ft Z ≡ X
⟦⟧Tm₁-ft u u₁ = ap ft (! u₁) ∙ ! (is-section₀ (⟦⟧Tmₛ u) refl) ∙ ⟦⟧Tm₀ u

⟦⟧Mor₀ : {X : Ob n} {Y : Ob m} (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₀ (⟦ δ ⟧Mor X Y $ δᵈ) ≡ X
⟦⟧Mor₀ ◇ = ptmor₀
⟦⟧Mor₀ (δ , u) = comp₀ ∙ ⟦⟧Tm₀ u

⟦⟧Mor₁ : {X : Ob n} {Y : Ob m} (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₁ (⟦ δ ⟧Mor X Y $ δᵈ) ≡ Y
⟦⟧Mor₁ ◇ = ptmor₁ ∙ ! (pt-unique _)
⟦⟧Mor₁ (δ , u) = comp₁ ∙ qq₁
