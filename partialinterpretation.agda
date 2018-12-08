{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import syntx
open import contextualcat

module _ (C : StructuredCCat) where

open StructuredCCat C
open CCat ccat renaming (Mor to MorC; id to idC)

{- Partial interpretation of types and terms -}

⟦_⟧Ty : TyExpr n → (X : Ob n) → Partial (Ob (suc n))
⟦_⟧Tm : TmExpr n → (X : Ob n) → Partial (MorC n (suc n))

⟦ uu i ⟧Ty X = return (UUStr i X)
⟦ el i v ⟧Ty X = do
  [v] ← ⟦ v ⟧Tm X
  [v]ₛ ← assume (is-section [v])
  [v]₁ ← assume (∂₁ [v] ≡ UUStr i (∂₀ [v]))
  return (ElStr i [v] (unbox [v]ₛ) (unbox [v]₁))
⟦ pi A B ⟧Ty X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  return (PiStr [B])
⟦ sig A B ⟧Ty X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  return (SigStr [B])
⟦ nat ⟧Ty X = return (NatStr X)
⟦ id _ u v ⟧Ty X = do
  [u] ← ⟦ u ⟧Tm X
  [v] ← ⟦ v ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [v]ₛ ← assume (is-section [v])
  p ← assume (∂₁ [u] ≡ ∂₁ [v])
  return (IdStr [u] (unbox [u]ₛ) [v] (unbox [v]ₛ) (unbox p))


⟦ var last ⟧Tm X = return (ss (idC X))
⟦ var (prev x) ⟧Tm X = do
  [x] ← ⟦ var x ⟧Tm (ft X)
  [x]₀ ← assume (∂₀ [x] ≡ ft X)
  return (ss (comp [x] (pp X) (pp₁ ∙ ! (unbox [x]₀))))
⟦ uu i ⟧Tm X = return (uuStr i X)
⟦ pi i a b ⟧Tm X = do
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ UUStr i (∂₀ [a]))
  [b] ← ⟦ b ⟧Tm (ElStr i [a] (unbox [a]ₛ) (unbox [a]₁))
  [b]ₛ ← assume (is-section [b])
  [b]₁ ← assume (∂₁ [b] ≡ UUStr i (ElStr i [a] (unbox [a]ₛ) (unbox [a]₁)))
  return (piStr i [a] (unbox [a]ₛ) (unbox [a]₁) [b] (unbox [b]ₛ) (unbox [b]₁))
⟦ lam A _ u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [u] ← ⟦ u ⟧Tm [A]
  [u]ₛ ← assume (is-section [u])
  return (lamStr [u] (unbox [u]ₛ))
⟦ app A B f a ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  [f] ← ⟦ f ⟧Tm X
  [a] ← ⟦ a ⟧Tm X
  [f]ₛ ← assume (is-section [f])
  [f]₁ ← assume (∂₁ [f] ≡ PiStr [B])
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ ft [B])
  return (appStr [B] [f] (unbox [f]ₛ) (unbox [f]₁) [a] (unbox [a]ₛ) (unbox [a]₁))
⟦ sig i a b ⟧Tm X = do
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ UUStr i (∂₀ [a]))
  [b] ← ⟦ b ⟧Tm (ElStr i [a] (unbox [a]ₛ) (unbox [a]₁))
  [b]ₛ ← assume (is-section [b])
  [b]₁ ← assume (∂₁ [b] ≡ UUStr i (ElStr i [a] (unbox [a]ₛ) (unbox [a]₁)))
  return (sigStr i [a] (unbox [a]ₛ) (unbox [a]₁) [b] (unbox [b]ₛ) (unbox [b]₁))
⟦ pair A B u v ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  [u] ← ⟦ u ⟧Tm X
  [v] ← ⟦ v ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ ft [B])
  [v]ₛ ← assume (is-section [v])
  [v]₁ ← assume (∂₁ [v] ≡ star [u] [B] (unbox [u]₁))
  return (pairStr [B] [u] (unbox [u]ₛ) (unbox [u]₁) [v] (unbox [v]ₛ) (unbox [v]₁))
⟦ pr1 A B u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ SigStr [B])
  return (pr1Str [B] [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ pr2 A B u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ SigStr [B])
  return (pr2Str [B] [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ nat i ⟧Tm X = return (natStr i X)
⟦ zero ⟧Tm X = return (zeroStr X)
⟦ suc u ⟧Tm X = do
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ NatStr (∂₀ [u]))
  return (sucStr [u] (unbox [u]ₛ) (unbox [u]₁))
--⟦ nat-elim P x x₁ x₂ ⟧Tm X = {!!}
⟦ id i a u v ⟧Tm X = do
  [a] ← ⟦ a ⟧Tm X
  [u] ← ⟦ u ⟧Tm X
  [v] ← ⟦ v ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ UUStr i (∂₀ [a]))
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ ElStr i [a] (unbox [a]ₛ) (unbox [a]₁))
  [v]ₛ ← assume (is-section [v])
  [v]₁ ← assume (∂₁ [v] ≡ ElStr i [a] (unbox [a]ₛ) (unbox [a]₁))
  return (idStr i [a] (unbox [a]ₛ) (unbox [a]₁) [u] (unbox [u]ₛ) (unbox [u]₁) [v] (unbox [v]ₛ) (unbox [v]₁))
⟦ refl _ u ⟧Tm X = do
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  return (reflStr [u] (unbox [u]ₛ))

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
  [u]₁ ← assume (∂₁ [u] ≡ star [δ] Y (unbox [δ]₁))
  return (comp (qq [δ] Y (unbox [δ]₁)) [u] (unbox [u]₁ ∙ ! qq₀))

{- Basic properties of the partial interpretation functions -}

⟦⟧Tmₛ : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → is-section (⟦ u ⟧Tm X $ uᵈ)
⟦⟧Tmₛ (var last) = ssₛ
⟦⟧Tmₛ (var (prev x)) = ssₛ
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
--⟦⟧Tmₛ (nat-elim P d0 dS u) = {!nat-elimStrₛ!}
⟦⟧Tmₛ (id i a u v) = idStrₛ
⟦⟧Tmₛ (refl A u) = reflStrₛ

⟦⟧Ty-ft : {X : Ob n} (A : TyExpr n) {Aᵈ : isDefined (⟦ A ⟧Ty X)} → ft (⟦ A ⟧Ty X $ Aᵈ) ≡ X
⟦⟧Tm₀ : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → ∂₀ (⟦ u ⟧Tm X $ uᵈ) ≡ X

⟦⟧Ty-ft (uu i) = UUStr=
⟦⟧Ty-ft (el i v) = ElStr= ∙ ⟦⟧Tm₀ v
⟦⟧Ty-ft (pi A B)  = PiStr= ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Ty-ft (sig A B) = SigStr= ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Ty-ft nat = NatStr=
⟦⟧Ty-ft (id A u v) = IdStr= ∙ ⟦⟧Tm₀ u

⟦⟧Tm₀ (var last) = ss₀ ∙ id₀
⟦⟧Tm₀ (var (prev x)) = ss₀ ∙ comp₀ ∙ pp₀
⟦⟧Tm₀ (uu i) = uuStr₀ _
⟦⟧Tm₀ (pi i a b) = piStr₀ _ ∙ ⟦⟧Tm₀ a
⟦⟧Tm₀ (lam A B u) = lamStr₀ _ ∙ ap ft (⟦⟧Tm₀ u) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (app A B f a) = appStr₀ _ _ ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (sig i a b) = sigStr₀ _ ∙ ⟦⟧Tm₀ a
⟦⟧Tm₀ (pair A B u v) = pairStr₀ _ ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (pr1 A B u) = pr1Str₀ _ ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (pr2 A B u) = pr2Str₀ _ ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (nat i) = natStr₀ _
⟦⟧Tm₀ zero = zeroStr₀ _
⟦⟧Tm₀ (suc u) = sucStr₀ _ ∙ ⟦⟧Tm₀ u
--⟦⟧Tm₀ (nat-elim P d0 dS u) = ?
⟦⟧Tm₀ (id i a u v) = idStr₀ _ ∙ ⟦⟧Tm₀ a
⟦⟧Tm₀ (refl A u) = reflStr₀ _ ∙ ⟦⟧Tm₀ u

⟦⟧Tm₁-ft : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → ft (∂₁ (⟦ u ⟧Tm X $ uᵈ)) ≡ X
⟦⟧Tm₁-ft (var last) = ap ft ss₁ ∙ ft-star ∙ comp₀ ∙ id₀
⟦⟧Tm₁-ft (var (prev x)) = ap ft ss₁ ∙ ft-star ∙ comp₀ ∙ comp₀ ∙ pp₀
⟦⟧Tm₁-ft (uu i) = ap ft uuStr₁ ∙ UUStr=
⟦⟧Tm₁-ft (pi i a b) = ap ft piStr₁ ∙ UUStr= ∙ ⟦⟧Tm₀ a
⟦⟧Tm₁-ft (lam A B u) {uᵈ = Aᵈ , _} = ap ft lamStr₁ ∙ PiStr= ∙ ap ft (⟦⟧Tm₁-ft u) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₁-ft (app A B f a) = ap ft appStr₁ ∙ ft-star ∙ ⟦⟧Tm₀ a
⟦⟧Tm₁-ft (sig i a b) = ap ft sigStr₁ ∙ UUStr= ∙ ⟦⟧Tm₀ a
⟦⟧Tm₁-ft (pair A B u v) = ap ft pairStr₁ ∙ SigStr= ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₁-ft (pr1 A B u) = ap ft pr1Str₁ ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₁-ft (pr2 A B u) = ap ft pr2Str₁ ∙ ft-star ∙ pr1Str₀ _ ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₁-ft (nat i) = ap ft natStr₁ ∙ UUStr=
⟦⟧Tm₁-ft zero = ap ft zeroStr₁ ∙ NatStr=
⟦⟧Tm₁-ft (suc u) = ap ft sucStr₁ ∙ NatStr= ∙ ⟦⟧Tm₀ u
--⟦⟧Tm₁-ft (nat-elim P d0 dS u) = ?
⟦⟧Tm₁-ft (id i a u v) = ap ft idStr₁ ∙ UUStr= ∙ ⟦⟧Tm₀ a
⟦⟧Tm₁-ft (refl A u) = ap ft reflStr₁ ∙ IdStr= ∙ ⟦⟧Tm₀ u

⟦⟧Mor₀ : {X : Ob n} {Y : Ob m} (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₀ (⟦ δ ⟧Mor X Y $ δᵈ) ≡ X
⟦⟧Mor₀ ◇ = ptmor₀
⟦⟧Mor₀ (δ , u) = comp₀ ∙ ⟦⟧Tm₀ u

⟦⟧Mor₁ : {X : Ob n} {Y : Ob m} (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₁ (⟦ δ ⟧Mor X Y $ δᵈ) ≡ Y
⟦⟧Mor₁ ◇ = ptmor₁ ∙ ! (pt-unique _)
⟦⟧Mor₁ (δ , u) = comp₁ ∙ qq₁
