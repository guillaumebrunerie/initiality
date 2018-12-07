{-# OPTIONS --rewriting --prop --without-K --allow-unsolved-metas #-}

open import common
open import syntx
open import contextualcat

module _ (C : StructuredCCat) where

open StructuredCCat C
open CCat ccat renaming (Mor to MorC; id to idC)

{- Partial interpretation of types and terms -}

⟦_⟧Ty : TyExpr n → (X : Ob n) → Partial (Ob (suc n))
⟦_⟧Tm : TmExpr n → (X : Ob n) → Partial (MorC n (suc n))

⟦ pi A B ⟧Ty X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  return (PiStr [B])
⟦ uu i ⟧Ty X = return (UUStr i X)
⟦ el i v ⟧Ty X = do
  [v] ← ⟦ v ⟧Tm X
  [v]ₛ ← assume (is-section [v])
  [v]₁ ← assume (∂₁ [v] ≡ UUStr i (∂₀ [v]))
  return (ElStr i [v] (unbox [v]ₛ) (unbox [v]₁))
⟦ sig A B ⟧Ty X = {!!}
⟦ nat ⟧Ty X = {!!}
⟦ id A u v ⟧Ty X = {!!}


⟦ var last ⟧Tm X = return (ss (idC X))
⟦ var (prev x) ⟧Tm X = do
  [x] ← ⟦ var x ⟧Tm (ft X)
  [x]₀ ← assume (∂₀ [x] ≡ ft X)
  return (ss (comp [x] (pp X) (pp₁ ∙ ! (unbox [x]₀))))
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
⟦ uu i ⟧Tm X = {!!}
⟦ pi i x x₁ ⟧Tm X = {!!}
⟦ sig i x x₁ ⟧Tm X = {!!}
⟦ pair A B x x₁ ⟧Tm X = {!!}
⟦ pr1 A B x ⟧Tm X = {!!}
⟦ pr2 A B x ⟧Tm X = {!!}
⟦ nat i ⟧Tm X = {!!}
⟦ zero ⟧Tm X = {!!}
⟦ suc x ⟧Tm X = {!!}
⟦ nat-elim P x x₁ x₂ ⟧Tm X = {!!}
⟦ id i x x₁ x₂ ⟧Tm X = {!!}
⟦ refl A x ⟧Tm X = {!!}

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
⟦⟧Tmₛ (var last) = ss-is-section
⟦⟧Tmₛ (var (prev x)) = ss-is-section
⟦⟧Tmₛ (lam A B u) = lamStrs
⟦⟧Tmₛ (app A B f a) = appStrs
⟦⟧Tmₛ (uu i) = uuStrₛ
⟦⟧Tmₛ (pi i u u₁) = piStrₛ
⟦⟧Tmₛ (sig i u u₁) = sigStrₛ
⟦⟧Tmₛ (pair A B u u₁) = {!pairStrₛ!}
⟦⟧Tmₛ (pr1 A B u) = {!pr1Strₛ!}
⟦⟧Tmₛ (pr2 A B u) = {!pr2Strₛ!}
⟦⟧Tmₛ (nat i) = {!natStrₛ!}
⟦⟧Tmₛ zero = {!zeroStrₛ!}
⟦⟧Tmₛ (suc u) = {!sucStrₛ!}
⟦⟧Tmₛ (nat-elim P u u₁ u₂) = {!nat-elimStrₛ!}
⟦⟧Tmₛ (id i u u₁ u₂) = {!idStrₛ!}
⟦⟧Tmₛ (refl A u) = {!reflStrₛ!}

⟦⟧Ty-ft : {X : Ob n} (A : TyExpr n) {Aᵈ : isDefined (⟦ A ⟧Ty X)} → ft (⟦ A ⟧Ty X $ Aᵈ) ≡ X
⟦⟧Tm₀ : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → ∂₀ (⟦ u ⟧Tm X $ uᵈ) ≡ X

⟦⟧Ty-ft (uu i) = UUStr=
⟦⟧Ty-ft (el i v) = ElStr= ∙ ⟦⟧Tm₀ v
⟦⟧Ty-ft (pi A B)  = PiStr= ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Ty-ft (sig A B) = SigStr= ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Ty-ft nat = NatStr=
⟦⟧Ty-ft (id A u v) = IdStr= ∙ {!!}

⟦⟧Tm₀ (var last) = ss₀ ∙ id₀
⟦⟧Tm₀ (var (prev x)) = ss₀ ∙ comp₀ ∙ pp₀
⟦⟧Tm₀ (lam A B u) = lamStr₀ (⟦⟧Tmₛ u) ∙ ap ft (⟦⟧Tm₀ u) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (app A B f a) = appStr₀ (⟦⟧Tmₛ a) _ ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (uu i) = ?
⟦⟧Tm₀ (pi i u u₁) = ?
⟦⟧Tm₀ (sig i u u₁) = ?
⟦⟧Tm₀ (pair A B u u₁) = ?
⟦⟧Tm₀ (pr1 A B u) = ?
⟦⟧Tm₀ (pr2 A B u) = ?
⟦⟧Tm₀ (nat i) = ?
⟦⟧Tm₀ zero = ?
⟦⟧Tm₀ (suc u) = ?
⟦⟧Tm₀ (nat-elim P u u₁ u₂) = ?
⟦⟧Tm₀ (id i u u₁ u₂) = ?
⟦⟧Tm₀ (refl A u) = ?

⟦⟧Tm₁-ft : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → ft (∂₁ (⟦ u ⟧Tm X $ uᵈ)) ≡ X
⟦⟧Tm₁-ft (var last) = ap ft ss₁ ∙ ft-star ∙ comp₀ ∙ id₀
⟦⟧Tm₁-ft (var (prev x)) = ap ft ss₁ ∙ ft-star ∙ comp₀ ∙ comp₀ ∙ pp₀
⟦⟧Tm₁-ft (lam A B u) {uᵈ = Aᵈ , _} = ap ft lamStr₁ ∙ PiStr= ∙ ap ft (⟦⟧Tm₁-ft u) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₁-ft (app A B f a) = ap ft appStr₁ ∙ ft-star ∙ ⟦⟧Tm₀ a
⟦⟧Tm₁-ft (uu i) = ?
⟦⟧Tm₁-ft (pi i u u₁) = ?
⟦⟧Tm₁-ft (sig i u u₁) = ?
⟦⟧Tm₁-ft (pair A B u u₁) = ?
⟦⟧Tm₁-ft (pr1 A B u) = ?
⟦⟧Tm₁-ft (pr2 A B u) = ?
⟦⟧Tm₁-ft (nat i) = ?
⟦⟧Tm₁-ft zero = ?
⟦⟧Tm₁-ft (suc u) = ?
⟦⟧Tm₁-ft (nat-elim P u u₁ u₂) = ?
⟦⟧Tm₁-ft (id i u u₁ u₂) = ?
⟦⟧Tm₁-ft (refl A u) = ?

⟦⟧Mor₀ : {X : Ob n} {Y : Ob m} (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₀ (⟦ δ ⟧Mor X Y $ δᵈ) ≡ X
⟦⟧Mor₀ ◇ = ptmor₀
⟦⟧Mor₀ (δ , u) = comp₀ ∙ ⟦⟧Tm₀ u

⟦⟧Mor₁ : {X : Ob n} {Y : Ob m} (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₁ (⟦ δ ⟧Mor X Y $ δᵈ) ≡ Y
⟦⟧Mor₁ ◇ = ptmor₁ ∙ ! (pt-unique _)
⟦⟧Mor₁ (δ , u) = comp₁ ∙ qq₁
