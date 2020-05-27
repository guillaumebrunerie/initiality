{-# OPTIONS --rewriting --prop #-}

open import common  
open import typetheory
open import syntx
open import contextualcat

module _ (sC : StructuredCCat) where

open StructuredCCat sC
open CCat+ ccat renaming (Mor to MorC; id to idC)


{- Partial interpretation of types and terms -}

⟦_⟧Ty : TyExpr n → (X : Ob n) → Partial (Ob (suc n))
⟦_⟧Tm : TmExpr n → (X : Ob n) → Partial (MorC n (suc n))

⟦ uu i ⟧Ty X = return (UUStr i X)
⟦ el i v ⟧Ty X = do
  [v] ← ⟦ v ⟧Tm X
  [v]ₛ ← assume (is-section [v])
  [v]₁ ← assume (∂₁ [v] ≡ UUStr i X)
  return (ElStr i X [v] (unbox [v]ₛ) (unbox [v]₁))
⟦ sum A B ⟧Ty X = do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [B] ← ⟦ B ⟧Ty X
  [B]= ← assume (ft [B] ≡ X)
  return (SumStr X [A] (unbox [A]=) [B] (unbox [B]=))
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
⟦ empty ⟧Ty X = return (EmptyStr X)
⟦ unit ⟧Ty X = return (UnitStr X)
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
⟦ sum i a b ⟧Tm X = do
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ UUStr i X)
  [b] ← ⟦ b ⟧Tm X
  [b]ₛ ← assume (is-section [b])
  [b]₁ ← assume (∂₁ [b] ≡ UUStr i X)
  return (sumStr i X [a] (unbox [a]ₛ) (unbox [a]₁) [b] (unbox [b]ₛ) (unbox [b]₁))
⟦ inl A B a ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [B] ← ⟦ B ⟧Ty X
  [B]= ← assume (ft [B] ≡ X)
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ [A])
  return (inlStr X [A] (unbox [A]=) [B] (unbox [B]=) [a] (unbox [a]ₛ) (unbox [a]₁))
⟦ inr A B b ⟧Tm X =  do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [B] ← ⟦ B ⟧Ty X
  [B]= ← assume (ft [B] ≡ X)
  [b] ← ⟦ b ⟧Tm X
  [b]ₛ ← assume (is-section [b])
  [b]₁ ← assume (∂₁ [b] ≡ [B])
  return (inrStr X [A] (unbox [A]=) [B] (unbox [B]=) [b] (unbox [b]ₛ) (unbox [b]₁))
⟦ match A B C da db u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [B] ← ⟦ B ⟧Ty X
  [B]= ← assume (ft [B] ≡ X)
  [C] ← ⟦ C ⟧Ty (SumStr X [A] (unbox [A]=) [B] (unbox [B]=))
  [C]= ← assume (ft [C] ≡ SumStr X [A] (unbox [A]=) [B] (unbox [B]=))
  [da] ← ⟦ da ⟧Tm [A]
  [da]ₛ ← assume (is-section [da])
  [da]₁ ← assume (∂₁ [da] ≡ T-da₁ X [A] (unbox [A]=) [B] (unbox [B]=) [C] (unbox [C]=))
  [db] ← ⟦ db ⟧Tm [B]
  [db]ₛ ← assume (is-section [db])
  [db]₁ ← assume (∂₁ [db] ≡ T-db₁ X [A] (unbox [A]=) [B] (unbox [B]=) [C] (unbox [C]=))
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ SumStr X [A] (unbox [A]=) [B] (unbox [B]=))
  return (matchStr X [A] (unbox [A]=) [B] (unbox [B]=) [C] (unbox [C]=) [da] (unbox [da]ₛ) (unbox [da]₁) [db] (unbox [db]ₛ) (unbox [db]₁) [u] (unbox [u]ₛ) (unbox [u]₁))
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
⟦ empty i ⟧Tm X = return (emptyStr i X)
⟦ emptyelim A u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty (EmptyStr X)
  [A]= ← assume (ft [A] ≡ EmptyStr X)
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ EmptyStr X)
  return (emptyelimStr X [A] (unbox [A]=) [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ unit i ⟧Tm X = return (unitStr i X)
⟦ tt ⟧Tm X = return (ttStr X)
⟦ unitelim A dtt u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty (UnitStr X)
  [A]= ← assume (ft [A] ≡ UnitStr X)
  [dtt] ← ⟦ dtt ⟧Tm X
  [dtt]ₛ ← assume (is-section [dtt])
  [dtt]₁ ← assume (∂₁ [dtt] ≡ star (ttStr X) [A] (unbox [A]=) ttStr₁)
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ UnitStr X)
  return (unitelimStr X [A] (unbox [A]=) [dtt] (unbox [dtt]ₛ) (unbox [dtt]₁) [u] (unbox [u]ₛ) (unbox [u]₁))
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
  [dO]₁ ← assume (∂₁ [dO] ≡ star (zeroStr X) [P] (unbox [P]=) zeroStr₁)
  [dS]  ← ⟦ dS ⟧Tm [P]
  [dS]ₛ ← assume (is-section [dS])
  [dS]₁ ← assume (∂₁ [dS] ≡ T-dS₁ X [P] (unbox [P]=))
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
⟦ jj A P d a b p ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [A]= ← assume (ft [A] ≡ X)
  [P] ← ⟦ P ⟧Ty (T-ftP X [A] (unbox [A]=))
  [P]= ← assume (ft [P] ≡ _)
  [d] ← ⟦ d ⟧Tm [A]
  [d]ₛ ← assume (is-section [d])
  [d]₁ ← assume (∂₁ [d] ≡ _)
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ [A])
  [b] ← ⟦ b ⟧Tm X
  [b]ₛ ← assume (is-section [b])
  [b]₁ ← assume (∂₁ [b] ≡ [A])
  [p] ← ⟦ p ⟧Tm X
  [p]ₛ ← assume (is-section [p])
  [p]₁ ← assume (∂₁ [p] ≡ IdStr X [A] (unbox [A]=) [a] (unbox [a]ₛ) (unbox [a]₁) [b] (unbox [b]ₛ) (unbox [b]₁))
  return (jjStr X [A] (unbox [A]=) [P] (unbox [P]=) [d] (unbox [d]ₛ) (unbox [d]₁) [a] (unbox [a]ₛ) (unbox [a]₁) [b] (unbox [b]ₛ) (unbox [b]₁) [p] (unbox [p]ₛ) (unbox [p]₁))

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
⟦⟧Tmₛ (sum i a b) = sumStrₛ
⟦⟧Tmₛ (inl A B a) = inlStrₛ
⟦⟧Tmₛ (inr A B b) = inrStrₛ
⟦⟧Tmₛ (match A B C da db u) = matchStrₛ
⟦⟧Tmₛ (pi i a b) = piStrₛ
⟦⟧Tmₛ (lam A B u) = lamStrₛ
⟦⟧Tmₛ (app A B f a) = appStrₛ
⟦⟧Tmₛ (sig i a b) = sigStrₛ
⟦⟧Tmₛ (pair A B u v) = pairStrₛ
⟦⟧Tmₛ (pr1 A B u) = pr1Strₛ
⟦⟧Tmₛ (pr2 A B u) = pr2Strₛ
⟦⟧Tmₛ (empty i) = emptyStrₛ
⟦⟧Tmₛ (emptyelim A u) = emptyelimStrₛ
⟦⟧Tmₛ (unit i) = unitStrₛ
⟦⟧Tmₛ tt = ttStrₛ
⟦⟧Tmₛ (unitelim A dtt u) = unitelimStrₛ
⟦⟧Tmₛ (nat i) = natStrₛ
⟦⟧Tmₛ zero = zeroStrₛ
⟦⟧Tmₛ (suc u) = sucStrₛ
⟦⟧Tmₛ (natelim P d0 dS u) = natelimStrₛ
⟦⟧Tmₛ (id i a u v) = idStrₛ
⟦⟧Tmₛ (refl A u) = reflStrₛ
⟦⟧Tmₛ (jj A P d a b p) = jjStrₛ

⟦⟧Ty-ft : {X : Ob n} (A : TyExpr n) {Aᵈ : isDefined (⟦ A ⟧Ty X)} → ft (⟦ A ⟧Ty X $ Aᵈ) ≡ X
⟦⟧Ty-ft (uu i) = UUStr=
⟦⟧Ty-ft (el i v) = ElStr=
⟦⟧Ty-ft (sum A B) = SumStr=
⟦⟧Ty-ft (pi A B)  = PiStr=
⟦⟧Ty-ft (sig A B) = SigStr=
⟦⟧Ty-ft empty = EmptyStr=
⟦⟧Ty-ft unit = UnitStr=
⟦⟧Ty-ft nat = NatStr=
⟦⟧Ty-ft (id A u v) = IdStr=

⟦⟧Tm₀ : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → ∂₀ (⟦ u ⟧Tm X $ uᵈ) ≡ X
⟦⟧Tm₀ (var k) = varC₀
⟦⟧Tm₀ (uu i) = uuStr₀
⟦⟧Tm₀ (sum i a b) = sumStr₀
⟦⟧Tm₀ (inl A B a) = inlStr₀
⟦⟧Tm₀ (inr A B b) = inrStr₀
⟦⟧Tm₀ (match A B C da db u) = matchStr₀
⟦⟧Tm₀ (pi i a b) = piStr₀
⟦⟧Tm₀ (lam A B u) = lamStr₀
⟦⟧Tm₀ (app A B f a) = appStr₀
⟦⟧Tm₀ (sig i a b) = sigStr₀
⟦⟧Tm₀ (pair A B u v) = pairStr₀
⟦⟧Tm₀ (pr1 A B u) = pr1Str₀
⟦⟧Tm₀ (pr2 A B u) = pr2Str₀
⟦⟧Tm₀ (empty i) = emptyStr₀
⟦⟧Tm₀ (emptyelim A u) = emptyelimStr₀
⟦⟧Tm₀ (unit i) = unitStr₀
⟦⟧Tm₀ tt = ttStr₀
⟦⟧Tm₀ (unitelim A dtt u) = unitelimStr₀
⟦⟧Tm₀ (nat i) = natStr₀
⟦⟧Tm₀ zero = zeroStr₀
⟦⟧Tm₀ (suc u) = sucStr₀
⟦⟧Tm₀ (natelim P d0 dS u) = natelimStr₀
⟦⟧Tm₀ (id i a u v) = idStr₀
⟦⟧Tm₀ (refl A u) = reflStr₀
⟦⟧Tm₀ (jj A P d a b p) = jjStr₀

⟦⟧Tm₁-ft : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} {Z : Ob (suc n)} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ Z) → ft Z ≡ X
⟦⟧Tm₁-ft u u₁ = ap ft (! u₁) ∙ ! (is-section₀ (⟦⟧Tmₛ u) refl) ∙ ⟦⟧Tm₀ u

⟦⟧Mor₀ : {X : Ob n} {Y : Ob m} (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₀ (⟦ δ ⟧Mor X Y $ δᵈ) ≡ X
⟦⟧Mor₀ ◇ = ptmor₀
⟦⟧Mor₀ (δ , u) = comp₀ ∙ ⟦⟧Tm₀ u

⟦⟧Mor₁ : {X : Ob n} {Y : Ob m} (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₁ (⟦ δ ⟧Mor X Y $ δᵈ) ≡ Y
⟦⟧Mor₁ ◇ = ptmor₁ ∙ ! (pt-unique _)
⟦⟧Mor₁ (δ , u) = comp₁ ∙ qq₁



{- Transport along the various partial interpretation functions -}

cong⟦⟧Tyᵈ : {X Y : Ob n} {A : TyExpr n} → X ≡ Y → isDefined (⟦ A ⟧Ty Y) → isDefined (⟦ A ⟧Ty X)
cong⟦⟧Tyᵈ refl Aᵈ = Aᵈ

cong⟦⟧TyEq : {X Y : Ob n} {A : TyExpr n} (p : X ≡ Y) (w₁ : _) → ⟦ A ⟧Ty Y $ w₁ ≡ ⟦ A ⟧Ty X $ (cong⟦⟧Tyᵈ {A = A} p w₁)
cong⟦⟧TyEq refl _ = refl

congTyEq⟦⟧Tyᵈ : {X : Ob n} {A B : TyExpr n} → A ≡ B → isDefined (⟦ A ⟧Ty X) → isDefined (⟦ B ⟧Ty X)
congTyEq⟦⟧Tyᵈ refl Aᵈ = Aᵈ

congTyEq⟦⟧Ty= : {X : Ob n} {A B : TyExpr n} (p : A ≡ B) (w₁ : _) → ⟦ A ⟧Ty X $ w₁ ≡ ⟦ B ⟧Ty X $ (congTyEq⟦⟧Tyᵈ {A = A} p w₁)
congTyEq⟦⟧Ty= refl _ = refl

cong⟦⟧Mor : {X : Ob n} {Y Y' : Ob m} {δ : Mor n m} → Y ≡ Y' → isDefined (⟦ δ ⟧Mor X Y) → isDefined (⟦ δ ⟧Mor X Y')
cong⟦⟧Mor refl δᵈ = δᵈ

cong⟦⟧MorEq : {X : Ob n} {Y Y' : Ob m} {δ : Mor n m} {w₁ : _} (p : Y ≡ Y') → ⟦ δ ⟧Mor X Y $ w₁ ≡ ⟦ δ ⟧Mor X Y' $ cong⟦⟧Mor {δ = δ} p w₁
cong⟦⟧MorEq refl = refl
