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


ap-irr-lamStr : {n : ℕ} {A A' : _} (A-eq : A ≡ A') {B B' : _} (B-eq : B ≡ B') {B= : _} {B=' : _} {u u' : _} (u-eq : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} → lamStr {n = n} A B B= u uₛ u₁ ≡ lamStr A' B' B=' u' uₛ' u₁'
ap-irr-lamStr refl refl refl = refl

ap-irr-appStr : {n : ℕ} {A A' : _} (A-eq : A ≡ A') {B B' : _} (B-eq : B ≡ B') {B= : _} {B=' : _} {f f' : _} (f-eq : f ≡ f') {fₛ : _} {fₛ' : _} {f₁ : _} {f₁' : _} {a a' : _} (a-eq : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} → appStr {n = n} A B B= f fₛ f₁ a aₛ a₁ ≡ appStr A' B' B=' f' fₛ' f₁' a' aₛ' a₁'
ap-irr-appStr refl refl refl refl = refl

ap-irr-piStr : {n : ℕ} {i : ℕ} {a a' : _} (a-eq : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} {b b' : _} (b-eq : b ≡ b') {bₛ : _} {bₛ' : _} {b₁ : _} {b₁' : _} → piStr {n = n} i a aₛ a₁ b bₛ b₁ ≡ piStr i a' aₛ' a₁' b' bₛ' b₁'
ap-irr-piStr refl refl = refl

ap-irr-sigStr : {n : ℕ} {i : ℕ} {a a' : _} (a-eq : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} {b b' : _} (b-eq : b ≡ b') {bₛ : _} {bₛ' : _} {b₁ : _} {b₁' : _} → sigStr {n = n} i a aₛ a₁ b bₛ b₁ ≡ sigStr i a' aₛ' a₁' b' bₛ' b₁'
ap-irr-sigStr refl refl = refl

ap-irr-pairStr : {n : ℕ} {A A' : _} (A-eq : A ≡ A') {B B' : _} (B-eq : B ≡ B') {B= : _} {B=' : _} {a a' : _} (a-eq : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} {b b' : _} (b-eq : b ≡ b') {bₛ : _} {bₛ' : _} {b₁ : _} {b₁' : _} → pairStr {n = n} A B B= a aₛ a₁ b bₛ b₁ ≡ pairStr A' B' B=' a' aₛ' a₁' b' bₛ' b₁'
ap-irr-pairStr refl refl refl refl = refl

ap-irr-pr1Str : {n : ℕ} {A A' : _} (A-eq : A ≡ A') {B B' : _} (B-eq : B ≡ B') {B= : _} {B=' : _} {u u' : _} (u-eq : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} → pr1Str {n = n} A B B= u uₛ u₁ ≡ pr1Str A' B' B=' u' uₛ' u₁'
ap-irr-pr1Str refl refl refl = refl

ap-irr-pr2Str : {n : ℕ} {A A' : _} (A-eq : A ≡ A') {B B' : _} (B-eq : B ≡ B') {B= : _} {B=' : _} {u u' : _} (u-eq : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} → pr2Str {n = n} A B B= u uₛ u₁ ≡ pr2Str A' B' B=' u' uₛ' u₁'
ap-irr-pr2Str refl refl refl = refl

ap-irr-natelimStr : {n : ℕ} {X X' : _} (X-eq : X ≡ X') {P P' : _} (P-eq : P ≡ P') {dO dO' : _} (dO-eq : dO ≡ dO') {dS dS' : _} (dS-eq : dS ≡ dS') {u u' : _} (u-eq : u ≡ u') → ∀ {P= P'=} → {dS₁ : T-dS₁ X P P= dS} {dS'₁ : T-dS₁ X' P' P'= dS'} → ∀ {dOₛ dO₁ dSₛ uₛ u₁ dO'ₛ dO'₁ dS'ₛ u'ₛ u'₁}
  → natelimStr {n = n} X P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁ ≡ natelimStr X' P' P'= dO' dO'ₛ dO'₁ dS' dS'ₛ dS'₁ u' u'ₛ u'₁
ap-irr-natelimStr refl refl refl refl refl = refl

ap-irr-idStr : {n : ℕ} {i : ℕ} {a a' : _} (a-eq : a ≡ a') {aₛ : _} {aₛ' : _} {a₁ : _} {a₁' : _} {u u' : _} (u-eq : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} {v v' : _} (v-eq : v ≡ v') {vₛ : _} {vₛ' : _} {v₁ : _} {v₁' : _} → idStr {n = n} i a aₛ a₁ u uₛ u₁ v vₛ v₁ ≡ idStr {n = n} i a' aₛ' a₁' u' uₛ' u₁' v' vₛ' v₁'
ap-irr-idStr refl refl refl = refl

ap-irr-reflStr : {n : ℕ} {a a' : _} (a-eq : a ≡ a') {u u' : _} (u-eq : u ≡ u') {uₛ : _} {uₛ' : _} {u₁ : _} {u₁' : _} → reflStr {n = n} a u uₛ u₁ ≡ reflStr {n = n} a' u' uₛ' u₁'
ap-irr-reflStr refl refl = refl


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
  [B]= ← assume (ft [B] ≡ [A])
  return (PiStr [A] [B] (unbox [B]=))
⟦ sig A B ⟧Ty X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  [B]= ← assume (ft [B] ≡ [A])
  return (SigStr [A] [B] (unbox [B]=))
⟦ nat ⟧Ty X = return (NatStr X)
⟦ id A u v ⟧Ty X = do
  [A] ← ⟦ A ⟧Ty X
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ [A])
  [v] ← ⟦ v ⟧Tm X
  [v]ₛ ← assume (is-section [v])
  [v]₁ ← assume (∂₁ [v] ≡ [A])
  return (IdStr [A] [u] (unbox [u]ₛ) (unbox [u]₁) [v] (unbox [v]ₛ) (unbox [v]₁))


⟦ var k ⟧Tm X = return (varC k X)
⟦ uu i ⟧Tm X = return (uuStr i X)
⟦ pi i a b ⟧Tm X = do
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ UUStr i (∂₀ [a]))
  [b] ← ⟦ b ⟧Tm (ElStr i [a] (unbox [a]ₛ) (unbox [a]₁))
  [b]ₛ ← assume (is-section [b])
  [b]₁ ← assume (∂₁ [b] ≡ UUStr i (ElStr i [a] (unbox [a]ₛ) (unbox [a]₁)))
  return (piStr i [a] (unbox [a]ₛ) (unbox [a]₁) [b] (unbox [b]ₛ) (unbox [b]₁))
⟦ lam A B u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  [B]= ← assume (ft [B] ≡ [A])
  [u] ← ⟦ u ⟧Tm [A]
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ [B])
  return (lamStr [A] [B] (unbox [B]=) [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ app A B f a ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  [B]= ← assume (ft [B] ≡ [A])
  [f] ← ⟦ f ⟧Tm X
  [f]ₛ ← assume (is-section [f])
  [f]₁ ← assume (∂₁ [f] ≡ PiStr [A] [B] (unbox [B]=))
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ [A])
  return (appStr [A] [B] (unbox [B]=) [f] (unbox [f]ₛ) (unbox [f]₁) [a] (unbox [a]ₛ) (unbox [a]₁))
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
  [B]= ← assume (ft [B] ≡ [A])
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ [A])
  [v] ← ⟦ v ⟧Tm X
  [v]ₛ ← assume (is-section [v])
  [v]₁ ← assume (∂₁ [v] ≡ star [u] [B] _)
  return (pairStr [A] [B] (unbox [B]=) [u] (unbox [u]ₛ) (unbox [u]₁) [v] (unbox [v]ₛ) (unbox [v]₁))
⟦ pr1 A B u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  [B]= ← assume (ft [B] ≡ [A])
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ SigStr [A] [B] (unbox [B]=))
  return (pr1Str [A] [B] (unbox [B]=) [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ pr2 A B u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [B] ← ⟦ B ⟧Ty [A]
  [B]= ← assume (ft [B] ≡ [A])
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ SigStr [A] [B] (unbox [B]=))
  return (pr2Str [A] [B] (unbox [B]=) [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ nat i ⟧Tm X = return (natStr i X)
⟦ zero ⟧Tm X = return (zeroStr X)
⟦ suc u ⟧Tm X = do
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ NatStr (∂₀ [u]))
  return (sucStr [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ natelim P dO dS u ⟧Tm X = do
  [P] ← ⟦ P ⟧Ty (NatStr X)
  [P]= ← assume (ft [P] ≡ NatStr X)
  [dO]  ← ⟦ dO ⟧Tm X
  [dO]ₛ ← assume (is-section [dO])
  [dO]₁ ← assume (∂₁ [dO] ≡ star (zeroStr X) [P] _)
  [dS]  ← ⟦ dS ⟧Tm [P]
  [dS]ₛ ← assume (is-section [dS])
  [dS]₁ ← assume (∂₁ [dS] ≡ star (pp [P])
                                 (star (sucStr (ss (idC (NatStr X))) ssₛ (ss₁' id₁ ∙ NatStrNat _ (! (comp₁ ∙ pp₁ ∙ NatStr=)) ∙ ap NatStr (comp₀ ∙ ! ss₀)))
                                       (star (qq (pp (NatStr X)) (NatStr X) pp₁)
                                             [P]
                                             (qq₁ ∙ ! (unbox [P]=)))
                                       (sucStr₁ ∙ ap NatStr (ss₀ ∙ id₀ ∙ ! pp₀) ∙ ! (NatStrNat _ (! NatStr= ∙ ! pp₁)) ∙ ! qq₀ ∙ ! ft-star))
                                 (pp₁ ∙ ! (ft-star ∙ sucStr₀ _ ∙ ss₀ ∙ id₀ ∙ ! (unbox [P]=))))
  [u]  ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ ft [P])
  return (natelimStr X [P] (unbox [P]=) [dO] (unbox [dO]ₛ) (unbox [dO]₁) [dS] (unbox [dS]ₛ) (unbox [dS]₁) [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ id i a u v ⟧Tm X = do
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ UUStr i (∂₀ [a]))
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ ElStr i [a] (unbox [a]ₛ) (unbox [a]₁))
  [v] ← ⟦ v ⟧Tm X
  [v]ₛ ← assume (is-section [v])
  [v]₁ ← assume (∂₁ [v] ≡ ElStr i [a] (unbox [a]ₛ) (unbox [a]₁))
  return (idStr i [a] (unbox [a]ₛ) (unbox [a]₁) [u] (unbox [u]ₛ) (unbox [u]₁) [v] (unbox [v]ₛ) (unbox [v]₁))
⟦ refl A u ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [u] ← ⟦ u ⟧Tm X
  [u]ₛ ← assume (is-section [u])
  [u]₁ ← assume (∂₁ [u] ≡ [A])
  return (reflStr [A] [u] (unbox [u]ₛ) (unbox [u]₁))
⟦ jj A P d a b p ⟧Tm X = do
  [A] ← ⟦ A ⟧Ty X
  [P] ← ⟦ P ⟧Ty (IdStr (star (pp (star (pp [A]) [A] pp₁)) (star (pp [A]) [A] pp₁) pp₁) (ss (pp (star (pp [A]) [A] pp₁))) ssₛ (ss₁' (pp₁ ∙ ft-star ∙ pp₀) ∙ star-comp pp₁) (ss (idC (star (pp [A]) [A] pp₁))) ssₛ (ss₁' id₁ ∙ ap2-irr star (id-left' pp₀) refl)) 
  [P]= ← assume (ft [P] ≡ _)
  [d] ← ⟦ d ⟧Tm [A]
  [d]ₛ ← assume (is-section [d])
  [d]₁ ← assume (∂₁ [d] ≡ T-d₁ [A] [P] (unbox [P]=) [d])
  [a] ← ⟦ a ⟧Tm X
  [a]ₛ ← assume (is-section [a])
  [a]₁ ← assume (∂₁ [a] ≡ [A])
  [b] ← ⟦ b ⟧Tm X
  [b]ₛ ← assume (is-section [b])
  [b]₁ ← assume (∂₁ [b] ≡ [A])
  [p] ← ⟦ p ⟧Tm X
  [p]ₛ ← assume (is-section [p])
  [p]₁ ← assume (∂₁ [p] ≡ IdStr [A] [a] (unbox [a]ₛ) (unbox [a]₁) [b] (unbox [b]ₛ) (unbox [b]₁))
  return (jjStr [A] [P] (unbox [P]=) [d] (unbox [d]ₛ) (unbox [d]₁) [a] (unbox [a]ₛ) (unbox [a]₁) [b] (unbox [b]ₛ) (unbox [b]₁) [p] (unbox [p]ₛ) (unbox [p]₁))

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
⟦⟧Tmₛ (natelim P d0 dS u) = natelimStrₛ
⟦⟧Tmₛ (id i a u v) = idStrₛ
⟦⟧Tmₛ (refl A u) = reflStrₛ
⟦⟧Tmₛ (jj A P d a b p) = jjStrₛ

⟦⟧Ty-ft : {X : Ob n} (A : TyExpr n) {Aᵈ : isDefined (⟦ A ⟧Ty X)} → ft (⟦ A ⟧Ty X $ Aᵈ) ≡ X
⟦⟧Tm₀ : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → ∂₀ (⟦ u ⟧Tm X $ uᵈ) ≡ X

⟦⟧Ty-ft (uu i) = UUStr=
⟦⟧Ty-ft (el i v) = ElStr= ∙ ⟦⟧Tm₀ v
⟦⟧Ty-ft (pi A B)  = PiStr= ∙ ⟦⟧Ty-ft A
⟦⟧Ty-ft (sig A B) = SigStr= ∙ ⟦⟧Ty-ft A
⟦⟧Ty-ft nat = NatStr=
⟦⟧Ty-ft (id A u v) = IdStr= ∙ ⟦⟧Ty-ft A

⟦⟧Tm₀ (var k) = varC₀ k _
⟦⟧Tm₀ (uu i) = uuStr₀ _
⟦⟧Tm₀ (pi i a b) = piStr₀ _ ∙ ⟦⟧Tm₀ a
⟦⟧Tm₀ (lam A B u) = lamStr₀ _ ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (app A B f a) = appStr₀ _ _ ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (sig i a b) = sigStr₀ _ ∙ ⟦⟧Tm₀ a
⟦⟧Tm₀ (pair A B u v) = pairStr₀ _ ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (pr1 A B u) = pr1Str₀ _ ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (pr2 A B u) = pr2Str₀ _ ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (nat i) = natStr₀ _
⟦⟧Tm₀ zero = zeroStr₀ _
⟦⟧Tm₀ (suc u) = sucStr₀ _ ∙ ⟦⟧Tm₀ u
⟦⟧Tm₀ (natelim P d0 dS u) = natelimStr₀ _ _ _
⟦⟧Tm₀ (id i a u v) = idStr₀ _ ∙ ⟦⟧Tm₀ a
⟦⟧Tm₀ (refl A u) = reflStr₀ _ ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (jj A P d a b p) = jjStr₀ _ ∙ ⟦⟧Ty-ft A

⟦⟧Tm₁-ft : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → ft (∂₁ (⟦ u ⟧Tm X $ uᵈ)) ≡ X
⟦⟧Tm₁-ft u = ! (is-section₀ (⟦⟧Tmₛ u) refl) ∙ ⟦⟧Tm₀ u

⟦⟧Mor₀ : {X : Ob n} {Y : Ob m} (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₀ (⟦ δ ⟧Mor X Y $ δᵈ) ≡ X
⟦⟧Mor₀ ◇ = ptmor₀
⟦⟧Mor₀ (δ , u) = comp₀ ∙ ⟦⟧Tm₀ u

⟦⟧Mor₁ : {X : Ob n} {Y : Ob m} (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₁ (⟦ δ ⟧Mor X Y $ δᵈ) ≡ Y
⟦⟧Mor₁ ◇ = ptmor₁ ∙ ! (pt-unique _)
⟦⟧Mor₁ (δ , u) = comp₁ ∙ qq₁
