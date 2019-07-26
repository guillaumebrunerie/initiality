{-# OPTIONS --rewriting --prop --without-K --no-auto-inline #-}

open import common
open import contextualcat

{- Morphisms of contextual categories -}

record CCatMor (C D : CCat) : Set where
  open CCat+
  field
    Ob→ : Ob C n → Ob D n
    Mor→ : Mor C n m → Mor D n m
    ∂₀→ : {X : Mor C n m} → Ob→ (∂₀ C X) ≡ ∂₀ D (Mor→ X)
    ∂₁→ : {X : Mor C n m} → Ob→ (∂₁ C X) ≡ ∂₁ D (Mor→ X)
    id→ : {X : Ob C n} → Mor→ (id C X) ≡ id D (Ob→ X)
    comp→ : {n m k : ℕ} {g : Mor C m k} {f : Mor C n m} {X : Ob C m} {g₀ : ∂₀ C g ≡ X} {f₁ : ∂₁ C f ≡ X} → Mor→ (comp C g f g₀ f₁) ≡ comp D (Mor→ g) (Mor→ f) (! ∂₀→ ∙ ap Ob→ g₀) (! ∂₁→ ∙ ap Ob→ f₁)
    ft→ : {X : Ob C (suc n)} → Ob→ (ft C X) ≡ ft D (Ob→ X)
    pp→ : {X : Ob C (suc n)} → Mor→ (pp C X) ≡ pp D (Ob→ X)
    star→ : {n m : ℕ} {f : Mor C m n} {X : Ob C (suc n)} {Y : Ob C n} {q : ft C X ≡ Y} {f₁ : ∂₁ C f ≡ Y} → Ob→ (star C f X q f₁) ≡ star D (Mor→ f) (Ob→ X) (! ft→ ∙ ap Ob→ q) (! ∂₁→ ∙ ap Ob→ f₁)
    qq→ : {n m : ℕ} {f : Mor C m n} {X : Ob C (suc n)} {Y : Ob C n} {q : ft C X ≡ Y} {f₁ : ∂₁ C f ≡ Y} → Mor→ (qq C f X q f₁) ≡ qq D (Mor→ f) (Ob→ X) (! ft→ ∙ ap Ob→ q) (! ∂₁→ ∙ ap Ob→ f₁)
    ss→ : {f : Mor C m (suc n)} → Mor→ (ss C f) ≡ ss D (Mor→ f)
    pt→ : Ob→ (pt C) ≡ pt D
    ptmor→ : {X : Ob C n} → Mor→ (ptmor C X) ≡ ptmor D (Ob→ X)

  Mor→ₛ : {n : ℕ} {u : Mor C n (suc n)} (uₛ : is-section C u) → is-section D (Mor→ u)
  Mor→ₛ uₛ = is-section→ D (! (comp→ ∙ ap-irr-comp D (pp→ ∙ ap (pp D) ∂₁→) refl) ∙ ap Mor→ (is-section= C (! (is-section₀ C uₛ refl)) uₛ refl) ∙ id→ ∙ ap (id D) ∂₀→)

  Mor→₁ : {n : ℕ} {u : Mor C n (suc n)} {X : Ob C (suc n)} (u₁ : ∂₁ C u ≡ X) → ∂₁ D (Mor→ u) ≡ Ob→ X
  Mor→₁ u₁ = ! ∂₁→ ∙ ap Ob→ u₁


{- Morphisms of structured contextual categories -}

record StructuredCCatMor (sC sD : StructuredCCat) : Set where
  private
    open StructuredCCat
    C = ccat sC
    D = ccat sD

  field
    ccat→ : CCatMor C D

  open CCatMor ccat→
  open CCat+

  field
    UUStr→ : {n : ℕ} (i : ℕ) (Γ : Ob C n) → Ob→ (UUStr sC i Γ) ≡ UUStr sD i (Ob→ Γ)
    ElStr→ : (i : ℕ) (Γ : Ob C n) (v : Mor C n (suc n)) (vₛ : is-section C v) (v₁ : ∂₁ C v ≡ UUStr sC i Γ)
           → Ob→ (ElStr sC i Γ v vₛ v₁) ≡ ElStr sD i (Ob→ Γ) (Mor→ v) (Mor→ₛ vₛ) (Mor→₁ v₁ ∙ UUStr→ i Γ)
    PiStr→  : (Γ : Ob C n) (A : Ob C (suc n)) (A= : ft C A ≡ Γ) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) → Ob→ (PiStr sC Γ A A= B B=) ≡ PiStr sD (Ob→ Γ) (Ob→ A) (! ft→ ∙ ap Ob→ A=) (Ob→ B) (! ft→ ∙ ap Ob→ B=)
    SigStr→ : (Γ : Ob C n) (A : Ob C (suc n)) (A= : ft C A ≡ Γ) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) → Ob→ (SigStr sC Γ A A= B B=) ≡ SigStr sD (Ob→ Γ) (Ob→ A)(! ft→ ∙ ap Ob→ A=) (Ob→ B) (! ft→ ∙ ap Ob→ B=)
    NatStr→ : (Γ : Ob C n) → Ob→ (NatStr sC Γ) ≡ NatStr sD (Ob→ Γ)
    IdStr→  : (Γ : Ob C n) (A : Ob C (suc n)) (A= : ft C A ≡ Γ) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ A) (b : Mor C n (suc n)) (bₛ : is-section C b) (b₁ : ∂₁ C b ≡ A)
            → Ob→ (IdStr sC Γ A A= a aₛ a₁ b bₛ b₁) ≡ IdStr sD (Ob→ Γ) (Ob→ A) (! ft→ ∙ ap Ob→ A=) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁)


    uuStr→ : (i : ℕ) (Γ : Ob C n)
            → Mor→ (uuStr sC i Γ) ≡ uuStr sD i (Ob→ Γ)
    piStr→ : (i : ℕ) (Γ : Ob C n) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ UUStr sC i Γ) (b : Mor C (suc n) (suc (suc n))) (bₛ : is-section C b) (b₁ : ∂₁ C b ≡ UUStr sC i (ElStr sC i Γ a aₛ a₁))
            → Mor→ (piStr sC i Γ a aₛ a₁ b bₛ b₁) ≡ piStr sD i (Ob→ Γ) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ UUStr→ i Γ) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁ ∙ UUStr→ i (ElStr sC i Γ a aₛ a₁) ∙ ap (UUStr sD i) (ElStr→ i Γ a aₛ a₁))
    lamStr→ : (Γ : Ob C n) (A : Ob C (suc n)) (A= : ft C A ≡ Γ) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (u : Mor C (suc n) (suc (suc n))) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ B)
            → Mor→ (lamStr sC Γ A A= B B= u uₛ u₁) ≡ lamStr sD (Ob→ Γ) (Ob→ A) (! ft→ ∙ ap Ob→ A=) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁)
    appStr→ : (Γ : Ob C n) (A : Ob C (suc n)) (A= : ft C A ≡ Γ) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (f : Mor C n (suc n)) (fₛ : is-section C f) (f₁ : ∂₁ C f ≡ PiStr sC Γ A A= B B=) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ A)
            → Mor→ (appStr sC Γ A A= B B= f fₛ f₁ a aₛ a₁) ≡ appStr sD (Ob→ Γ) (Ob→ A) (! ft→ ∙ ap Ob→ A=) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ f) (Mor→ₛ fₛ) (Mor→₁ f₁ ∙ PiStr→ Γ A A= B B=) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁)
    sigStr→ : (i : ℕ) (Γ : Ob C n) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ UUStr sC i Γ) (b : Mor C (suc n) (suc (suc n))) (bₛ : is-section C b) (b₁ : ∂₁ C b ≡ UUStr sC i (ElStr sC i Γ a aₛ a₁))
            → Mor→ (sigStr sC i Γ a aₛ a₁ b bₛ b₁) ≡ sigStr sD i (Ob→ Γ) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ UUStr→ i Γ) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁ ∙ UUStr→ i (ElStr sC i Γ a aₛ a₁) ∙ ap (UUStr sD i) (ElStr→ i Γ a aₛ a₁))
    pairStr→ : (Γ : Ob C n) (A : Ob C (suc n)) (A= : ft C A ≡ Γ) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ A) (b : Mor C n (suc n)) (bₛ : is-section C b) (b₁ : ∂₁ C b ≡ star C a B B= a₁)
            → Mor→ (pairStr sC Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ pairStr sD (Ob→ Γ) (Ob→ A) (! ft→ ∙ ap Ob→ A=) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁) (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁ ∙ star→)
    pr1Str→ : (Γ : Ob C n) (A : Ob C (suc n)) (A= : ft C A ≡ Γ) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (u : Mor C n (suc n)) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ SigStr sC Γ A A= B B=)
            → Mor→ (pr1Str sC Γ A A= B B= u uₛ u₁) ≡ pr1Str sD (Ob→ Γ) (Ob→ A) (! ft→ ∙ ap Ob→ A=) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ SigStr→ Γ A A= B B=)
    pr2Str→ : (Γ : Ob C n) (A : Ob C (suc n)) (A= : ft C A ≡ Γ) (B : Ob C (suc (suc n))) (B= : ft C B ≡ A) (u : Mor C n (suc n)) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ SigStr sC Γ A A= B B=)
            → Mor→ (pr2Str sC Γ A A= B B= u uₛ u₁) ≡ pr2Str sD (Ob→ Γ) (Ob→ A) (! ft→ ∙ ap Ob→ A=) (Ob→ B) (! ft→ ∙ ap Ob→ B=) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ SigStr→ Γ A A= B B=)
    natStr→ : (i : ℕ) (Γ : Ob C n)
            → Mor→ (natStr sC i Γ) ≡ natStr sD i (Ob→ Γ)
    zeroStr→ : (Γ : Ob C n)
            → Mor→ (zeroStr sC Γ) ≡ zeroStr sD (Ob→ Γ)
    sucStr→ : (Γ : Ob C n) (u : Mor C n (suc n)) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ NatStr sC Γ)
            → Mor→ (sucStr sC Γ u uₛ u₁) ≡ sucStr sD (Ob→ Γ) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ NatStr→ Γ)
    idStr→ : (i : ℕ) (Γ : Ob C n) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ UUStr sC i Γ) (u : Mor C n (suc n)) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ ElStr sC i Γ a aₛ a₁)
                     (v : Mor C n (suc n)) (vₛ : is-section C v) (v₁ : ∂₁ C v ≡ ElStr sC i Γ a aₛ a₁)
            → Mor→ (idStr sC i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ idStr sD i (Ob→ Γ) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁ ∙ UUStr→ i Γ) (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ ElStr→ i Γ a aₛ a₁) (Mor→ v) (Mor→ₛ vₛ) (Mor→₁ v₁ ∙ ElStr→ i Γ a aₛ a₁)
    reflStr→ : (Γ : Ob C n) (A : Ob C (suc n)) (A= : ft C A ≡ Γ) (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ A)
            → Mor→ (reflStr sC Γ A A= a aₛ a₁) ≡ reflStr sD (Ob→ Γ) (Ob→ A) (! ft→ ∙ ap Ob→ A=) (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁)

  abstract
    T-dS→ : {Γ : Ob C n} {P : Ob C (suc (suc n))} {P= : ft C P ≡ NatStr sC Γ} → Ob→ (T-dS₁ sC Γ P P=) ≡ T-dS₁ sD (Ob→ Γ) (Ob→ P) (! ft→ ∙ ap Ob→ P= ∙ NatStr→ Γ)
    T-dS→ {_} {Γ} {P} {P=} =
      star→ ∙ ap-irr-star D (sucStr→ _ _ _ _ ∙ ap-irr-sucStr sD refl (ss→ ∙ ap (ss D) pp→))
                            (star→ ∙ ap-irr-star D (qq→ ∙ ap-irr-qq D pp→ (star→ ∙ ap-irr-star D (pp→ ∙ ap (pp D) (NatStr→ Γ)) (NatStr→ Γ)))
                                                   (star→ ∙ ap-irr-star D (qq→ ∙ ap-irr-qq D (pp→ ∙ ap (pp D) (NatStr→ Γ)) (NatStr→ Γ)) refl))

    T-ftP→ : {Γ : Ob C n} {A : Ob C (suc n)} {A= : ft C A ≡ Γ} → Ob→ (T-ftP sC Γ A A=) ≡ T-ftP sD (Ob→ Γ) (Ob→ A) (! ft→ ∙ ap Ob→ A=)
    T-ftP→ {_} {Γ} {A} {A=} = IdStr→ (star C (pp C A) A A= (pp₁ C ∙ A=))
                                     (star C (pp C (star C (pp C A) A A= (pp₁ C ∙ A=))) (star C (pp C A) A A= (pp₁ C ∙ A=)) (ft-star C ∙ pp₀ C) (pp₁ C ∙ ft-star C ∙ pp₀ C))
                                     (ft-star C ∙ pp₀ C)
                                     (varC C (prev last) (star C (pp C A) A A= (pp₁ C ∙ A=)))
                                     (varCₛ C (prev last) (star C (pp C A) A A= (pp₁ C ∙ A=)))
                                     (varC+₁ C last (ft-star C ∙ pp₀ C) (varCL₁ C) )
                                     (varC C last (star C (pp C A) A A= (pp₁ C ∙ A=)))
                                     (varCₛ C last (star C (pp C A) A A= (pp₁ C ∙ A=)))
                                     (varCL₁ C) ∙
                              ap-irr-IdStr sD (star→ ∙ ap-irr-star D pp→ refl)
                                              (star→ ∙ ap-irr-star D (pp→ ∙ ap (pp D) (star→ ∙ ap-irr-star D pp→ refl)) (star→ ∙ ap-irr-star D pp→ refl))
                                              (ss→ ∙ ap (ss D) (pp→ ∙ ap (pp D) (star→ ∙ ap-irr-star D pp→ refl)))
                                              (ss→ ∙ ap (ss D) (id→ ∙ ap (id D) (star→ ∙ ap-irr-star D pp→ refl)))


    T-d₁→ : {Γ : Ob C n} {A : Ob C (suc n)} {A= : ft C A ≡ Γ} {P : Ob C (suc (suc (suc (suc n))))} {P= : ft C P ≡ T-ftP sC Γ A A=} →
            Ob→ (T-d₁ sC Γ A A= P P=) ≡ T-d₁ sD (Ob→ Γ) (Ob→ A) (! ft→ ∙ ap Ob→ A=) (Ob→ P) (! ft→ ∙ ap Ob→ P= ∙ T-ftP→)
    T-d₁→ {_} {Γ} {A} {A=} {P} {P=} =
      star→ ∙ ap-irr-star D
        (reflStr→ A (star C (pp C A) A A= (pp₁ C ∙ A=)) (ft-star C ∙ pp₀ C)
                    (varC C last A) (varCₛ C last A) (varCL₁ C)
         ∙ ap-irr-reflStr sD refl
           (star→ ∙ ap-irr-star D pp→ refl)
           (ss→ ∙ ap (ss D) id→))
        (star→ ∙ ap-irr-star D
          (qq→ ∙ ap-irr-qq D
            (ss→ ∙ ap (ss D) id→)
            (star→ ∙ ap-irr-star D
              (qq→ ∙ ap-irr-qq D
                (ss→ ∙ ap (ss D) id→)
                (star→ ∙ ap-irr-star D
                  (qq→ ∙ ap-irr-qq D pp→ refl)
                  (star→ ∙ ap-irr-star D pp→ refl)))
              (star→ ∙ ap-irr-star D
                (qq→ ∙ ap-irr-qq D
                  (qq→ ∙ ap-irr-qq D pp→ refl)
                  (star→ ∙ ap-irr-star D pp→ refl))
                T-ftP→)))
          (star→ ∙ ap-irr-star D
            (qq→ ∙ ap-irr-qq D
              (qq→ ∙ ap-irr-qq D
                (ss→ ∙ ap (ss D) id→)
                (star→ ∙ ap-irr-star D
                  (qq→ ∙ ap-irr-qq D pp→ refl)
                  (star→ ∙ ap-irr-star D pp→ refl)))
              (star→ ∙ ap-irr-star D
                (qq→ ∙ ap-irr-qq D
                  (qq→ ∙ ap-irr-qq D pp→ refl)
                  (star→ ∙ ap-irr-star D pp→ refl))
                T-ftP→))
            (star→ ∙ ap-irr-star D
              (qq→ ∙ ap-irr-qq D
                (qq→ ∙ ap-irr-qq D
                  (qq→ ∙ ap-irr-qq D pp→ refl)
                  (star→ ∙ ap-irr-star D pp→ refl))
                T-ftP→)
              refl)))


record StructuredCCatMor+ (sC sD : StructuredCCat) : Set where
  private
    open StructuredCCat
    C = ccat sC
    D = ccat sD


  field
    strucCCat→ : StructuredCCatMor sC sD

  open StructuredCCatMor strucCCat→
  open CCatMor ccat→
  open CCat+

  field
    natelimStr→ : (Γ : Ob C n) (P : Ob C (suc (suc n))) (P= : ft C P ≡ NatStr sC Γ)
                  (dO : Mor C n (suc n)) (dOₛ : is-section C dO) (dO₁ : ∂₁ C dO ≡ star C (zeroStr sC Γ) P P= (zeroStr₁ sC))
                  (dS : Mor C (suc (suc n)) (suc (suc (suc n)))) (dSₛ : is-section C dS) (dS₁ : ∂₁ C dS ≡ T-dS₁ sC Γ P P=)
                  (u : Mor C n (suc n)) (uₛ : is-section C u) (u₁ : ∂₁ C u ≡ NatStr sC Γ)
            → Mor→ (natelimStr sC Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)
              ≡ natelimStr sD (Ob→ Γ) (Ob→ P) (! ft→ ∙ ap Ob→ P= ∙ NatStr→ Γ)
                              (Mor→ dO) (Mor→ₛ dOₛ) (Mor→₁ dO₁ ∙ star→ ∙ ap-irr-star D (zeroStr→ Γ) refl)
                              (Mor→ dS) (Mor→ₛ dSₛ) (Mor→₁ dS₁ ∙ T-dS→)
                              (Mor→ u) (Mor→ₛ uₛ) (Mor→₁ u₁ ∙ NatStr→ Γ)

  field
    jjStr→ : (Γ : Ob C n) (A : Ob C (suc n)) (A= : ft C A ≡ Γ) (P : Ob C (suc (suc (suc (suc n)))))
             (P= : ft C P ≡ T-ftP sC Γ A A=)
             (d : Mor C (suc n) (suc (suc n))) (dₛ : is-section C d)
             (d₁ : ∂₁ C d ≡ T-d₁ sC Γ A A= P P=)
             (a : Mor C n (suc n)) (aₛ : is-section C a) (a₁ : ∂₁ C a ≡ A)
             (b : Mor C n (suc n)) (bₛ : is-section C b) (b₁ : ∂₁ C b ≡ A)
             (p : Mor C n (suc n)) (pₛ : is-section C p) (p₁ : ∂₁ C p ≡ IdStr sC Γ A A= a aₛ a₁ b bₛ b₁)
             → Mor→ (jjStr sC Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁) ≡ jjStr sD (Ob→ Γ) (Ob→ A) (! ft→ ∙ ap Ob→ A=) (Ob→ P)
                                                                                      (! ft→ ∙ ap Ob→ P= ∙ T-ftP→)
                                                                                      (Mor→ d) (Mor→ₛ dₛ) (Mor→₁ d₁ ∙ T-d₁→)
                                                                                      (Mor→ a) (Mor→ₛ aₛ) (Mor→₁ a₁)
                                                                                      (Mor→ b) (Mor→ₛ bₛ) (Mor→₁ b₁)
                                                                                      (Mor→ p) (Mor→ₛ pₛ) (Mor→₁ p₁ ∙ IdStr→ Γ A A= a aₛ a₁ b bₛ b₁)


module _ {sC sD : StructuredCCat} where
  open StructuredCCatMor+
  open StructuredCCatMor
  open StructuredCCat
  open CCatMor
  open CCat

  {- Equalities between morphisms between structured contextual categories -}

  structuredCCatMorEq : {f g : StructuredCCatMor sC sD}
                      → ({n : ℕ} (X : Ob (ccat sC) n) → Ob→ (ccat→ f) X ≡ Ob→ (ccat→ g) X)
                      → ({n m : ℕ} (X : Mor (ccat sC) n m) → Mor→ (ccat→ f) X ≡ Mor→ (ccat→ g) X)
                      → f ≡ g
  structuredCCatMorEq h k = lemma (funextI (λ n → funext h)) (funextI (λ m → funextI (λ n → funext k)))  where

    lemma : {f g : StructuredCCatMor sC sD}
            → ((λ {n} → Ob→ (ccat→ f) {n}) ≡ (λ {n} → Ob→ (ccat→ g) {n}))
            → ((λ {n m} → Mor→ (ccat→ f) {n} {m}) ≡ (λ {n m} → Mor→ (ccat→ g) {n} {m}))
            → f ≡ g
    lemma refl refl = refl

  structuredCCatMor+Eq : {f+ g+ : StructuredCCatMor+ sC sD} (let f = strucCCat→ f+) (let g = strucCCat→ g+)
                      → ({n : ℕ} (X : Ob (ccat sC) n) → Ob→ (ccat→ f) X ≡ Ob→ (ccat→ g) X)
                      → ({n m : ℕ} (X : Mor (ccat sC) n m) → Mor→ (ccat→ f) X ≡ Mor→ (ccat→ g) X)
                      → f+ ≡ g+
  structuredCCatMor+Eq h k = lemma (structuredCCatMorEq h k)  where

    lemma : {f+ g+ : StructuredCCatMor+ sC sD} (let f = strucCCat→ f+) (let g = strucCCat→ g+)
            → f ≡ g
            → f+ ≡ g+
    lemma refl = refl
