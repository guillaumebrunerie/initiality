{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import typetheory
open import reflection hiding (proj)
open import syntx
open import rules
open import contextualcat
open import quotients
open import termmodel-common
open import termmodel-synccat
open import termmodel-uuel

open CCat hiding (Mor) renaming (id to idC)


{- Pi -}

PiStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : ftS (proj B) ≡ proj A) → DCtx (suc n)
PiStrS-// Γ A A= B B= = (ctx Γ , pi (getTy A) (getTy B)) , (der Γ , Pi (dTy A A=) (dTy+ A= B B=))

PiStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : _) (A'= : _) {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : _) (B'= : _)
          → proj {R = ObEquiv} (PiStrS-// Γ A A= B B=) ≡ proj (PiStrS-// Γ' A' A'= B' B'=)
PiStrS-eq rΓ {A = A} rA A= A'= {B = B} rB B= B'= = eq (box (unOb≃ rΓ ,, PiCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=)))

PiStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) → ObS (suc n)
PiStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → proj (PiStrS-// Γ A A= B B=))
                                                            (λ rB B= B=' → proj= (PiStrS-eq (ref Γ) (ref A) A= A= rB B= B=')))
                                       (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → proj= (PiStrS-eq (ref Γ) rA A= A'= (ref B) B= B='))))
                     (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → proj= (PiStrS-eq rΓ (ref A) A= A=' (ref B) B= B='))))

PiStr=S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) → ftS (PiStrS Γ A A= B B=) ≡ Γ
PiStr=S = //-elimP-Ctx (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → refl)))

PiStrSynCCat : CCatwithPi synCCat
CCatwithPi.PiStr PiStrSynCCat = PiStrS 
CCatwithPi.PiStr= PiStrSynCCat = PiStr=S _ _ _ _ _
CCatwithPi.PiStrNat' PiStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= g₁ → refl)))))


{- pi -}

piStrS-// : (i : ℕ) (Γ : DCtx n) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (proj Γ)) (b : DMor (suc n) (suc (suc n))) (bₛ : S.is-section (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj Γ) (proj a) aₛ a₁)) → DMor n (suc n)
piStrS-// i Γ a aₛ a₁ b bₛ b₁ = dmorTm Γ (uu i) UU (pi i (getTm a) (getTm b)) (PiUU (dTm refl a aₛ a₁) (dTm refl b bₛ b₁))

piStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : _) (a'ₛ : _) (a₁ : _) (a'₁ : _) {b b' : DMor (suc n) (suc (suc n))} (rb : b ≃ b') (bₛ : _) (b'ₛ : _) (b₁ : _) (b'₁ : _)
          → proj {R = MorEquiv} (piStrS-// i Γ a aₛ a₁ b bₛ b₁) ≡ proj (piStrS-// i Γ' a' a'ₛ a'₁ b' b'ₛ b'₁)
piStrS-eq i rΓ ra aₛ a'ₛ a₁ a'₁ rb bₛ b'ₛ b₁ b'₁ =
  dmorTm= rΓ UU UU UUCong (PiUU (dTm refl _ aₛ a₁) (dTm refl _ bₛ b₁)) (PiUU (dTm refl _ a'ₛ a'₁) (dTm refl _ b'ₛ b'₁))
    (PiUUCong (dTm refl _ aₛ a₁)
              (dTm= (box (unOb≃ rΓ ,, UUCong)) refl ra aₛ a'ₛ a₁ a'₁)
              (dTm= (box ((unOb≃ rΓ ,, ElCong (dTm= (box (unOb≃ rΓ ,, UUCong)) refl ra aₛ a'ₛ a₁ a'₁)) ,, UUCong)) refl rb bₛ b'ₛ b₁ b'₁))


piStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁)) → MorS n (suc n)
piStrS i = //-elim-Ctx (λ Γ → //-elim-Tm (λ a aₛ a₁ → //-elim-Tm (λ b bₛ b₁ → proj (piStrS-// i Γ a aₛ a₁ b bₛ b₁))
                                                                 (λ rb bₛ b'ₛ b₁ b'₁ → proj= (piStrS-eq i (ref Γ) (ref a) aₛ aₛ a₁ a₁ rb bₛ b'ₛ b₁ b'₁)))
                                         (λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (piStrS-eq i (ref Γ) ra aₛ a'ₛ a₁ a'₁ (ref b) bₛ bₛ b₁ b₁'))))
                       (λ rΓ → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (piStrS-eq i rΓ (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁'))))

piStrₛS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁)) → S.is-section (piStrS i Γ a aₛ a₁ b bₛ b₁)
piStrₛS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → dmorTmₛ UU (PiUU (dTm refl a aₛ a₁) (dTm refl b bₛ b₁)))))

piStr₁S : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁)) → ∂₁S (piStrS i Γ a aₛ a₁ b bₛ b₁) ≡ UUStrS i Γ
piStr₁S i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → refl)))

piStrSynCCat : CCatwithpi synCCat UUStrSynCCat ElStrSynCCat

CCatwithpi.piStr piStrSynCCat = piStrS
CCatwithpi.piStrₛ piStrSynCCat {Γ = Γ} {a = a} {b = b} = piStrₛS _ Γ a _ _ b _ _
CCatwithpi.piStr₁ piStrSynCCat {Γ = Γ} {a = a} {b = b} = piStr₁S _ Γ a _ _ b _ _
CCatwithpi.piStrNat' piStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ g₁ → refl)))))


{- lam -}

lamStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : ftS (proj B) ≡ proj A) (u : DMor (suc n) (suc (suc n))) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ proj B) → DMor n (suc n)
lamStrS-// Γ A A= B B= u uₛ u₁ = dmorTm Γ (pi (getTy A) (getTy B)) (Pi (dTy A A=) (dTy+ A= B B=)) (lam (getTy A) (getTy B) (getTm u)) (Lam (dTy A A=) (dTy+ A= B B=) (dTm+ A= B= u uₛ u₁))

lamStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : _) (A'= : _) {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : _) (B'= : _) {u u' : DMor (suc n) (suc (suc n))} (ru : u ≃ u') (uₛ : _) (u'ₛ : _) (u₁ : _) (u'₁ : _) → proj {R = MorEquiv} (lamStrS-// Γ A A= B B= u uₛ u₁) ≡ proj (lamStrS-// Γ' A' A'= B' B'= u' u'ₛ u'₁)
lamStrS-eq rΓ {A} {A'} rA A= A'= {B} {B'} rB B= B'= ru uₛ u'ₛ u₁ u'₁ = dmorTm= rΓ (Pi (dTy A A=) (dTy+ A= B B=)) (Pi (dTy A' A'=) (dTy+ A'= B' B'=)) (PiCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=)) (Lam (dTy A A=) (dTy+ A= B B=) (dTm+ A= B= _ uₛ u₁)) (Lam (dTy A' A'=) (dTy+ A'= B' B'=) (dTm+ A'= B'= _ u'ₛ u'₁)) (LamCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=) (dTm+= A= rB B= ru uₛ u'ₛ u₁ u'₁))

lamStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (u : MorS (suc n) (suc (suc n))) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ B) → MorS n (suc n)
lamStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → //-elim-Tm (λ u uₛ u₁ → proj (lamStrS-// Γ A A= B B= u uₛ u₁))
                                                                                  (λ ru uₛ u'ₛ u₁ u'₁ → proj= (lamStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= ru uₛ u'ₛ u₁ u'₁)))
                                                             (λ rB B= B'= → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (lamStrS-eq (ref Γ) (ref A) A= A= rB B= B'= (ref u) uₛ uₛ u₁ u₁'))))
                                        (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (lamStrS-eq (ref Γ) rA A= A'= (ref B) B= B=' (ref u) uₛ uₛ u₁ u₁')))))
                     (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (lamStrS-eq rΓ (ref A) A= A=' (ref B) B= B=' (ref u) uₛ uₛ u₁ u₁')))))

lamStrₛS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (u : MorS (suc n) (suc (suc n))) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ B) → S.is-section (lamStrS Γ A A= B B= u uₛ u₁)
lamStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → dmorTmₛ (Pi (dTy A A=) (dTy+ A= B B=)) (Lam (dTy A A=) (dTy+ A= B B=) (dTm+ A= B= u uₛ u₁))))))

lamStr₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (u : MorS (suc n) (suc (suc n))) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ B) → ∂₁S (lamStrS Γ A A= B B= u uₛ u₁) ≡ PiStrS Γ A A= B B=
lamStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → refl))))


lamStrSynCCat : CCatwithlam synCCat PiStrSynCCat
CCatwithlam.lamStr lamStrSynCCat = lamStrS
CCatwithlam.lamStrₛ lamStrSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = lamStrₛS Γ A _ B _ u _ _
CCatwithlam.lamStr₁ lamStrSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = lamStr₁S Γ A _ B _ u _ _
CCatwithlam.lamStrNat' lamStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ g₁ → up-to-rhsTyEq (ap (_[_]Ty (pi (getTy A) (getTy B))) (idMor[]Mor (mor g)))))))))


{- app -}

appStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : ftS (proj B) ≡ proj A) (f : DMor n (suc n)) (fₛ : S.is-section (proj f)) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj Γ) (proj A) A= (proj B) B=) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) → DMor n (suc n)
appStrS-// Γ A A= B B= f fₛ f₁ a aₛ a₁ = dmorTm Γ (substTy (getTy B) (getTm a)) (SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (dTm A= a aₛ a₁))) (app (getTy A) (getTy B) (getTm f) (getTm a)) (App (dTy A A=) (dTy+ A= B B=) (dTm refl f fₛ f₁) (dTm A= a aₛ a₁))
 
appStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : ftS (proj A) ≡ proj Γ) (A'= : ftS (proj A') ≡ proj Γ') {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : ftS (proj B) ≡ proj A) (B'= : ftS (proj B') ≡ proj A') {f f' : DMor n (suc n)} (rf : f ≃ f') (fₛ : S.is-section (proj f)) (f'ₛ : S.is-section (proj f')) (f₁ : ∂₁S (proj f) ≡ PiStrS (proj Γ) (proj A) A= (proj B) B=) (f₁' : ∂₁S (proj f') ≡ PiStrS (proj Γ') (proj A') A'= (proj B') B'=) {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ proj A) (a'₁ : ∂₁S (proj a') ≡ proj A')
          → proj {R = MorEquiv} (appStrS-// Γ A A= B B= f fₛ f₁ a aₛ a₁) ≡ proj (appStrS-// Γ' A' A'= B' B'= f' f'ₛ f₁' a' a'ₛ a'₁)
appStrS-eq {Γ = Γ} {Γ'} rΓ {A} {A'} rA A= A'= {B} {B'} rB B= B'= {f} {f'} rf fₛ f'ₛ f₁ f'₁ {a} {a'} ra aₛ a'ₛ a₁ a'₁ =
  dmorTm= rΓ (SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (dTm A= a aₛ a₁))) (SubstTy (dTy+ A'= B' B'=) (idMor+ (der Γ') (dTm A'= a' a'ₛ a'₁)))
          (SubstTyMorEq2 (der Γ) (der Γ , dTy A A=) (dTy+= A= rB B=) (idMor+= (der Γ) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁))) (App (dTy A A=) (dTy+ A= B B=) (dTm refl f fₛ f₁) (dTm A= a aₛ a₁)) (App (dTy A' A'=) (dTy+ A'= B' B'=) (dTm refl f' f'ₛ f'₁) (dTm A'= a' a'ₛ a'₁))
          (AppCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=) (dTm= (box (unOb≃ rΓ ,, PiCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=))) refl rf fₛ f'ₛ f₁ f'₁) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁))

appStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (f : MorS n (suc n)) (fₛ : S.is-section f) (f₁ : ∂₁S f ≡ PiStrS Γ A A= B B=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
        → MorS n (suc n)
appStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → //-elim-Tm (λ f fₛ f₁ → //-elim-Tm (λ a aₛ a₁ → proj (appStrS-// Γ A A= B B= f fₛ f₁ a aₛ a₁))
                                                                                                          (λ ra aₛ a'ₛ a₁ a'₁ → proj= (appStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= (ref f) fₛ fₛ f₁ f₁ ra aₛ a'ₛ a₁ a'₁)))
                                                                                  (λ rf fₛ f'ₛ f₁ f'₁ → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (appStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= rf fₛ f'ₛ f₁ f'₁ (ref a) aₛ aₛ a₁ a₁'))))
                                                             (λ rB B= B'= → //-elimP-Tm (λ f fₛ f₁ f₁' → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (appStrS-eq (ref Γ) (ref A) A= A= rB B= B'= (ref f) fₛ fₛ f₁ f₁' (ref a) aₛ aₛ a₁ a₁')))))
                                        (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ f fₛ f₁ f₁' → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (appStrS-eq (ref Γ) rA A= A'= (ref B) B= B=' (ref f) fₛ fₛ f₁ f₁' (ref a) aₛ aₛ a₁ a₁'))))))
                      (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ f fₛ f₁ f₁' → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (appStrS-eq rΓ (ref A) A= A=' (ref B) B= B=' (ref f) fₛ fₛ f₁ f₁' (ref a) aₛ aₛ a₁ a₁'))))))

appStrₛS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (f : MorS n (suc n)) (fₛ : S.is-section f) (f₁ : ∂₁S f ≡ PiStrS Γ A A= B B=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
         → S.is-section (appStrS Γ A A= B B= f fₛ f₁ a aₛ a₁)
appStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ f fₛ f₁ → //-elimP (λ a aₛ a₁ → dmorTmₛ (SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (dTm A= a aₛ a₁))) (App (dTy A A=) (dTy+ A= B B=) (dTm refl f fₛ f₁) (dTm A= a aₛ a₁)))))))

appStr₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) (f : MorS n (suc n)) (fₛ : S.is-section f) (f₁ : ∂₁S f ≡ PiStrS Γ A A= B B=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
         → ∂₁S (appStrS Γ A A= B B= f fₛ f₁ a aₛ a₁) ≡ S.star a B B= a₁
appStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ f fₛ f₁ → //-elimP (λ a aₛ a₁ → eq (box (CtxSymm ((reflectOb (S.is-section₀ aₛ a₁ ∙ A=)) ,, SubstTyMorEq (dTy B B=) (ConvMor (morDer a) (CtxRefl (der (lhs a))) (reflectOb a₁)) (ConvMorEq (morTm=idMorTm' aₛ) (CtxRefl (der (lhs a))) (reflectOb a₁))))))))))

appStrSynCCat : CCatwithapp synCCat PiStrSynCCat
CCatwithapp.appStr appStrSynCCat = appStrS
CCatwithapp.appStrₛ appStrSynCCat {Γ = Γ} {A = A} {B = B} {f = f} {a = a} = appStrₛS Γ A _ B _ f _ _ a _ _
CCatwithapp.appStr₁ appStrSynCCat {Γ = Γ} {A = A} {B = B} {f = f} {a = a} = appStr₁S Γ A _ B _ f _ _ a _ _
CCatwithapp.appStrNat' appStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ f fₛ f₁ → //-elimP (λ a aₛ a₁ g₁ → up-to-rhsTyEq (ap (_[_]Ty (substTy (getTy B) (getTm a))) (idMor[]Mor (mor g)) ∙ []Ty-substTy))))))))


{- ElPi= -}

elpiStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁))
            → ElStrS i Γ (piStrS i Γ a aₛ a₁ b bₛ b₁) (piStrₛS i Γ a aₛ a₁ b bₛ b₁) (piStr₁S i Γ a aₛ a₁ b bₛ b₁) ≡ PiStrS Γ (ElStrS i Γ a aₛ a₁) (ElStr=S i Γ a aₛ a₁) (ElStrS i (ElStrS i Γ a aₛ a₁) b bₛ b₁) (ElStr=S i (ElStrS i Γ a aₛ a₁) b bₛ b₁)
elpiStrS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → eq (box (CtxRefl (der Γ) ,, ElPi= (dTm refl a aₛ a₁) (dTm refl b bₛ b₁))))))


{- BetaPi -}

betaPiStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS (suc n) (suc (suc n))) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ B) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
            → appStrS Γ A A= B B= (lamStrS Γ A A= B B= u uₛ u₁) (lamStrₛS Γ A A= B B= u uₛ u₁) (lamStr₁S Γ A A= B B= u uₛ u₁) a aₛ a₁ ≡ S.starTm a u (S.is-section₀ uₛ u₁ ∙ B=) a₁
betaPiStrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → //-elimP (λ a aₛ a₁ → eq (box
             (CtxSymm (CtxTran (reflectOb (S.is-section₀ aₛ a₁)) (reflectOb A=)))
             (CtxSymm (CtxTran (reflectOb (S.is-section₀ aₛ a₁)) (reflectOb A=)) ,, SubstTyMorEq2 (der Γ) (der Γ , dTy A A=)
                                                                                                  (dTy+= A= (sym (reflect u₁)) B=)
                                                                                                  (MorTran (der Γ) (der Γ , dTy A A=)
                                                                                                           (MorSymm (der Γ) (der Γ , (dTy A A=)) (morTm=idMorTm A= a aₛ a₁))
                                                                                                           (congMorEq refl refl (idMor[]Mor _) refl
                                                                                                                      (SubstMorEq (MorSymm (der Γ , dTy A A=) (der Γ , dTy A A=)
                                                                                                                                           (getMor=idMor (combine A= B B=) u uₛ u₁)) (dMor A= a aₛ a₁)))))
             (idMor+= (der Γ) (TmTran (SubstTm (dTm+ A= B= u uₛ u₁) (idMor+ (der Γ) (dTm A= a aₛ a₁)))
                                      (BetaPi (dTy A A=) (dTy+ A= B B=) (dTm+ A= B= u uₛ u₁) (dTm A= a aₛ a₁))
                                      (SubstTmMorEq (dTm+ A= B= u uₛ u₁) (idMor+ (der Γ) (dTm A= a aₛ a₁)) (MorSymm (der Γ) (der Γ , dTy A A=) (morTm=idMorTm A= a aₛ a₁)))))))))))

{- EtaPi -}
etaPiStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (f : MorS n (suc n)) (fₛ : S.is-section f) (f₁ : ∂₁S f ≡ PiStrS Γ A A= B B=)
          → f ≡ T-lhsEtaPi PiStrSynCCat lamStrSynCCat appStrSynCCat Γ A A= B B= f fₛ f₁
etaPiStrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ f fₛ f₁ → eq (box (reflectOb (S.is-section₀ fₛ f₁)) (reflectOb f₁) (ConvMorEq (MorTran (der Γ) (der Γ , Pi (dTy A A=) (dTy+ A= B B=)) (morTm=idMorTm refl f fₛ f₁) (idMor+= (der Γ) (congTmEq refl (ap-lam-Tm refl refl (ap-app-Tm weakenTy-to-[]Ty weakenTy+-to-[]Ty weakenTm-to-[]Tm refl)) refl (EtaPi (dTy A A=) (dTy+ A= B B=) (dTm refl f fₛ f₁))))) (reflectOb (! (S.is-section₀ fₛ f₁))) (reflectOb (! f₁))))))))
