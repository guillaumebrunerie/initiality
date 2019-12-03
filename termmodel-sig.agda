{-# OPTIONS --rewriting --prop #-}

open import common
open import typetheory
open import syntx
open import rules
open import contextualcat
open import quotients
open import termmodel-common
open import termmodel-synccat
open import termmodel-uuel

open CCat hiding (Mor) renaming (id to idC)


{- Sig -}

SigStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : ftS (proj B) ≡ proj A) → DCtx (suc n)
SigStrS-// Γ A A= B B= = dctx (der Γ , Sig (dTy A A=) (dTy+ A= B B=))

SigStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : _) (A'= : _) {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : _) (B'= : _)
          → SigStrS-// Γ A A= B B= ≃ SigStrS-// Γ' A' A'= B' B'=
SigStrS-eq rΓ {A = A} rA A= A'= rB B= B'= = box (unOb≃ rΓ ,, SigCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=))

SigStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) → ObS (suc n)
SigStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → proj (SigStrS-// Γ A A= B B=))
                                                             (λ rB B= B=' → proj= (SigStrS-eq (ref Γ) (ref A) A= A= rB B= B=')))
                                        (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → proj= (SigStrS-eq (ref Γ) rA A= A'= (ref B) B= B='))))
                      (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → proj= (SigStrS-eq rΓ (ref A) A= A=' (ref B) B= B='))))

SigStr=S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc (suc n))) (B= : ftS B ≡ A) → ftS (SigStrS Γ A A= B B=) ≡ Γ
SigStr=S = //-elimP-Ctx (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → refl)))

SigStrSynCCat : CCatwithSig synCCat
CCatwithSig.SigStr SigStrSynCCat = SigStrS 
CCatwithSig.SigStr= SigStrSynCCat = SigStr=S _ _ _ _ _
CCatwithSig.SigStrNat' SigStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= g₁ → refl)))))


{- sig -}

sigStrS-// : (i : ℕ) (Γ : DCtx n) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (proj Γ)) (b : DMor (suc n) (suc (suc n))) (bₛ : S.is-section (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (ElStrS i (proj Γ) (proj a) aₛ a₁)) → DMor n (suc n)
sigStrS-// i Γ a aₛ a₁ b bₛ b₁ = dmorTm Γ (uu i) UU (sig i (getTm a) (getTm b)) (SigUU (dTm refl a aₛ a₁) (dTm refl b bₛ b₁))

sigStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : _) (a'ₛ : _) (a₁ : _) (a'₁ : _) {b b' : DMor (suc n) (suc (suc n))} (rb : b ≃ b') (bₛ : _) (b'ₛ : _) (b₁ : _) (b'₁ : _)
          → sigStrS-// i Γ a aₛ a₁ b bₛ b₁ ≃ sigStrS-// i Γ' a' a'ₛ a'₁ b' b'ₛ b'₁
sigStrS-eq i rΓ ra aₛ a'ₛ a₁ a'₁ rb bₛ b'ₛ b₁ b'₁ =
  dmorTm= dmorTmₛ dmorTmₛ rΓ UUCong (SigUUCong (dTm refl _ aₛ a₁)
                                               (dTm= refl ra aₛ a'ₛ a₁ a'₁)
                                               (dTm= refl rb bₛ b'ₛ b₁ b'₁))


sigStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁)) → MorS n (suc n)
sigStrS i = //-elim-Ctx (λ Γ → //-elim-Tm (λ a aₛ a₁ → //-elim-Tm (λ b bₛ b₁ → proj (sigStrS-// i Γ a aₛ a₁ b bₛ b₁))
                                                                 (λ rb bₛ b'ₛ b₁ b'₁ → proj= (sigStrS-eq i (ref Γ) (ref a) aₛ aₛ a₁ a₁ rb bₛ b'ₛ b₁ b'₁)))
                                         (λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (sigStrS-eq i (ref Γ) ra aₛ a'ₛ a₁ a'₁ (ref b) bₛ bₛ b₁ b₁'))))
                       (λ rΓ → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (sigStrS-eq i rΓ (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁'))))

sigStrₛS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁)) → S.is-section (sigStrS i Γ a aₛ a₁ b bₛ b₁)
sigStrₛS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → dmorTmₛ)))

sigStr₁S : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁)) → ∂₁S (sigStrS i Γ a aₛ a₁ b bₛ b₁) ≡ UUStrS i Γ
sigStr₁S i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → refl)))

sigStrSynCCat : CCatwithsig synCCat UUStrSynCCat ElStrSynCCat

CCatwithsig.sigStr sigStrSynCCat = sigStrS
CCatwithsig.sigStrₛ sigStrSynCCat {Γ = Γ} {a = a} {b = b} = sigStrₛS _ Γ a _ _ b _ _
CCatwithsig.sigStr₁ sigStrSynCCat {Γ = Γ} {a = a} {b = b} = sigStr₁S _ Γ a _ _ b _ _
CCatwithsig.sigStrNat' sigStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ g₁ → refl)))))


{- pair -}

pairStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : S.ft (proj B) ≡ proj A) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : S.∂₁ (proj a) ≡ proj A) (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : S.∂₁ (proj b) ≡ S.star (proj a) (proj B) B= a₁) → DMor n (suc n)
pairStrS-// Γ A A= B B= a aₛ a₁ b bₛ b₁ = dmorTm Γ (sig (getTy A) (getTy B))
                                                   (Sig (dTy A A=) (dTy+ A= B B=))
                                                   (pair (getTy A) (getTy B) (getTm a) (getTm b))
                                                   (Pair (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)) 


pairStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : S.ft (proj A) ≡ proj Γ) (A'= : S.ft (proj A') ≡ proj Γ') {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : S.ft (proj B) ≡ proj A) (B'= : S.ft (proj B') ≡ proj A') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : S.∂₁ (proj a) ≡ proj A) (a'₁ : S.∂₁ (proj a') ≡ proj A') {b b' : DMor n (suc n)} (rb : b ≃ b') (bₛ : S.is-section (proj b)) (b'ₛ : S.is-section (proj b')) (b₁ : S.∂₁ (proj b) ≡ S.star (proj a) (proj B) B= a₁) (b'₁ : S.∂₁ (proj b') ≡ S.star (proj a') (proj B') B'= a'₁) → pairStrS-// Γ A A= B B= a aₛ a₁ b bₛ b₁ ≃ pairStrS-// Γ' A' A'= B' B'= a' a'ₛ a'₁ b' b'ₛ b'₁
pairStrS-eq rΓ {A} {A'} rA A= A'= {B} {B'} rB B= B'= {a} {a'} ra aₛ a'ₛ a₁ a'₁ {b} {b'} rb bₛ b'ₛ b₁ b'₁ =
            dmorTm= dmorTmₛ dmorTmₛ rΓ (SigCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=))
                                       (PairCong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=) (dTm= A= ra aₛ a'ₛ a₁ a'₁) (dTmSubst= A= rB B= B'= ra aₛ a'ₛ a₁ a'₁ rb bₛ b'ₛ b₁ b'₁))

pairStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ S.star a B B= a₁) → MorS n (suc n)
pairStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → //-elim-Tm (λ a aₛ a₁ → //-elim-Tm (λ b bₛ b₁ → proj (pairStrS-// Γ A A= B B= a aₛ a₁ b bₛ b₁))
                                                                                                           (λ rb bₛ b'ₛ b₁ b'₁ → proj= (pairStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= (ref a) aₛ aₛ a₁ a₁ rb bₛ b'ₛ b₁ b'₁)))
                                                                                   (λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (pairStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= ra aₛ a'ₛ a₁ a'₁ (ref b) bₛ bₛ b₁ b₁'))))
                                                              (λ rB B= B'= → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (pairStrS-eq (ref Γ) (ref A) A= A= rB B= B'= (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁')))))
                                         (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (pairStrS-eq (ref Γ) rA A= A'= (ref B) B= B=' (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁'))))))
                       (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (pairStrS-eq rΓ (ref A) A= A=' (ref B) B= B=' (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁'))))))
           
pairStrₛS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ S.star a B B= a₁) → S.is-section (pairStrS Γ A A= B B= a aₛ a₁ b bₛ b₁)
pairStrₛS =  //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → dmorTmₛ)))))

pairStr₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ S.star a B B= a₁) → S.∂₁ (pairStrS Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ SigStrS Γ A A= B B=
pairStr₁S =  //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → refl)))))

pairStrSynCCat : CCatwithpair synCCat SigStrSynCCat
CCatwithpair.pairStr pairStrSynCCat = pairStrS
CCatwithpair.pairStrₛ pairStrSynCCat {Γ = Γ} {A = A} {B = B} {a = a} {b = b} = pairStrₛS Γ A _ B _ a _ _ b _ _
CCatwithpair.pairStr₁ pairStrSynCCat {Γ = Γ} {A = A} {B = B} {a = a} {b = b} = pairStr₁S Γ A _ B _ a _ _ b _ _
CCatwithpair.pairStrNat' pairStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ g₁ → up-to-rhsTyEq (ap (_[_]Ty (sig (getTy A) (getTy B))) (idMor[]Mor (mor g))))))))))


{- pr1 -}

pr1StrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : S.ft (proj B) ≡ proj A) (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj Γ) (proj A) A= (proj B) B=) → DMor n (suc n)
pr1StrS-// Γ A A= B B= u uₛ u₁ = dmorTm Γ (getTy A) (dTy A A=) (pr1 (getTy A) (getTy B) (getTm u))
                                                               (Pr1 (dTy A A=) (dTy+ A= B B=) (dTm refl u uₛ u₁))


pr1StrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : S.ft (proj A) ≡ proj Γ) (A'= : S.ft (proj A') ≡ proj Γ') {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : S.ft (proj B) ≡ (proj A)) (B'= : S.ft (proj B') ≡ proj A') {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj Γ) (proj A) A= (proj B) B=) (u'₁ : ∂₁S (proj u') ≡ SigStrS (proj Γ') (proj A') A'= (proj B') B'=) → pr1StrS-// Γ A A= B B= u uₛ u₁ ≃ pr1StrS-// Γ' A' A'= B' B'= u' u'ₛ u'₁
pr1StrS-eq {Γ = Γ} {Γ'} rΓ {A} {A'} rA A= A'= {B} {B'} rB B= B'= {u} {u'} ru uₛ u'ₛ u₁ u'₁ =
              dmorTm= dmorTmₛ dmorTmₛ rΓ  (dTy= rA A=) (Pr1Cong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=) (dTm= refl ru uₛ u'ₛ u₁ u'₁))


pr1StrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=) → MorS n (suc n)
pr1StrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → //-elim-Tm (λ u uₛ u₁ → proj (pr1StrS-// Γ A A= B B= u uₛ u₁))
                                                                                   (λ ru uₛ u'ₛ u₁ u'₁ → proj= (pr1StrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= ru uₛ u'ₛ u₁ u'₁)))
                                                              (λ rB B= B'= → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (pr1StrS-eq (ref Γ) (ref A) A= A= rB B= B'= (ref u) uₛ uₛ u₁ u₁'))))
                                         (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (pr1StrS-eq (ref Γ) rA A= A'= (ref B) B= B=' (ref u) uₛ uₛ u₁ u₁')))))
                       (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (pr1StrS-eq rΓ (ref A) A= A=' (ref B) B= B=' (ref u) uₛ uₛ u₁ u₁')))))

pr1StrₛS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=) → S.is-section (pr1StrS Γ A A= B B= u uₛ u₁)
pr1StrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → dmorTmₛ))))

pr1Str₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=) → S.∂₁ (pr1StrS Γ A A= B B= u uₛ u₁) ≡ A
pr1Str₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → eq (box (CtxTy=Ctx A A=))))))


pr1StrSynCCat : CCatwithpr1 synCCat SigStrSynCCat
CCatwithpr1.pr1Str pr1StrSynCCat = pr1StrS
CCatwithpr1.pr1Strₛ pr1StrSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = pr1StrₛS Γ A _ B _ u _ _
CCatwithpr1.pr1Str₁ pr1StrSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = pr1Str₁S Γ A _ B _ u _ _
CCatwithpr1.pr1StrNat' pr1StrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ g₁ → up-to-rhsTyEq (ap (_[_]Ty (getTy A)) (idMor[]Mor (mor g)))))))))


{- pr2 -}

pr2StrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ) (B : DCtx (suc (suc n))) (B= : S.ft (proj B) ≡ proj A) (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj Γ) (proj A) A= (proj B) B=) → DMor n (suc n)
pr2StrS-// Γ A A= B B= u uₛ u₁ = dmorTm Γ (substTy (getTy B) (pr1 (getTy A) (getTy B) (getTm u)))
                                          (SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (Pr1 (dTy A A=) (dTy+ A= B B=) (dTm refl u uₛ u₁))))
                                          (pr2 (getTy A) (getTy B) (getTm u))
                                          (Pr2 (dTy A A=) (dTy+ A= B B=) (dTm refl u uₛ u₁))


pr2StrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : S.ft (proj A) ≡ proj Γ) (A'= : S.ft (proj A') ≡ proj Γ') {B B' : DCtx (suc (suc n))} (rB : B ≃ B') (B= : S.ft (proj B) ≡ (proj A)) (B'= : S.ft (proj B') ≡ proj A') {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : ∂₁S (proj u) ≡ SigStrS (proj Γ) (proj A) A= (proj B) B=) (u'₁ : ∂₁S (proj u') ≡ SigStrS (proj Γ') (proj A') A'= (proj B') B'=) → pr2StrS-// Γ A A= B B= u uₛ u₁ ≃ pr2StrS-// Γ' A' A'= B' B'= u' u'ₛ u'₁
pr2StrS-eq {Γ = Γ} {Γ'} rΓ {A} {A'} rA A= A'= {B} {B'} rB B= B'= {u} {u'} ru uₛ u'ₛ u₁ u'₁ =
              dmorTm= dmorTmₛ dmorTmₛ rΓ  (SubstTyFullEq' (der Γ) ((der Γ) , (dTy A A=)) (dTy+= A= rB B=) (idMor+= (der Γ) (Pr1Cong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=) (dTm= refl ru uₛ u'ₛ u₁ u'₁))))
                                          (Pr2Cong (dTy A A=) (dTy= rA A=) (dTy+= A= rB B=) (dTm= refl ru uₛ u'ₛ u₁ u'₁))


pr2StrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=) → MorS n (suc n)
pr2StrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → //-elim-Tm (λ u uₛ u₁ → proj (pr2StrS-// Γ A A= B B= u uₛ u₁))
                                                                                   (λ ru uₛ u'ₛ u₁ u'₁ → proj= (pr2StrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= ru uₛ u'ₛ u₁ u'₁)))
                                                              (λ rB B= B'= → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (pr2StrS-eq (ref Γ) (ref A) A= A= rB B= B'= (ref u) uₛ uₛ u₁ u₁'))))
                                         (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (pr2StrS-eq (ref Γ) rA A= A'= (ref B) B= B=' (ref u) uₛ uₛ u₁ u₁')))))
                       (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (pr2StrS-eq rΓ (ref A) A= A=' (ref B) B= B=' (ref u) uₛ uₛ u₁ u₁')))))

pr2StrₛS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=) → S.is-section (pr2StrS Γ A A= B B= u uₛ u₁)
pr2StrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → dmorTmₛ))))

pr2Str₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=) → S.∂₁ (pr2StrS Γ A A= B B= u uₛ u₁) ≡ S.star (pr1StrS Γ A A= B B= u uₛ u₁) B B= (pr1Str₁S Γ A A= B B= u uₛ u₁)
pr2Str₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → refl))))


pr2StrSynCCat : CCatwithpr2 synCCat SigStrSynCCat pr1StrSynCCat
CCatwithpr2.pr2Str pr2StrSynCCat = pr2StrS
CCatwithpr2.pr2Strₛ pr2StrSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = pr2StrₛS Γ A _ B _ u _ _
CCatwithpr2.pr2Str₁ pr2StrSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = pr2Str₁S Γ A _ B _ u _ _
CCatwithpr2.pr2StrNat' pr2StrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ g₁ → up-to-rhsTyEq (ap (_[_]Ty (getTy B [ idMor _ , pr1 (getTy A) (getTy B) (getTm u) ]Ty)) (idMor[]Mor (mor g)) ∙ []Ty-substTy)))))))


{- ElSig= -}

elsigStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (b : MorS (suc n) (suc (suc n))) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i (ElStrS i Γ a aₛ a₁))
            → ElStrS i Γ (sigStrS i Γ a aₛ a₁ b bₛ b₁) (sigStrₛS i Γ a aₛ a₁ b bₛ b₁) (sigStr₁S i Γ a aₛ a₁ b bₛ b₁) ≡ SigStrS Γ (ElStrS i Γ a aₛ a₁) (ElStr=S i Γ a aₛ a₁) (ElStrS i (ElStrS i Γ a aₛ a₁) b bₛ b₁) (ElStr=S i (ElStrS i Γ a aₛ a₁) b bₛ b₁)
elsigStrS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → eq (box (CtxRefl (der Γ) ,, ElSig= (dTm refl a aₛ a₁) (dTm refl b bₛ b₁))))))


{- BetaSig1 -}

betaSig1StrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ S.star a B B= a₁) → pr1StrS Γ A A= B B= (pairStrS Γ A A= B B= a aₛ a₁ b bₛ b₁) (pairStrₛS Γ A A= B B= a aₛ a₁ b bₛ b₁) (pairStr₁S Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ a
betaSig1StrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ →
             eq (box (CtxSymm (CtxTran (reflectOb (S.is-section₀ aₛ a₁)) (reflectOb A=)))
                     (CtxTran (CtxTy=Ctx A A=) (CtxSymm (reflectOb a₁)))
                     (MorTran (der Γ) (der Γ , dTy A A=) (idMor+= (der Γ) (BetaSig1 (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)))
                                                         (MorSymm (der Γ) (der Γ , dTy A A=) (morTm=idMorTm A= a aₛ a₁)))))))))


{- BetaSig2 -}

betaSig2StrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ S.star a B B= a₁) → pr2StrS Γ A A= B B= (pairStrS Γ A A= B B= a aₛ a₁ b bₛ b₁) (pairStrₛS Γ A A= B B= a aₛ a₁ b bₛ b₁) (pairStr₁S Γ A A= B B= a aₛ a₁ b bₛ b₁) ≡ b
betaSig2StrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → eq (box
                        (CtxSymm (CtxTran (reflectOb (S.is-section₀ bₛ b₁)) (CtxTran (reflectOb (S.is-section₀ aₛ a₁)) (reflectOb A=))))
                        (CtxTran (CtxRefl (der Γ) ,, SubstTyMorEq (dTy+ A= B B=)
                                                                  (idMor+ (der Γ) (Pr1 (dTy A A=) (dTy+ A= B B=) (Pair (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁))))
                                                                  (MorTran (der Γ) (der Γ , dTy A A=) (idMor+= (der Γ) (BetaSig1 (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)))
                                                                                                      (MorSymm (der Γ) (der Γ , dTy A A=) (morTm=idMorTm A= a aₛ a₁))))
                                 (CtxTran (CtxSymm (CtxTran (reflectOb (S.is-section₀ aₛ a₁)) (reflectOb A=)) ,, TyRefl (SubstTy (dTy+ A= B B=) (dMor A= a aₛ a₁)))
                                          (CtxSymm (reflectOb b₁)))) 
                        (MorTran (der Γ) (der Γ , SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (Pr1 (dTy A A=) (dTy+ A= B B=)
                                                                                              (Pair (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)))))
                                 (idMor+= (der Γ) (ConvEq (SubstTy (dTy+ A= B B=)
                                                          (idMor+ (der Γ) (dTm A= a aₛ a₁)))
                                                          (BetaSig2 (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁))
                                                          (SubstTyMorEq (dTy+ A= B B=) (idMor+ (der Γ) (dTm A= a aₛ a₁))
                                                                                       (idMor+= (der Γ) (TmSymm (BetaSig1 (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)))))))
                                 (MorSymm (der Γ) (der Γ , SubstTy (dTy+ A= B B=) (idMor+ (der Γ) (Pr1 (dTy A A=) (dTy+ A= B B=) (Pair (dTy A A=) (dTy+ A= B B=) (dTm A= a aₛ a₁) (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)))))
                                          (ConvMorEq (morTm=idMorTm {Γ = Γ} (eq (box (CtxTran (reflectOb (S.is-section₀ aₛ a₁)) (reflectOb A=)))) b bₛ b₁)
                                                     (CtxRefl (der Γ)) (CtxRefl (der Γ) ,, SubstTyMorEq (dTy+ A= B B=) (dMor A= a aₛ a₁)
                                                                                                        (MorTran (der Γ) (der Γ , dTy A A=)
                                                                                                                 (morTm=idMorTm A= a aₛ a₁)
                                                                                                                 (idMor+= (der Γ) (TmSymm (BetaSig1 (dTy A A=)
                                                                                                                                                    (dTy+ A= B B=)
                                                                                                                                                    (dTm A= a aₛ a₁)
                                                                                                                                                    (dTmSubst A= B B= a aₛ a₁ b bₛ b₁)))))))))))))))

{- EtaSig -}

etaSigStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (B : ObS (suc (suc n))) (B= : S.ft B ≡ A) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SigStrS Γ A A= B B=)
           → u ≡ pairStrS Γ A A= B B= (pr1StrS Γ A A= B B= u uₛ u₁) (pr1StrₛS Γ A A= B B= u uₛ u₁) (pr1Str₁S Γ A A= B B= u uₛ u₁) (pr2StrS Γ A A= B B= u uₛ u₁) (pr2StrₛS Γ A A= B B= u uₛ u₁) (pr2Str₁S Γ A A= B B= u uₛ u₁)
etaSigStrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ → eq (box (reflectOb (S.is-section₀ uₛ u₁)) (reflectOb u₁) (ConvMorEq (MorTran (der Γ) (der Γ , Sig (dTy A A=) (dTy+ A= B B=)) (morTm=idMorTm refl u uₛ u₁) (idMor+= (der Γ) (EtaSig (dTy A A=) (dTy+ A= B B=) (dTm refl u uₛ u₁)))) (reflectOb (! (S.is-section₀ uₛ u₁))) (reflectOb (! u₁))))))))
