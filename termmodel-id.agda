{-# OPTIONS --rewriting --prop --without-K #-}

open import common
open import typetheory
open import syntx
open import rules
open import reflection hiding (proj)
open import contextualcat
open import quotients
open import termmodel-common
open import termmodel-synccat
open import termmodel-uuel

open CCat hiding (Mor) renaming (id to idC)


{- Id -}

IdStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : ∂₁S (proj b) ≡ proj A) → DCtx (suc n)
IdStrS-// Γ A A= a aₛ a₁ b bₛ b₁ = (ctx Γ , id (getTy A) (getTm a) (getTm b)) , (der Γ , Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= b bₛ b₁))

IdStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : _) (A'= : _) {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : _) (a'ₛ : _) (a₁ : _) (a'₁ : _) {b b' : DMor n (suc n)} (rb : b ≃ b') (bₛ : _) (b'ₛ : _) (b₁ : _) (b'₁ : _) → proj {R = ObEquiv} (IdStrS-// Γ A A= a aₛ a₁ b bₛ b₁) ≡ proj (IdStrS-// Γ' A' A'= a' a'ₛ a'₁ b' b'ₛ b'₁)
IdStrS-eq rΓ rA A= A'= ra aₛ a'ₛ a₁ a'₁ rb bₛ b'ₛ b₁ b'₁ = eq (box (unOb≃ rΓ ,, IdCong (dTy= rA A=) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁) (dTm= rA A= rb bₛ b'ₛ b₁ b'₁)))

IdStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ A) → ObS (suc n)
IdStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Tm (λ a aₛ a₁ → //-elim-Tm (λ b bₛ b₁ → proj (IdStrS-// Γ A A= a aₛ a₁ b bₛ b₁))
                                                                                    (λ rb bₛ b'ₛ b₁ b'₁ → proj= (IdStrS-eq (ref Γ) (ref A) A= A= (ref a) aₛ aₛ a₁ a₁ rb bₛ b'ₛ b₁ b'₁)))
                                                            (λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (IdStrS-eq (ref Γ) (ref A) A= A= ra aₛ a'ₛ a₁ a'₁ (ref b) bₛ bₛ b₁ b₁'))))
                                       (λ rA A= A'= → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (IdStrS-eq (ref Γ) rA A= A'= (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁')))))
                     (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (IdStrS-eq rΓ (ref A) A= A=' (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁')))))

IdStr=S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ A) → ftS (IdStrS Γ A A= a aₛ a₁ b bₛ b₁) ≡ Γ
IdStr=S = //-elimP-Ctx (λ Γ → //-elimP (λ A A= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → refl))))

IdStrSynCCat : CCatwithId synCCat
CCatwithId.IdStr IdStrSynCCat = IdStrS
CCatwithId.IdStr= IdStrSynCCat = IdStr=S _ _ _ _ _ _ _ _ _
CCatwithId.IdStrNat' IdStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ g₁ → refl))))))


{- id -}

idStrS-// : (i : ℕ) (Γ : DCtx n) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (proj Γ)) (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj Γ) (proj a) aₛ a₁)  (v : DMor n (suc n)) (vₛ : S.is-section (proj v)) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj Γ) (proj a) aₛ a₁) → DMor n (suc n)
idStrS-// i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁ = dmorTm Γ (uu i) UU (id i (getTm a) (getTm u) (getTm v))
                                                           (IdUU (dTm refl a aₛ a₁) (dTm refl u uₛ u₁) (dTm refl v vₛ v₁)) 

idStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ UUStrS i (proj Γ)) (a'₁ : ∂₁S (proj a') ≡ UUStrS i (proj Γ')) {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj Γ) (proj a) aₛ a₁)  (u'₁ : ∂₁S (proj u') ≡ ElStrS i (proj Γ') (proj a') a'ₛ a'₁) {v v' : DMor n (suc n)} (rv : v ≃ v') (vₛ : S.is-section (proj v)) (v'ₛ : S.is-section (proj v')) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj Γ) (proj a) aₛ a₁) (v'₁ : ∂₁S (proj v') ≡ ElStrS i (proj Γ') (proj a') a'ₛ a'₁) → proj {R = MorEquiv} (idStrS-// i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ proj (idStrS-// i Γ' a' a'ₛ a'₁ u' u'ₛ u'₁ v' v'ₛ v'₁)
idStrS-eq i {Γ} {Γ'} rΓ {a} {a'} ra aₛ a'ₛ a₁ a'₁ {u} {u'} ru uₛ u'ₛ u₁ u'₁ {v} {v'} rv vₛ v'ₛ v₁ v'₁ =
          dmorTm= rΓ UU UU UUCong (IdUU (dTm refl a aₛ a₁) (dTm refl u uₛ u₁) (dTm refl v vₛ v₁))
                                  (IdUU (dTm refl a' a'ₛ a'₁) (dTm refl u' u'ₛ u'₁) (dTm refl v' v'ₛ v'₁))
                                  (IdUUCong (dTm= (box (unOb≃ rΓ ,, UUCong)) refl ra aₛ a'ₛ a₁ a'₁)
                                            (dTm= (box (unOb≃ rΓ ,, ElCong (dTm= (box (unOb≃ rΓ ,, UUCong)) refl ra aₛ a'ₛ a₁ a'₁))) refl ru uₛ u'ₛ u₁ u'₁)
                                            (dTm= (box (unOb≃ rΓ ,, ElCong (dTm= (box (unOb≃ rΓ ,, UUCong)) refl ra aₛ a'ₛ a₁ a'₁))) refl rv vₛ v'ₛ v₁ v'₁))

idStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)  (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁) → MorS n (suc n)
idStrS i = //-elim-Ctx (λ Γ → //-elim-Tm (λ a aₛ a₁ → //-elim-Tm (λ u uₛ u₁ → //-elim-Tm (λ v vₛ v₁ → proj (idStrS-// i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁))
                                                                                         (λ rv vₛ v'ₛ v₁ v'₁ → proj= (idStrS-eq i (ref Γ) (ref a) aₛ aₛ a₁ a₁ (ref u) uₛ uₛ u₁ u₁ rv vₛ v'ₛ v₁ v'₁)))
                                                                 (λ ru uₛ u'ₛ u₁ u'₁ → //-elimP-Tm (λ v vₛ v₁ v₁' → proj= (idStrS-eq i (ref Γ) (ref a) aₛ aₛ a₁ a₁ ru uₛ u'ₛ u₁ u'₁ (ref v) vₛ vₛ v₁ v₁'))))
                                         (λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ u uₛ u₁ u₁' → //-elimP-Tm (λ v vₛ v₁ v₁' → proj= (idStrS-eq i (ref Γ) ra aₛ a'ₛ a₁ a'₁ (ref u) uₛ uₛ u₁ u₁' (ref v) vₛ vₛ v₁ v₁')))))
                       (λ rΓ → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → //-elimP-Tm (λ v vₛ v₁ v₁' → proj= (idStrS-eq i rΓ (ref a) aₛ aₛ a₁ a₁' (ref u) uₛ uₛ u₁ u₁' (ref v) vₛ vₛ v₁ v₁')))))

idStrₛS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)  (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁) → S.is-section (idStrS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁)
idStrₛS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → dmorTmₛ UU (IdUU (dTm refl a aₛ a₁) (dTm refl u uₛ u₁) (dTm refl v vₛ v₁))))))

idStr₁S : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)  (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁) → ∂₁S (idStrS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ UUStrS i Γ
idStr₁S i = //-elimP (λ Γ →  //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → refl))))

idStrSynCCat : CCatwithid synCCat UUStrSynCCat ElStrSynCCat
CCatwithid.idStr idStrSynCCat = idStrS
CCatwithid.idStrₛ idStrSynCCat {Γ = Γ} {a = a} {u = u} {v = v} = idStrₛS _ Γ a _ _ u _ _ v _ _
CCatwithid.idStr₁ idStrSynCCat {Γ = Γ} {a = a} {u = u} {v = v} = idStr₁S _ Γ a _ _ u _ _ v _ _
CCatwithid.idStrNat' idStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ g₁ → refl))))))


{- refl -}

reflStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ (proj A)) → DMor n (suc n)
reflStrS-// Γ A A= a aₛ a₁ = dmorTm Γ (id (getTy A) (getTm a) (getTm a)) (Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= a aₛ a₁)) (refl (getTy A) (getTm a)) (Refl (dTy A A=) (dTm A= a aₛ a₁))

reflStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : S.ft (proj A) ≡ proj Γ) (A'= : S.ft (proj A') ≡ proj Γ') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ (proj A)) (a'₁ : ∂₁S (proj a') ≡ (proj A')) → proj {R = MorEquiv} (reflStrS-// Γ A A= a aₛ a₁) ≡ proj (reflStrS-// Γ' A' A'= a' a'ₛ a'₁)
reflStrS-eq rΓ {A} {A'} rA A= A'= {a} {a'} ra aₛ a'ₛ a₁ a'₁ = dmorTm= rΓ (Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= a aₛ a₁))
                                                                         (Id (dTy A' A'=) (dTm A'= a' a'ₛ a'₁) (dTm A'= a' a'ₛ a'₁))
                                                                         (IdCong (dTy= rA A=) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁))
                                                                         (Refl (dTy A A=) (dTm A= a aₛ a₁))
                                                                         (Refl (dTy A' A'=) (dTm A'= a' a'ₛ a'₁))
                                                                         (ReflCong (dTy= rA A=) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁))

reflStrS  : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) → MorS n (suc n)
reflStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Tm (λ a aₛ a₁ → proj (reflStrS-// Γ A A= a aₛ a₁))
                                                              (λ ra aₛ a'ₛ a₁ a'₁ → proj= (reflStrS-eq (ref Γ) (ref A) A= A= ra aₛ a'ₛ a₁ a'₁)))
                                         (λ rA A= A'= → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (reflStrS-eq (ref Γ) rA A= A'= (ref a) aₛ aₛ a₁ a₁'))))
                       (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (reflStrS-eq rΓ (ref A) A= A=' (ref a) aₛ aₛ a₁ a₁'))))
                       
reflStrₛS :  (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) → S.is-section (reflStrS Γ A A= a aₛ a₁)
reflStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → (//-elimP (λ a aₛ a₁ → dmorTmₛ (Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= a aₛ a₁)) (Refl (dTy A A=) (dTm A= a aₛ a₁))))))

reflStr₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) → ∂₁S (reflStrS Γ A A= a aₛ a₁) ≡ IdStrS Γ A A= a aₛ a₁ a aₛ a₁
reflStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → (//-elimP (λ a aₛ a₁ → refl))))

reflStrSynCCat : CCatwithrefl IdStrSynCCat
CCatwithrefl.reflStr reflStrSynCCat = reflStrS
CCatwithrefl.reflStrₛ reflStrSynCCat {Γ = Γ} {A = A} {a = a} = reflStrₛS Γ A _ a _ _
CCatwithrefl.reflStr₁ reflStrSynCCat {Γ = Γ} {A = A} {a = a} = reflStr₁S Γ A _ a _ _
CCatwithrefl.reflStrNat' reflStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ a aₛ a₁ g₁ → up-to-rhsTyEq (ap (_[_]Ty (id (getTy A) (getTm a) (getTm a))) (idMor[]Mor (mor g))))))))
 

{- JJ (TODO) -}


postulate
  #TODO#S : ∀ {l} {A : Set l} → A
  #TODO# : {P : Prop} → P

-- poging : {ccat : CCat} {ccatId : CCatwithId ccat} (ccatrefl : CCatwithrefl ccatId) (let open CCat+ ccat) (let open CCatwithrefl ccatrefl) (Γ : CCat.Ob ccat n) (A : CCat.Ob ccat (suc n)) (A= : CCat.ft ccat A ≡ Γ) (u v : CCat.Mor ccat n (suc n)) (uₛ : is-section u) (u₁ : ∂₁ ccat u ≡ A) (vₛ : is-section v) (v₁ : ∂₁ ccat v ≡ A) → CCat.Ob ccat (suc n)
-- poging {ccat = ccat} {ccatId} ccatrefl Γ A A= u v uₛ u₁ vₛ v₁ = CCatwithId.IdStr ccatId Γ A A= u uₛ u₁ v vₛ v₁

-- pogingS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (u v : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ proj A) (vₛ : S.is-section (proj v)) (v₁ : ∂₁S (proj v) ≡ proj A) (d : DMor n (suc n)) (dₛ : S.is-section (proj d)) (d₁ : ∂₁S (proj d) ≡ poging reflStrSynCCat (proj Γ) (proj A) A= (proj u) (proj v) uₛ u₁ vₛ v₁) → DCtx n
-- pogingS-// Γ A A= u v uₛ u₁ vₛ v₁ d dₛ d₁ = {!!}


jjStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (P : DCtx (suc (suc (suc (suc n))))) (P= : ftS (proj P) ≡ T-ftP IdStrSynCCat (proj Γ) (proj A) A=) (d : DMor (suc n) (suc (suc n))) (dₛ : S.is-section (proj d)) (d₁ : ∂₁S (proj d) ≡ T-d₁ reflStrSynCCat (proj Γ) (proj A) A= (proj P) P=) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : S.∂₁ (proj a) ≡ (proj A)) (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : S.∂₁ (proj b) ≡ (proj A)) (p : DMor n (suc n)) (pₛ : S.is-section (proj p)) (p₁ : S.∂₁ (proj p) ≡ proj (IdStrS-// Γ A A= a aₛ a₁ b bₛ b₁)) → DMor n (suc n)
jjStrS-// Γ A A= P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁ = #TODO#S


-- jjStrS-// Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁ = dmorTm Γ (subst3Ty (getTy P) (getTm a) (getTm b) (getTm p)) (Subst3Ty {C = weakenTy (getTy A)} {D = id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)} (der Γ) dP (dTm A= a aₛ a₁) (congTmTy (! (weakenSubstTy (getTy A) (getTm a))) (dTm A= b bₛ b₁)) (congTmTy (! (ap-id-Ty subst2Ty-weakenTy refl refl)) (dTm (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) p pₛ p₁))) (jj (getTy A) (getTy P) (getTm d) (getTm a) (getTm b) (getTm p)) (JJ (dTy A A=) dP dd (dTm A= a aₛ a₁) (dTm A= b bₛ b₁) (dTm (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) p pₛ p₁))
--           where dP : Derivable ((((ctx Γ , getTy A) , weakenTy (getTy A)) , id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)) ⊢ getTy P)
--                 dP = dTy {Γ = ((((_ , _) , _) , _) , (((der Γ , dTy A A=) , WeakTy (dTy A A=)) , Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))} P (P= ∙ eq (box (CtxSymm ((CtxTy=Ctx A A= ,, congTyEq refl weakenTy-to-[]Ty (TyRefl (WeakTy (dTy A A=)))) ,,
--                                                     congTyEq refl (ap-id-Ty (weakenTy-to-[]Ty ∙ ap (λ z → z [ _ ]Ty) weakenTy-to-[]Ty) refl refl)
--                                                                   (TyRefl (Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))))))
--                 dd : Derivable ((ctx Γ , getTy A) ⊢ getTm d :> subst3Ty (weakenTy' (prev (prev (prev last))) (getTy P)) (var last) (var last) (refl (weakenTy (getTy A)) (var last)))
--                 dd = congTmTy {!!} (dTm ? d dₛ d₁)



{-{A = starS-// (reflStrS-// A (starS-// (ppS-// A) A (pp₁S (proj A))) (ft-starS (ppS (proj A)) (proj A) (pp₁S (proj A)) ∙ pp₀S (proj A) ) (ssS-// (idS-// (suc _) A)) (S.varCₛ last (proj A)) {!!})
                                       (starS-// (qqS-// (ssS-// (idS-// (suc _) A)) {!!} {!!}) (starS-// (qqS-// (qqS-// (ssS-// (idS-// (suc _) A)) {!!} {!!}) {!!} {!!}) (starS-// (qqS-// (qqS-// (qqS-// (ppS-// A) A (pp₁S (proj A))) (starS-// (ppS-// A) A (pp₁S (proj A))) {!!}) {!!} {!!}) P ({!!} ∙ ! P=)) {!!}) {!!}) {!!}}-}
{-(idMor+ ((((der Γ) , (dTy A A=)) , (WeakTy (dTy A A=))) , (WeakTy (WeakTy (dTy A A=))))
                                                                                  (Refl (ConvTy (WeakTy {k = prev (prev last)} {Γ = ((ctx Γ , getTy A) , weakenTy (getTy A))} {T = getTy A} (WeakTy (WeakTy (dTy A A=)))) (((CtxRefl (der Γ) ,, TyRefl (dTy A A=)) ,, TyRefl (WeakTy (dTy A A=))) ,, congTyEq refl weakenTy-weakenTy (TyRefl (WeakTy (WeakTy (dTy A A=)))))) (congTmTy (! (weakenTy-weakenTy {k = prev last} ∙ ap weakenTy weakenTy-weakenTy)) (VarPrev (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=)))))))-}

{-{A = (ctx A , subst3Ty (weakenTy' (prev (prev (prev last))) (getTy P)) (var last) (var last) (refl (weakenTy (getTy A)) (var last))) , der A , ConvTy (Subst3Ty {B = weakenTy (getTy A)} {C = weakenTy' (prev last) (weakenTy (getTy A))} {D = weakenTy' (prev (prev last)) (id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last))} (der Γ , dTy A A=) (WeakTy {T = getTy A} dP) (VarLast (dTy A A=)) (congTmTy (! (ap (λ z → substTy z (var last)) weakenTy-weakenTy ∙ substTy-weakenTy)) (VarLast (dTy A A=))) (congTmTy (ap-id-Ty (! (weakenTyInsert' (prev (prev last)) (weakenTy (weakenTy (getTy A))) (idMor _ , var last) (var last) ∙ weakenTyInsert (weakenTy (getTy A)) (idMor _) (var last) ∙ [idMor]Ty _ )) refl refl) (Refl (WeakTy (dTy A A=)) (VarLast (dTy A A=))))) (CtxTy=Ctx A A=)}-}
-- {-((_ , _) , (der A , ConvTy (Subst3Ty (der Γ , dTy A A=) (WeakTy dP) (VarLast (dTy A A=)) (congTmTy (! (weakenSubstTy (substTy (weakenTy' (prev last) (weakenTy (getTy A))) (var last)) (var last) ∙ ap (λ z → substTy z (var last)) weakenTy-weakenTy ∙ weakenSubstTy (weakenTy (getTy A)) (var last)) ∙ weakenSubstTy (substTy (weakenTy' (prev last) (weakenTy (getTy A))) (var last)) (var last)) (VarLast (dTy A A=))) (congTmTy (ap-id-Ty (! (weakenTyInsert' (prev (prev last)) (weakenTy (weakenTy (getTy A))) (idMor _ , var last) (var last) ∙ weakenTyInsert (weakenTy (getTy A)) (idMor _) (var last) ∙ ([idMor]Ty (weakenTy (getTy A))))) refl refl) (Refl (WeakTy (dTy A A=)) (VarLast (dTy A A=))))) (CtxTy=Ctx A A=)))-}
-- {-
-- jjStrS-// Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁ = dmorTm Γ (substTy (substTy (substTy (getTy P) (weakenTm (weakenTm (getTm p)))) (weakenTm (getTm b))) (getTm a)) (SubstTy (SubstTy (SubstTy {!!} (idMor+ ((der Γ , dTy A A=) , WeakTy (dTy A A=)) (WeakTm (WeakTm (dTm (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) p pₛ p₁))))) (idMor+ (der Γ , dTy A A=) (WeakTm (dTm A= b bₛ b₁)))) (idMor+ (der Γ) (dTm A= a aₛ a₁))) (jj (getTy A) (getTy P) (getTm d) (getTm a) (getTm b) (getTm p)) {!JJ (dTy A A=) ? (dTm ? d dₛ d₁)!}-}


jjStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : ftS (proj A) ≡ proj Γ) (A'= : ftS (proj A') ≡ proj Γ') {P P' : DCtx (suc (suc (suc (suc n))))} (rP : P ≃ P') (P= : ftS (proj P) ≡ T-ftP IdStrSynCCat (proj Γ) (proj A) A=) (P'= : ftS (proj P') ≡ T-ftP IdStrSynCCat (proj Γ') (proj A') A'=) {d d' : DMor (suc n) (suc (suc n))} (rd : d ≃ d') (dₛ : S.is-section (proj d)) (d'ₛ : S.is-section (proj d')) (d₁ : ∂₁S (proj d) ≡ T-d₁ reflStrSynCCat (proj Γ) (proj A) A= (proj P) P=) (d'₁ : ∂₁S (proj d') ≡ T-d₁ reflStrSynCCat (proj Γ') (proj A') A'= (proj P') P'=) {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : S.∂₁ (proj a) ≡ (proj A)) (a'₁ : ∂₁S (proj a') ≡ (proj A')) {b b' : DMor n (suc n)} (rb : b ≃ b') (bₛ : S.is-section (proj b)) (b'ₛ : S.is-section (proj b')) (b₁ : S.∂₁ (proj b) ≡ (proj A)) (b'₁ : ∂₁S (proj b') ≡ proj A') {p p' : DMor n (suc n)} (rp : p ≃ p') (pₛ : S.is-section (proj p)) (p'ₛ : S.is-section (proj p')) (p₁ : S.∂₁ (proj p) ≡ proj (IdStrS-// Γ A A= a aₛ a₁ b bₛ b₁)) (p'₁ : ∂₁S (proj p') ≡ proj (IdStrS-// Γ' A' A'= a' a'ₛ a'₁ b' b'ₛ b'₁)) → jjStrS-// Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁ ≡ jjStrS-// Γ' A' A'= P' P'= d' d'ₛ d'₁ a' a'ₛ a'₁ b' b'ₛ b'₁ p' p'ₛ p'₁
jjStrS-eq rΓ rA A= A'= rP P= P'= rd dₛ d'ₛ d₁ d'₁ ra aₛ a'ₛ a₁ a'₁ rb bₛ b'ₛ b₁ b'₁ rp pₛ p'ₛ p₁ p'₁ = #TODO#

jjStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ T-ftP IdStrSynCCat Γ A A=)
         (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ T-d₁ reflStrSynCCat Γ A A= P P=)
         (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A)
         (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ A)
         (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS Γ A A= a aₛ a₁ b bₛ b₁) → MorS n (suc n)
jjStrS = #TODO#S


jjStrₛS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ T-ftP IdStrSynCCat Γ A A=) (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ T-d₁ reflStrSynCCat Γ A A= P P=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ A) (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS Γ A A= a aₛ a₁ b bₛ b₁) → S.is-section (jjStrS Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁)
jjStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → //-elimP (λ p pₛ p₁ → #TODO#)))))))

jjStr₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ T-ftP IdStrSynCCat Γ A A=) (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ T-d₁ reflStrSynCCat Γ A A= P P=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ A) (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS Γ A A= a aₛ a₁ b bₛ b₁) → ∂₁S (jjStrS Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁) ≡ T-jjStr₁ IdStrSynCCat Γ A A= P P= a aₛ a₁ b bₛ b₁ p pₛ p₁
jjStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → //-elimP (λ p pₛ p₁ → #TODO#)))))))


jjStrSynCCat : CCatwithjj synCCat IdStrSynCCat reflStrSynCCat
CCatwithjj.jjStr jjStrSynCCat = jjStrS
CCatwithjj.jjStrₛ jjStrSynCCat {Γ = Γ} {A = A} {P = P} {d = d} {a = a} {b = b} {p = p} = jjStrₛS Γ A _ P _ d _ _ a _ _ b _ _ p _ _
CCatwithjj.jjStr₁ jjStrSynCCat {Γ = Γ} {A = A} {P = P} {d = d} {a = a} {b = b} {p = p} = jjStr₁S Γ A _ P _ d _ _ a _ _ b _ _ p _ _
CCatwithjj.jjStrNat' jjStrSynCCat = #TODO#

{- ElId= -}

elidStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)
                   (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁) → ElStrS i Γ (idStrS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStrₛS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStr₁S i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ IdStrS Γ (ElStrS i Γ a aₛ a₁) (ElStr=S i Γ a aₛ a₁) u uₛ u₁ v vₛ v₁
elidStrS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → eq (box (CtxRefl (der Γ) ,, ElId= (dTm refl a aₛ a₁) (dTm refl u uₛ u₁) (dTm refl v vₛ v₁)))))))


{- BetaJ (TODO) -}


betaIdStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ T-ftP IdStrSynCCat Γ A A=)
             (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ T-d₁ reflStrSynCCat Γ A A= P P=)
             (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
           → jjStrS Γ A A= P P= d dₛ d₁ a aₛ a₁ a aₛ a₁ (reflStrS Γ A A= a aₛ a₁) (reflStrₛS Γ A A= a aₛ a₁) (reflStr₁S Γ A A= a aₛ a₁) ≡ S.starTm a d (S.is-section₀ dₛ d₁ ∙ T-d₁= reflStrSynCCat) a₁
betaIdStrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ → #TODO#)))))
