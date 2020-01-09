{-# OPTIONS --rewriting --prop #-}

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

{- Unit -}

UnitStrS-// : (Γ : DCtx n) → DCtx (suc n)
UnitStrS-// Γ = dctx (der Γ , Unit)

UnitStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → UnitStrS-// Γ ≃ UnitStrS-// Γ'
UnitStrS-eq rΓ = box (unOb≃ rΓ ,, UnitCong)

UnitStrS : (Γ : ObS n) → ObS (suc n)
UnitStrS = //-elim-Ctx (λ Γ → proj (UnitStrS-// Γ))
                        (λ rΓ → proj= (UnitStrS-eq rΓ))

UnitStr=S : (Γ : ObS n) → ftS (UnitStrS Γ) ≡ Γ
UnitStr=S = //-elimP-Ctx (λ Γ → refl)


UnitStrSynCCat : CCatwithUnit synCCat
CCatwithUnit.UnitStr UnitStrSynCCat = UnitStrS
CCatwithUnit.UnitStr= UnitStrSynCCat = UnitStr=S _
CCatwithUnit.UnitStrNat' UnitStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → refl)))

{- unit -}

unitStrS-// : (i : ℕ) (Γ : DCtx n) → DMor n (suc n)
unitStrS-// i Γ = dmorTm Γ (uu i) UU (unit i) UnitUU

unitStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → unitStrS-// i Γ ≃ unitStrS-// i Γ'
unitStrS-eq i rΓ = dmorTm= dmorTmₛ dmorTmₛ rΓ UUCong UnitUUCong

unitStrS : (i : ℕ) (Γ : ObS n) → MorS n (suc n)
unitStrS i = //-elim-Ctx (λ Γ → proj (unitStrS-// i Γ))
                         (λ rΓ → proj= (unitStrS-eq i rΓ))

unitStrₛS : (i : ℕ) (Γ : ObS n) → S.is-section (unitStrS i Γ)
unitStrₛS  i = //-elimP-Ctx (λ Γ → dmorTmₛ)

unitStr₁S : (i : ℕ) (Γ : ObS n) → S.∂₁ (unitStrS i Γ) ≡ UUStrS i Γ
unitStr₁S i = //-elimP-Ctx (λ Γ → refl)

unitStrSynCCat : CCatwithunit synCCat UUStrSynCCat
CCatwithunit.unitStr unitStrSynCCat = unitStrS
CCatwithunit.unitStrₛ unitStrSynCCat {Γ = Γ} = unitStrₛS _ Γ
CCatwithunit.unitStr₁ unitStrSynCCat {Γ = Γ} = unitStr₁S _ Γ
CCatwithunit.unitStrNat' unitStrSynCCat = //-elimP (λ g → JforNat (//-elimP-Ctx (λ Γ g₁ → refl)))

{- tt -}

ttStrS-// : (Γ : DCtx n) → DMor n (suc n)
ttStrS-// Γ = dmorTm Γ unit Unit tt TT

ttStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → ttStrS-// Γ ≃ ttStrS-// Γ'
ttStrS-eq rΓ = dmorTm= dmorTmₛ dmorTmₛ rΓ UnitCong TTCong

ttStrS : (Γ : ObS n) → MorS n (suc n)
ttStrS = //-elim-Ctx (λ Γ → proj (ttStrS-// Γ)) (λ rΓ → proj= (ttStrS-eq rΓ))

ttStrₛS : (Γ : ObS n) → S.is-section (ttStrS Γ)
ttStrₛS = //-elimP (λ Γ → dmorTmₛ)

ttStr₁S : (Γ : ObS n) → S.∂₁ (ttStrS Γ) ≡ UnitStrS Γ
ttStr₁S = //-elimP-Ctx (λ Γ → refl)

ttStrSynCCat : CCatwithtt synCCat UnitStrSynCCat
CCatwithtt.ttStr ttStrSynCCat = ttStrS
CCatwithtt.ttStrₛ ttStrSynCCat {Γ = Γ} = ttStrₛS Γ
CCatwithtt.ttStr₁ ttStrSynCCat {Γ = Γ} = ttStr₁S Γ
CCatwithtt.ttStrNat' ttStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ g₁ → refl)))


{- unitelim -}

unitelimStrS-// : (Γ : DCtx n) (A : DCtx (suc (suc n))) (A= : ftS (proj A) ≡ UnitStrS (proj Γ)) (dtt : DMor n (suc n)) (dttₛ : S.is-section (proj dtt)) (dtt₁ : S.∂₁ (proj dtt) ≡ S.star (ttStrS (proj Γ)) (proj A) A= (ttStr₁S (proj Γ))) (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : S.∂₁ (proj u) ≡ UnitStrS (proj Γ)) → DMor n (suc n)
unitelimStrS-// Γ A A= dtt dttₛ dtt₁ u uₛ u₁ = dmorTm Γ (substTy (getTy A) (getTm u)) (SubstTy (dTy A A=) (idMor+ (der Γ) (dTm refl u uₛ u₁))) (unitelim (getTy A) (getTm dtt) (getTm u)) (Unitelim (dTy A A=) (dTm refl dtt dttₛ dtt₁) (dTm refl u uₛ u₁))

unitelimStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc (suc n))} (rA : A ≃ A') (A= : ftS (proj A) ≡ UnitStrS (proj Γ)) (A'= : ftS (proj A') ≡ UnitStrS (proj Γ')) {dtt dtt' : DMor n (suc n)} (rdtt : dtt ≃ dtt') (dttₛ : S.is-section (proj dtt)) (dtt'ₛ : S.is-section (proj dtt')) (dtt₁ : S.∂₁ (proj dtt) ≡ S.star (ttStrS (proj Γ)) (proj A) A= (ttStr₁S (proj Γ))) (dtt'₁ : S.∂₁ (proj dtt') ≡ S.star (ttStrS (proj Γ')) (proj A') A'= (ttStr₁S (proj Γ'))) {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : S.∂₁ (proj u) ≡ UnitStrS (proj Γ)) (u'₁ : S.∂₁ (proj u') ≡ UnitStrS (proj Γ')) → unitelimStrS-// Γ A A= dtt dttₛ dtt₁ u uₛ u₁ ≃ unitelimStrS-// Γ' A' A'= dtt' dtt'ₛ dtt'₁ u' u'ₛ u'₁
unitelimStrS-eq {Γ = Γ} {Γ'} rΓ rA A= A'= rdtt dttₛ dtt'ₛ dtt₁ dtt'₁ ru uₛ u'ₛ u₁ u'₁ = dmorTm= dmorTmₛ dmorTmₛ rΓ
                                                                                                (SubstTyFullEq' (der Γ) (der Γ , Unit)
                                                                                                                (dTy= rA A=)
                                                                                                                (idMor+= (der Γ) (dTm= refl ru uₛ u'ₛ u₁ u'₁)))
                                                                                                (UnitelimCong (dTy= rA A=) (dTm= refl rdtt dttₛ dtt'ₛ dtt₁ dtt'₁) (dTm= refl ru uₛ u'ₛ u₁ u'₁))

unitelimStrS : (Γ : ObS n) (A : ObS (suc (suc n))) (A= : ftS A ≡ UnitStrS Γ) (dtt : MorS n (suc n)) (dttₛ : S.is-section dtt) (dtt₁ : S.∂₁ dtt ≡ S.star (ttStrS Γ) A A= (ttStr₁S Γ)) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ UnitStrS Γ) → MorS n (suc n)
unitelimStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Tm (λ dtt dttₛ dtt₁ → (//-elim-Tm (λ u uₛ u₁ → proj (unitelimStrS-// Γ A A= dtt dttₛ dtt₁ u uₛ u₁))
                                                                                                 (λ ru uₛ u'ₛ u₁ u'₁ → proj= (unitelimStrS-eq (ref Γ) (ref A) A= A= (ref dtt) dttₛ dttₛ dtt₁ dtt₁ ru uₛ u'ₛ u₁ u'₁))))
                                                                  (λ rdtt dttₛ dtt'ₛ dtt₁ dtt'₁ → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (unitelimStrS-eq (ref Γ) (ref A) A= A= rdtt dttₛ dtt'ₛ dtt₁ dtt'₁ (ref u) uₛ uₛ u₁ u₁'))))
                                             (λ rA A= A'= → //-elimP-Tm (λ dtt dttₛ dtt₁ dtt₁' → (//-elimP-Tm (λ u uₛ u₁ u₁' → proj= (unitelimStrS-eq (ref Γ) rA A= A'= (ref dtt) dttₛ dttₛ dtt₁ dtt₁' (ref u) uₛ uₛ u₁ u₁'))))))
                           (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Tm (λ dtt dttₛ dtt₁ dtt₁' → (//-elimP-Tm (λ u uₛ u₁ u₁' → proj= (unitelimStrS-eq rΓ (ref A) A= A=' (ref dtt) dttₛ dttₛ dtt₁ dtt₁' (ref u) uₛ uₛ u₁ u₁'))))))

unitelimStrₛS : (Γ : ObS n) (A : ObS (suc (suc n))) (A= : ftS A ≡ UnitStrS Γ) (dtt : MorS n (suc n)) (dttₛ : S.is-section dtt) (dtt₁ : S.∂₁ dtt ≡ S.star (ttStrS Γ) A A= (ttStr₁S Γ)) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ UnitStrS Γ) → S.is-section (unitelimStrS Γ A A= dtt dttₛ dtt₁ u uₛ u₁)
unitelimStrₛS = //-elimP-Ctx (λ Γ → //-elimP (λ A A= → //-elimP (λ dtt dttₛ dtt₁ → //-elimP (λ u uₛ u₁ → dmorTmₛ))))

unitelimStr₁S : (Γ : ObS n) (A : ObS (suc (suc n))) (A= : ftS A ≡ UnitStrS Γ) (dtt : MorS n (suc n)) (dttₛ : S.is-section dtt) (dtt₁ : S.∂₁ dtt ≡ S.star (ttStrS Γ) A A= (ttStr₁S Γ)) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ UnitStrS Γ) → S.∂₁ (unitelimStrS Γ A A= dtt dttₛ dtt₁ u uₛ u₁) ≡ S.star u A A= u₁
unitelimStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ dtt dttₛ dtt₁ → //-elimP (λ u uₛ u₁ → eq (box (CtxSymm (reflectOb (S.is-section₀ uₛ u₁)) ,, SubstTyMorEq (dTy A A=) (idMor+ (der Γ) (dTm refl u uₛ u₁)) (MorSymm (der Γ) (der Γ , Unit) (morTm=idMorTm refl u uₛ u₁))))))))

unitelimStrSynCCat : CCatwithunitelim synCCat UnitStrSynCCat ttStrSynCCat
CCatwithunitelim.unitelimStr unitelimStrSynCCat = unitelimStrS
CCatwithunitelim.unitelimStrₛ unitelimStrSynCCat {Γ = Γ} {A = A} {dtt = dtt} {u = u} = unitelimStrₛS Γ A _ dtt _ _ u _ _
CCatwithunitelim.unitelimStr₁ unitelimStrSynCCat {Γ = Γ} {A = A} {dtt = dtt} {u = u} = unitelimStr₁S Γ A _ dtt _ _ u _ _
CCatwithunitelim.unitelimStrNat' unitelimStrSynCCat = //-elimP (λ g → JforNat (//-elimP-Ctx (λ Γ → //-elimP (λ A A= → //-elimP (λ dtt dttₛ dtt₁ → //-elimP (λ u uₛ u₁ g₁ → up-to-rhsTyEq (ap (_[_]Ty (substTy (getTy A) (getTm u))) (idMor[]Mor (mor g)) ∙ []Ty-substTy)))))))

{- ElUnit= -}

elunitStrS : (i : ℕ) (Γ : ObS n) → ElStrS i Γ (unitStrS i Γ) (unitStrₛS i Γ) (unitStr₁S i Γ) ≡ UnitStrS Γ
elunitStrS i = //-elimP (λ Γ → eq (box (CtxRefl (der Γ) ,, ElUnit=)))

{- BetaUnit -}

betaUnitStrS : (Γ : ObS n) (A : ObS (suc (suc n))) (A= : ftS A ≡ UnitStrS Γ) (dtt : MorS n (suc n)) (dttₛ : S.is-section dtt) (dtt₁ : S.∂₁ dtt ≡ S.star (ttStrS Γ) A A= (ttStr₁S Γ))
             → unitelimStrS Γ A A= dtt dttₛ dtt₁ (ttStrS Γ) (ttStrₛS Γ) (ttStr₁S Γ) ≡ dtt
betaUnitStrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ dtt dttₛ dtt₁ → eq (box (CtxSymm (reflectOb (S.is-section₀ dttₛ dtt₁))) (CtxSymm (reflectOb dtt₁)) (MorTran (der Γ) (der Γ , SubstTy (dTy A A=) (idMor+ (der Γ) TT)) (idMor+= (der Γ) (BetaUnit (dTy A A=) (dTm refl dtt dttₛ dtt₁))) (MorSymm (der Γ) (der Γ , SubstTy (dTy A A=) (idMor+ (der Γ) TT)) (morTm=idMorTm refl dtt dttₛ dtt₁)))))))
