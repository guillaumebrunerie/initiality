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

{- Empty -}

EmptyStrS-// : (Γ : DCtx n) → DCtx (suc n)
EmptyStrS-// Γ = (ctx Γ , empty) , (der Γ , Empty)

EmptyStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → EmptyStrS-// Γ ≃ EmptyStrS-// Γ'
EmptyStrS-eq rΓ = box (unOb≃ rΓ ,, EmptyCong)

EmptyStrS : (Γ : ObS n) → ObS (suc n)
EmptyStrS = //-elim-Ctx (λ Γ → proj (EmptyStrS-// Γ))
                        (λ rΓ → proj= (EmptyStrS-eq rΓ))

EmptyStr=S : (Γ : ObS n) → ftS (EmptyStrS Γ) ≡ Γ
EmptyStr=S = //-elimP-Ctx (λ Γ → refl)


EmptyStrSynCCat : CCatwithEmpty synCCat
CCatwithEmpty.EmptyStr EmptyStrSynCCat = EmptyStrS
CCatwithEmpty.EmptyStr= EmptyStrSynCCat = EmptyStr=S _
CCatwithEmpty.EmptyStrNat' EmptyStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → refl)))

{- empty -}

emptyStrS-// : (i : ℕ) (Γ : DCtx n) → DMor n (suc n)
emptyStrS-// i Γ = dmorTm Γ (uu i) UU (empty i) EmptyUU

emptyStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → emptyStrS-// i Γ ≃ emptyStrS-// i Γ'
emptyStrS-eq i rΓ = dmorTm= (dmorTmₛ refl refl) (dmorTmₛ refl refl) rΓ UUCong EmptyUUCong

emptyStrS : (i : ℕ) (Γ : ObS n) → MorS n (suc n)
emptyStrS i = //-elim-Ctx (λ Γ → proj (emptyStrS-// i Γ))
                          (λ rΓ → proj= (emptyStrS-eq i rΓ))

emptyStrₛS : (i : ℕ) (Γ : ObS n) → S.is-section (emptyStrS i Γ)
emptyStrₛS  i = //-elimP (λ Γ → dmorTmₛ refl refl)

emptyStr₁S : (i : ℕ) (Γ : ObS n) → S.∂₁ (emptyStrS i Γ) ≡ UUStrS i Γ
emptyStr₁S i = //-elimP (λ Γ → refl)

emptyStrSynCCat : CCatwithempty synCCat UUStrSynCCat
CCatwithempty.emptyStr emptyStrSynCCat = emptyStrS
CCatwithempty.emptyStrₛ emptyStrSynCCat {Γ = Γ} = emptyStrₛS _ Γ
CCatwithempty.emptyStr₁ emptyStrSynCCat {Γ = Γ} = emptyStr₁S _ Γ
CCatwithempty.emptyStrNat' emptyStrSynCCat = //-elimP (λ g → JforNat (//-elimP-Ctx (λ Γ g₁ → refl)))

{- emptyelim -}

emptyelimStrS-// : (Γ : DCtx n) (A : DCtx (suc (suc n))) (A= : ftS (proj A) ≡ EmptyStrS (proj Γ)) (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : S.∂₁ (proj u) ≡ EmptyStrS (proj Γ)) → DMor n (suc n)
emptyelimStrS-// Γ A A= u uₛ u₁ = dmorTm Γ (substTy (getTy A) (getTm u)) (SubstTy (dTy A A=) (idMor+ (der Γ) (dTm refl u uₛ u₁))) (emptyelim (getTy A) (getTm u)) (Emptyelim (dTy A A=) (dTm refl u uₛ u₁))

emptyelimStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc (suc n))} (rA : A ≃ A') (A= : ftS (proj A) ≡ EmptyStrS (proj Γ)) (A'= : ftS (proj A') ≡ EmptyStrS (proj Γ')) {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : S.∂₁ (proj u) ≡ EmptyStrS (proj Γ)) (u'₁ : S.∂₁ (proj u') ≡ EmptyStrS (proj Γ')) → emptyelimStrS-// Γ A A= u uₛ u₁ ≃ emptyelimStrS-// Γ' A' A'= u' u'ₛ u'₁
emptyelimStrS-eq {Γ = Γ} {Γ'} rΓ {A} {A'} rA A= A'= ru uₛ u'ₛ u₁ u'₁ = dmorTm= (dmorTmₛ refl refl) (dmorTmₛ refl refl) rΓ (SubstTyMorEq2 (der Γ) (der Γ , Empty) (dTy= rA A=) (idMor+= (der Γ) (dTm= (box (unOb≃ rΓ ,, EmptyCong)) refl ru uₛ u'ₛ u₁ u'₁))) (EmptyelimCong (dTy= rA A=) (dTm= (box (unOb≃ rΓ ,, EmptyCong)) refl ru uₛ u'ₛ u₁ u'₁))

emptyelimStrS : (Γ : ObS n) (A : ObS (suc (suc n))) (A= : ftS A ≡ EmptyStrS Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ EmptyStrS Γ) → MorS n (suc n)
emptyelimStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Tm (λ u uₛ u₁ → proj (emptyelimStrS-// Γ A A= u uₛ u₁))
                                                                   (λ ru uₛ u'ₛ u₁ u'₁ → proj= (emptyelimStrS-eq (ref Γ) (ref A) A= A= ru uₛ u'ₛ u₁ u'₁)))
                                              (λ rA A= A'= → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (emptyelimStrS-eq (ref Γ) rA A= A'= (ref u) uₛ uₛ u₁ u₁'))))
                            (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (emptyelimStrS-eq rΓ (ref A) A= A=' (ref u) uₛ uₛ u₁ u₁'))))

emptyelimStrₛS : (Γ : ObS n) (A : ObS (suc (suc n))) (A= : ftS A ≡ EmptyStrS Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ EmptyStrS Γ) → S.is-section (emptyelimStrS Γ A A= u uₛ u₁)
emptyelimStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ u uₛ u₁ → dmorTmₛ refl refl)))

emptyelimStr₁S : (Γ : ObS n) (A : ObS (suc (suc n))) (A= : ftS A ≡ EmptyStrS Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ EmptyStrS Γ) → S.∂₁ (emptyelimStrS Γ A A= u uₛ u₁) ≡ S.star u A A= u₁
emptyelimStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ u uₛ u₁ → eq (box (CtxSymm (reflectOb (S.is-section₀ uₛ u₁)) ,, SubstTyMorEq (dTy A A=) (idMor+ (der Γ) (dTm refl u uₛ u₁)) (MorSymm (der Γ) (der Γ , Empty) (morTm=idMorTm refl u uₛ u₁)))))))

emptyelimStrSynCCat : CCatwithemptyelim synCCat EmptyStrSynCCat
CCatwithemptyelim.emptyelimStr emptyelimStrSynCCat = emptyelimStrS
CCatwithemptyelim.emptyelimStrₛ emptyelimStrSynCCat {Γ = Γ} {A = A} {u = u} = emptyelimStrₛS Γ A _ u _ _
CCatwithemptyelim.emptyelimStr₁ emptyelimStrSynCCat {Γ = Γ} {A = A} {u = u} = emptyelimStr₁S Γ A _ u _ _
CCatwithemptyelim.emptyelimStrNat' emptyelimStrSynCCat = //-elimP (λ g → JforNat (//-elimP-Ctx (λ Γ → //-elimP (λ A A= → //-elimP (λ u uₛ u₁ g₁ → up-to-rhsTyEq (ap (_[_]Ty (substTy (getTy A) (getTm u))) (idMor[]Mor (mor g)) ∙ []Ty-substTy))))))

{- ElEmpty= -}

elemptyStrS : (i : ℕ) (Γ : ObS n) → ElStrS i Γ (emptyStrS i Γ) (emptyStrₛS i Γ) (emptyStr₁S i Γ) ≡ EmptyStrS Γ
elemptyStrS i = //-elimP (λ Γ → eq (box (CtxRefl (der Γ) ,, ElEmpty=)))
