{-# OPTIONS --rewriting --prop --without-K --allow-unsolved-metas #-}

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


{- Nat -}

NatStrS-// : DCtx n → DCtx (suc n)
NatStrS-// Γ = ((ctx Γ , nat) , (der Γ , Nat))

NatStrS-eq : {Γ Γ' : DCtx n} → Γ ≃ Γ' → proj {R = ObEquiv} (NatStrS-// Γ) ≡ proj (NatStrS-// Γ')
NatStrS-eq dΓ= = eq (box (unOb≃ dΓ= ,, NatCong))

NatStrS : ObS n → ObS (suc n)
NatStrS = //-elim-Ctx (λ Γ → proj (NatStrS-// Γ)) (λ rΓ → proj= (NatStrS-eq rΓ))

NatStr=S : (Γ : ObS n) → ftS (NatStrS Γ) ≡ Γ
NatStr=S = //-elimP (λ Γ → refl)

NatStrNatS : (g : MorS n m) (Γ : ObS m) (g₁ : ∂₁S g ≡ Γ) → S.star g (NatStrS Γ) (NatStr=S Γ) g₁ ≡ NatStrS (∂₀S g)
NatStrNatS = //-elimP (λ g → //-elimP (λ Γ g₁ → refl))

NatStrSynCCat : CCatwithNat synCCat
CCatwithNat.NatStr NatStrSynCCat = NatStrS
CCatwithNat.NatStr= NatStrSynCCat = NatStr=S _
CCatwithNat.NatStrNat' NatStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → refl)))


{- nat -}

natStrS-// : (i : ℕ) (Γ : DCtx n) → DMor n (suc n)
natStrS-// i Γ = dmorTm Γ (uu i) UU (nat i) NatUU
 
natStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → proj {R = MorEquiv} (natStrS-// i Γ) ≡ proj (natStrS-// i Γ')
natStrS-eq i {Γ = Γ} {Γ'} rΓ = dmorTm= rΓ UU UU UUCong NatUU NatUU NatUUCong

natStrS : (i : ℕ) (Γ : ObS n) → MorS n (suc n)
natStrS i = //-elim-Ctx (λ Γ → proj (natStrS-// i Γ)) (λ rΓ → proj= (natStrS-eq i rΓ))

natStrₛS : (i : ℕ) (Γ : ObS n) → S.is-section (natStrS i Γ)
natStrₛS i = //-elimP (λ Γ → dmorTmₛ UU NatUU)

natStr₁S : (i : ℕ) (Γ : ObS n) → ∂₁S (natStrS i Γ) ≡ UUStrS i Γ
natStr₁S i = //-elimP (λ Γ → refl)

natStrSynCCat : CCatwithnat synCCat UUStrSynCCat
CCatwithnat.natStr natStrSynCCat = natStrS
CCatwithnat.natStrₛ natStrSynCCat {Γ = Γ} = natStrₛS _ Γ
CCatwithnat.natStr₁ natStrSynCCat {Γ = Γ} = natStr₁S _ Γ
CCatwithnat.natStrNat' natStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ g₁ → refl)))


{- zero -}

zeroStrS-// : (Γ : DCtx n) → DMor n (suc n)
zeroStrS-// Γ = dmorTm Γ nat Nat zero Zero

zeroStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → proj {R = MorEquiv} (zeroStrS-// Γ) ≡ proj (zeroStrS-// Γ')
zeroStrS-eq rΓ = dmorTm= rΓ Nat Nat NatCong Zero Zero ZeroCong

zeroStrS : (Γ : ObS n) → MorS n (suc n)
zeroStrS = //-rec (λ Γ → proj (zeroStrS-// Γ)) (λ rΓ → zeroStrS-eq rΓ)

zeroStrₛS : (Γ : ObS n) → S.is-section (zeroStrS Γ)
zeroStrₛS = //-elimP (λ Γ → dmorTmₛ Nat Zero)

zeroStr₁S : (Γ : ObS n) → ∂₁S (zeroStrS Γ) ≡ NatStrS Γ
zeroStr₁S = //-elimP (λ Γ → refl)

zeroStrSynCCat : CCatwithzero synCCat NatStrSynCCat
CCatwithzero.zeroStr zeroStrSynCCat = zeroStrS 
CCatwithzero.zeroStrₛ zeroStrSynCCat {Γ = Γ} = zeroStrₛS Γ
CCatwithzero.zeroStr₁ zeroStrSynCCat {Γ = Γ} = zeroStr₁S Γ
CCatwithzero.zeroStrNat' zeroStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ g₁ → refl)))


{- suc -}

sucStrS-// : (Γ : DCtx n) (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (proj Γ)) → DMor n (suc n)
sucStrS-// Γ u uₛ u₁ = dmorTm Γ nat Nat (suc (getTm u)) (Suc (dTm refl u uₛ u₁))

sucStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : _) (u'ₛ : _) (u₁ : _) (u'₁ : _) → proj {R = MorEquiv} (sucStrS-// Γ u uₛ u₁) ≡ proj (sucStrS-// Γ' u' u'ₛ u'₁)
sucStrS-eq rΓ ru uₛ u'ₛ u₁ u'₁ = dmorTm= rΓ Nat Nat NatCong (Suc (dTm refl _ uₛ u₁)) (Suc (dTm refl _ u'ₛ u'₁)) (SucCong (dTm= (box (unOb≃ rΓ ,, TyRefl Nat)) refl ru uₛ u'ₛ u₁ u'₁))

sucStrS : (Γ : ObS n) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ) → MorS n (suc n)
sucStrS = //-elim-Ctx (λ Γ → //-elim-Tm (λ u uₛ u₁ → proj (sucStrS-// Γ u uₛ u₁))
                                        (λ ru uₛ u'ₛ u₁ u'₁ → proj= (sucStrS-eq (ref Γ) ru uₛ u'ₛ u₁ u'₁)))
                      (λ rΓ → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (sucStrS-eq rΓ (ref u) uₛ uₛ u₁ u₁')))

sucStrₛS : (Γ : ObS n) (u : MorS n (suc n)) {uₛ : S.is-section u} {u₁ : ∂₁S u ≡ NatStrS Γ} → S.is-section (sucStrS Γ u uₛ u₁)
sucStrₛS = //-elimP (λ Γ → //-elimP (λ u {uₛ} {u₁} → dmorTmₛ Nat (Suc (dTm refl u uₛ u₁))))

sucStr₁S : (Γ : ObS n) (u : MorS n (suc n)) {uₛ : S.is-section u} {u₁ : ∂₁S u ≡ NatStrS Γ} → ∂₁S (sucStrS Γ u uₛ u₁) ≡ NatStrS Γ
sucStr₁S = //-elimP (λ Γ → //-elimP (λ u → refl))

sucStrSynCCat : CCatwithsuc synCCat NatStrSynCCat
CCatwithsuc.sucStr sucStrSynCCat = sucStrS
CCatwithsuc.sucStrₛ sucStrSynCCat {Γ = Γ} {u = u} = sucStrₛS Γ u
CCatwithsuc.sucStr₁ sucStrSynCCat {Γ = Γ} {u = u} = sucStr₁S Γ u
CCatwithsuc.sucStrNat' sucStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ u uₛ u₁ g₁ → refl))))


{- natelim -}

natelimStrS-// : (Γ : DCtx n) (P : DCtx (suc (suc n))) (P= : ftS (proj P) ≡ NatStrS (proj Γ))
                 (dO : DMor n (suc n)) (dOₛ : S.is-section (proj dO)) (dO₁ : ∂₁S (proj dO) ≡ S.star (zeroStrS (proj Γ)) (proj P) P= (zeroStr₁S (proj Γ)))
                 (dS : DMor (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section (proj dS)) (dS₁ : ∂₁S (proj dS) ≡ T-dS₁ sucStrSynCCat (proj Γ) (proj P) P=)
                 (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (proj Γ))
                 → DMor n (suc n)
natelimStrS-// Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁ = let fixSubstTyP = (! (weaken[]Ty _ _ last) ∙ ap weakenTy ([idMor]Ty _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty (getTy P)) (ap (λ z → z , suc (var last)) (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _)) ∙  ! (weakenTyInsert' _ _ _ _))) in
               dmorTm Γ (substTy (getTy P) (getTm u)) (SubstTy (dTy P P=) (idMor+ (der Γ) (dTm refl u uₛ u₁)))
                        (natelim (getTy P) (getTm dO) (getTm dS) (getTm u))
                        (Natelim (dTy P P=)
                                 (dTm refl dO dOₛ dO₁)
                                 (congTmTy fixSubstTyP (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (! (eq (box (CtxTy=Ctx P P=)))) dS dSₛ dS₁))
                                 (dTm refl u uₛ u₁))

natelimStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {P P' : DCtx (suc (suc n))} (rP : P ≃ P') (P= : ftS (proj P) ≡ NatStrS (proj Γ)) (P'= : ftS (proj P') ≡ NatStrS (proj Γ')) {dO dO' : DMor n (suc n)} (rdO : dO ≃ dO') (dOₛ : S.is-section (proj dO)) (dO'ₛ : S.is-section (proj dO')) (dO₁ : ∂₁S (proj dO) ≡ S.star (zeroStrS (proj Γ)) (proj P) P= (zeroStr₁S (proj Γ))) (dO'₁ : ∂₁S (proj dO') ≡ S.star (zeroStrS (proj Γ')) (proj P') P'= (zeroStr₁S (proj Γ')))
                   {dS dS' : DMor (suc (suc n)) (suc (suc (suc n)))} (rdS : dS ≃ dS') (dSₛ : S.is-section (proj dS))(dS'ₛ : S.is-section (proj dS'))
                   (dS₁ : ∂₁S (proj dS) ≡  T-dS₁ sucStrSynCCat (proj Γ) (proj P) P=)
                   (dS'₁ : ∂₁S (proj dS') ≡ T-dS₁ sucStrSynCCat (proj Γ') (proj P') P'=)
                   {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : ∂₁S (proj u) ≡ NatStrS (proj Γ)) (u'₁ : ∂₁S (proj u') ≡ NatStrS (proj Γ')) → proj {R = MorEquiv} (natelimStrS-// Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) ≡ proj (natelimStrS-// Γ' P' P'= dO' dO'ₛ dO'₁ dS' dS'ₛ dS'₁ u' u'ₛ u'₁)
natelimStrS-eq {Γ = Γ} {Γ'} rΓ {P} {P'} rP P= P'= {dO} {dO'} rdO dOₛ dO'ₛ dO₁ dO'₁ {dS} {dS'} rdS dSₛ dS'ₛ dS₁ dS'₁ {u} {u'} ru uₛ u'ₛ u₁ u'₁ =
                  let fixSubstTy X = (! (weaken[]Ty _ _ last) ∙ ap weakenTy ([idMor]Ty _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty (getTy X)) (ap (λ z → z , suc (var last)) (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _)) ∙  ! (weakenTyInsert' _ _ _ _)))
                  in  
               dmorTm= rΓ (SubstTy (dTy P P=) (idMor+ (der Γ) (dTm refl u uₛ u₁)))
                          (SubstTy (dTy P' P'=) (idMor+ (der Γ') (dTm refl u' u'ₛ u'₁)))
                          (SubstTyMorEq2 (der Γ) (der Γ , Nat) (dTy= rP P=) (idMor+= (der Γ) (dTm= (box (unOb≃ rΓ ,, NatCong)) refl ru uₛ u'ₛ u₁ u'₁)))
                          (Natelim (dTy P P=)
                                   (dTm refl dO dOₛ dO₁)
                                   (congTmTy (fixSubstTy P) (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (eq (box (CtxSymm (CtxTy=Ctx P P=)))) dS dSₛ dS₁))
                                   (dTm refl u uₛ u₁))
                          (Natelim (dTy P' P'=) 
                                   (dTm refl dO' dO'ₛ dO'₁)
                                   (congTmTy (fixSubstTy P') (dTm {Γ = (((_ , _) , _) , ((der Γ' , Nat) , dTy P' P'=))} (eq (box (CtxSymm (CtxTy=Ctx P' P'=)))) dS' dS'ₛ dS'₁))
                                   (dTm refl u' u'ₛ u'₁))
                          (NatelimCong (dTy P P=) (dTy= rP P=)
                                       (dTm= (box (unOb≃ rΓ ,, SubstTyMorEq2 (der Γ) (der Γ , Nat) (dTy= rP P=) (idMor+= (der Γ) ZeroCong))) refl rdO dOₛ dO'ₛ dO₁ dO'₁)
                                       (congTmEqTy (fixSubstTy P) (dTm= {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (box (unOb≃ rP ,, SubstTyEq (SubstTyEq (SubstTyEq (dTy= rP P=) ((WeakMor _ (WeakMor _ (idMorDerivable (der Γ)))) , (VarLast Nat))) ((idMorDerivable (der Γ , Nat)) , (Suc (VarLast Nat)))) (ConvMor (WeakMor _ (WeakMor _ (idMorDerivable (der Γ)))) (CtxTy=Ctx P P=) (CtxRefl (der Γ)) , ConvTm (VarPrev Nat (VarLast Nat)) (CtxTy=Ctx P P=)))) (eq (box (CtxSymm (CtxTy=Ctx P P=)))) rdS dSₛ dS'ₛ dS₁ dS'₁))
                                       (dTm= (box (unOb≃ rΓ ,, NatCong)) refl ru uₛ u'ₛ u₁ u'₁))
               
natelimStrS : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
              (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : ∂₁S dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
              (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : ∂₁S dS ≡ T-dS₁ sucStrSynCCat Γ P P=)
              (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ)
              → MorS n (suc n)
natelimStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ P P= → //-elim-Tm (λ dO dOₛ dO₁ → //-elim-Tm (λ dS dSₛ dS₁ → //-elim-Tm (λ u uₛ u₁ → proj (natelimStrS-// Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁))
                                                                                                                       (λ ru uₛ u'ₛ u₁ u'₁ → proj= (natelimStrS-eq (ref Γ) (ref P) P= P= (ref dO) dOₛ dOₛ dO₁ dO₁ (ref dS) dSₛ dSₛ dS₁ dS₁ ru uₛ u'ₛ u₁ u'₁)))
                                                                                            (λ rdS dSₛ dS'ₛ dS₁ dS'₁ → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (natelimStrS-eq (ref Γ) (ref P) P= P= (ref dO) dOₛ dOₛ dO₁ dO₁ rdS dSₛ dS'ₛ dS₁ dS'₁ (ref u) uₛ uₛ u₁ u₁'))))
                                                                 (λ rdO dOₛ dO'ₛ dO₁ dO'₁ → //-elimP-Tm (λ dS dSₛ dS₁ dS₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (natelimStrS-eq (ref Γ) (ref P) P= P= rdO dOₛ dO'ₛ dO₁ dO'₁ (ref dS) dSₛ dSₛ dS₁ dS₁' (ref u) uₛ uₛ u₁ u₁')))))
                                            (λ rP P= P'= → //-elimP-Tm (λ dO dOₛ dO₁ dO₁' → //-elimP-Tm (λ dS dSₛ dS₁ dS₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (natelimStrS-eq (ref Γ) rP P= P'= (ref dO) dOₛ dOₛ dO₁ dO₁' (ref dS) dSₛ dSₛ dS₁ dS₁' (ref u) uₛ uₛ u₁ u₁'))))))
                          (λ rΓ → //-elimP-Ty (λ P P= P=' → //-elimP-Tm (λ dO dOₛ dO₁ dO₁' → //-elimP-Tm (λ dS dSₛ dS₁ dS₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (natelimStrS-eq rΓ (ref P) P= P=' (ref dO) dOₛ dOₛ dO₁ dO₁' (ref dS) dSₛ dSₛ dS₁ dS₁' (ref u) uₛ uₛ u₁ u₁'))))))

abstract
 natelimStrₛS : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
               (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : ∂₁S dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
               (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : ∂₁S dS ≡ T-dS₁ sucStrSynCCat Γ P P=)
               (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ) → S.is-section (natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)
 natelimStrₛS = let fixSubstTy X = (! (weaken[]Ty _ _ last) ∙ ap weakenTy ([idMor]Ty _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty (getTy X)) (ap (λ z → z , suc (var last)) (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _)) ∙  ! (weakenTyInsert' _ _ _ _)))
               in
               //-elimP (λ Γ → //-elimP (λ P P= → //-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → //-elimP (λ u uₛ u₁ →  dmorTmₛ (SubstTy (dTy P P=) (idMor+ (der Γ) (dTm refl u uₛ u₁))) (Natelim (dTy P P=)
                                   (dTm refl dO dOₛ dO₁)
                                   (congTmTy (fixSubstTy P) (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (eq (box (CtxSymm (CtxTy=Ctx P P=)))) dS dSₛ dS₁))
                                   (dTm refl u uₛ u₁)))))))

 natelimStr₁S : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
               (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : ∂₁S dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
               (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : ∂₁S dS ≡ T-dS₁ sucStrSynCCat Γ P P=)
               (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ) → S.∂₁ (natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) ≡ S.star u P P= u₁
 natelimStr₁S = //-elimP (λ Γ → //-elimP (λ P P= → //-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → //-elimP (λ u uₛ u₁ → eq (box (CtxSymm (reflectOb (S.is-section₀ uₛ u₁)) ,, SubstTyMorEq (dTy P P=) (idMor+ (der Γ) (dTm refl u uₛ u₁)) (ConvMorEq (MorSymm (der (lhs u)) (der (rhs u)) (morTm=idMorTm' uₛ)) (reflectOb (S.is-section₀ uₛ u₁)) (reflectOb u₁)))))))))

natelimStrSynCCat : CCatwithnatelim synCCat NatStrSynCCat zeroStrSynCCat sucStrSynCCat
CCatwithnatelim.natelimStr natelimStrSynCCat = natelimStrS
CCatwithnatelim.natelimStrₛ natelimStrSynCCat {Γ = Γ} {P = P} {dO = dO} {dS = dS} {u = u} = natelimStrₛS Γ P _ dO _ _ dS _ _ u _ _
CCatwithnatelim.natelimStr₁ natelimStrSynCCat {Γ = Γ} {P = P} {dO = dO} {dS = dS} {u = u} = natelimStr₁S Γ P _ dO _ _ dS _ _ u _ _
CCatwithnatelim.natelimStrNat' natelimStrSynCCat = {!//-elimP (λ g → JforNat (//-elimP (λ g → //-elimP (λ Γ → //-elimP (λ P P= → //-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → //-elimP (λ u uₛ u₁ g₁ → up-to-rhsTyEq ?))))))))!}


{- ElNat= -}

elnatStrS : (i : ℕ) (Γ : ObS n) → ElStrS i Γ (natStrS i Γ) (natStrₛS i Γ) (natStr₁S i Γ) ≡ NatStrS Γ
elnatStrS i = //-elimP (λ Γ → eq (box (CtxRefl (der Γ) ,, ElNat=)))


-- {- BetaNatZero -}

-- betaNatZeroStrS : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
--                (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : S.∂₁ dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
--                (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : S.∂₁ dS ≡ T-dS₁ sucStrSynCCat Γ P P=) →
--                natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ (zeroStrS Γ) (zeroStrₛS Γ) (zeroStr₁S Γ)  ≡ dO               
-- betaNatZeroStrS = let fixSubstTy X = (! (weaken[]Ty _ _ last) ∙ ap weakenTy ([idMor]Ty _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty (getTy X)) (ap (λ z → z , suc (var last)) (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _)) ∙  ! (weakenTyInsert' _ _ _ _)))                      
--                   in
--                   //-elimP (λ Γ → //-elimP (λ P P= → (//-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → eq (box
--                            (CtxSymm (reflectOb (S.is-section₀ dOₛ dO₁)))
--                            (CtxSymm (reflectOb dO₁))
--                            (MorTran (der Γ) (der Γ , SubstTy (dTy P P=) (idMor+ (der Γ) Zero)) (idMor+= (der Γ) (BetaNatZero (dTy P P=) (dTm refl dO dOₛ dO₁) (congTmTy (fixSubstTy P) (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (eq (box (CtxSymm (CtxTy=Ctx P P=)))) dS dSₛ dS₁)))) (MorSymm (der Γ) (der Γ , SubstTy (dTy P P=) (idMor+ (der Γ) Zero)) (morTm=idMorTm refl dO dOₛ dO₁)))))))))


-- up-to-rhsTyEq2 : {Γ : DCtx n} {A B : TyExpr n} {δ : Mor n n} {u u' : TmExpr n} {w₁ : _} {w₂ : _} {w₃ : _} {w₄ : _} → Derivable (ctx Γ ⊢ A == B) → Derivable (ctx Γ ⊢ u == u' :> A)
--                → proj {R = MorEquiv} (dmor Γ ((ctx Γ , A) , w₁) (δ , u) w₂) ≡ proj (dmor Γ ((ctx Γ , B) , w₃) (δ , u') w₄)
-- up-to-rhsTyEq2 p q = eq (box {!CtxRefl (der Γ)!} ({!!} ,, p) ({!!} , {!!}))

-- {- BetaNatSuc -}

-- betaNatSucStrS : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
--                (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : S.∂₁ dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
--                (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : S.∂₁ dS ≡ T-dS₁ sucStrSynCCat Γ P P=)
--                (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ) →
--                natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ (sucStrS Γ u uₛ u₁) (sucStrₛS Γ u) (sucStr₁S Γ u) ≡ Tm-substdS natelimStrSynCCat Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁ 
-- betaNatSucStrS = let fixSubstTy X = (! (weaken[]Ty _ _ last) ∙ ap weakenTy ([idMor]Ty _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty (getTy X)) (ap (λ z → z , suc (var last)) (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _)) ∙  ! (weakenTyInsert' _ _ _ _)))                      
--                  in
--                 //-elimP (λ Γ → //-elimP (λ P P= → (//-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → //-elimP (λ u uₛ u₁ → up-to-rhsTyEq2 {!dTy= (reflect (! dS₁)) refl!} {!(congTmEq refl {!!} refl (BetaNatSuc (dTy P P=) (dTm refl dO dOₛ dO₁) (congTmTy (fixSubstTy P) (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (eq (box (CtxSymm (CtxTy=Ctx P P=)))) dS dSₛ dS₁)) (dTm refl u uₛ u₁)))!}))))))



-- -- eq (box
-- --                   (CtxRefl (der Γ))
-- --                   (CtxRefl (der Γ) ,, TySymm (TyTran {!!} (congTyEq (! ([]Ty-assoc _ _ _ ∙ ap (_[_]Ty (getTy (rhs dS))) (ap (λ z → (getLHS (mor dS) [ weakenMor (mor u) , var last ]Mor) [ z ]Mor) (ap (λ z → (z , natelim (getTy P) (getRHS (mor dO)) (getRHS (mor dS)) (getRHS (mor u)))) (weakenMorInsert _ _ _ ∙ (idMor[]Mor _))) ∙ []Mor-assoc (idMor _  , natelim (getTy P) (getRHS (mor dO)) (getRHS (mor dS)) (getRHS (mor u)))  (weakenMor (mor u) , var last) (getLHS (mor dS)) ∙ ap (_[_]Mor (getLHS (mor dS))) ((ap
-- --                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (λ z →
-- --                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  z Mor.,
-- --                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  natelim (getTy P) (getRHS (mor dO)) (getRHS (mor dS))
-- --                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (getRHS (mor u)))
-- --                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (weakenMorInsert (mor u) (idMor _) (natelim (getTy P) (getTm dO) (getTm dS) (getTm u)) ∙ [idMor]Mor (mor u))))))) refl (SubstTyMorEq2 {Δ = (ctx Γ , nat) , getTy P} (der Γ) ((der Γ , Nat) , dTy P P=) (congTyEq refl (fixSubstTy P) {!!}) {!!})) {!!}))
-- --                   (MorTran (der Γ) (der Γ , SubstTy (dTy P P=) (idMor+ (der Γ) (Suc (dTm refl u uₛ u₁))))
-- --                   (idMor+= (der Γ) (BetaNatSuc (dTy P P=) (dTm refl dO dOₛ dO₁) (congTmTy (fixSubstTy P) (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (eq (box (CtxSymm (CtxTy=Ctx P P=)))) dS dSₛ dS₁)) (dTm refl u uₛ u₁)))
-- --                   (idMor+= (der Γ) (congTmEq refl (ap (_[_]Tm (getRHS (mor dS))) (ap (λ z → z , natelim (getTy P) (getRHS (mor dO)) (getRHS (mor dS)) (getRHS (mor u))) (! (weakenMorInsert (mor u) (idMor _) (natelim (getTy P) (getRHS (mor dO)) (getRHS (mor dS)) (getRHS (mor u))) ∙ ([idMor]Mor (mor u))))) ∙ ! ([]Tm-assoc (idMor _ , natelim (getTy P) (getRHS (mor dO)) (getRHS (mor dS)) (getRHS (mor u))) (weakenMor (mor u) , var last) (getRHS (mor dS)))) (weakenTyInsert _ _ _ ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty (weakenTy' (prev last) (getTy P))) (ap (λ z → ((z , getTm u) , suc (getRHS (mor u)))) (weakenMorInsert _ _ _ ∙ idMor[]Mor _)) ∙ weakenTyInsert' (prev last) (getTy P) (idMor _ , suc (getRHS (mor u))) (getTm u)) (SubstTmMorEq ((congTmTy (fixSubstTy P) (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (eq (box (CtxSymm (CtxTy=Ctx P P=)))) dS dSₛ dS₁))) (idMor+ (der Γ) (dTm refl u uₛ u₁) , (Natelim (dTy P P=)
-- --                                    (dTm refl dO dOₛ dO₁)
-- --                                    (congTmTy (fixSubstTy P) (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (eq (box (CtxSymm (CtxTy=Ctx P P=)))) dS dSₛ dS₁))
-- --                                    (dTm refl u uₛ u₁))) (MorSymm (der Γ) (der Γ , Nat) (morTm=idMorTm refl u uₛ u₁) , TmRefl (Natelim (dTy P P=)
-- --                                    (dTm refl dO dOₛ dO₁)
-- --                                    (congTmTy (fixSubstTy P) (dTm {Γ = (((_ , _) , _) , ((der Γ , Nat) , dTy P P=))} (eq (box (CtxSymm (CtxTy=Ctx P P=)))) dS dSₛ dS₁))
-- --                                    (dTm refl u uₛ u₁))))))))))))))
