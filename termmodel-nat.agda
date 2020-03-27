{-# OPTIONS --rewriting --prop #-}

open import common
open import typetheory
open import syntx hiding (getTy)
open import rules 
open import contextualcat
open import quotients
open import termmodel-common
open import termmodel-synccat
open import termmodel-uuel

open CCat hiding (Mor) renaming (id to idC)


{- Nat -}

NatStrS-// : DCtx n → DCtx (suc n)
NatStrS-// Γ = dctx (der Γ , Nat)

NatStrS-eq : {Γ Γ' : DCtx n} → Γ ≃ Γ' → NatStrS-// Γ ≃ NatStrS-// Γ'
NatStrS-eq dΓ= = box (unOb≃ dΓ= , NatCong)

NatStrS : ObS n → ObS (suc n)
NatStrS = //-elim-Ctx (λ Γ → proj (NatStrS-// Γ)) (λ rΓ → proj= (NatStrS-eq rΓ))

NatStr=S : (Γ : ObS n) → ftS (NatStrS Γ) ≡ Γ
NatStr=S = //-elimP-Ctx (λ Γ → refl)

NatStrNatS : (g : MorS n m) (Γ : ObS m) (g₁ : ∂₁S g ≡ Γ) → S.star g (NatStrS Γ) (NatStr=S Γ) g₁ ≡ NatStrS (∂₀S g)
NatStrNatS = //-elimP (λ g → //-elimP (λ Γ g₁ → refl))

NatStrSynCCat : CCatwithNat synCCat
CCatwithNat.NatStr NatStrSynCCat = NatStrS
CCatwithNat.NatStr= NatStrSynCCat = NatStr=S _
CCatwithNat.NatStrNat' NatStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → refl)))


{- nat -}

natStrS-// : (i : ℕ) (Γ : DCtx n) → DMor n (suc n)
natStrS-// i Γ = dmorTm Γ (NatUU {i = i})
 
natStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → natStrS-// i Γ ≃ natStrS-// i Γ'
natStrS-eq i rΓ = dmorTm= dmorTmₛ dmorTmₛ rΓ UUCong NatUUCong

natStrS : (i : ℕ) (Γ : ObS n) → MorS n (suc n)
natStrS i = //-elim-Ctx (λ Γ → proj (natStrS-// i Γ)) (λ rΓ → proj= (natStrS-eq i rΓ))

natStrₛS : (i : ℕ) (Γ : ObS n) → S.is-section (natStrS i Γ)
natStrₛS i = //-elimP (λ Γ → dmorTmₛ)

natStr₁S : (i : ℕ) (Γ : ObS n) → ∂₁S (natStrS i Γ) ≡ UUStrS i Γ
natStr₁S i = //-elimP (λ Γ → refl)

natStrSynCCat : CCatwithnat synCCat UUStrSynCCat
CCatwithnat.natStr natStrSynCCat = natStrS
CCatwithnat.natStrₛ natStrSynCCat {Γ = Γ} = natStrₛS _ Γ
CCatwithnat.natStr₁ natStrSynCCat {Γ = Γ} = natStr₁S _ Γ
CCatwithnat.natStrNat' natStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ g₁ → refl)))


{- zero -}

zeroStrS-// : (Γ : DCtx n) → DMor n (suc n)
zeroStrS-// Γ = dmorTm Γ Zero

zeroStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') → zeroStrS-// Γ ≃ zeroStrS-// Γ'
zeroStrS-eq rΓ = dmorTm= dmorTmₛ dmorTmₛ rΓ NatCong ZeroCong

zeroStrS : (Γ : ObS n) → MorS n (suc n)
zeroStrS = //-elim-Ctx (λ Γ → proj (zeroStrS-// Γ)) (λ rΓ → proj= (zeroStrS-eq rΓ))

zeroStrₛS : (Γ : ObS n) → S.is-section (zeroStrS Γ)
zeroStrₛS = //-elimP (λ Γ → dmorTmₛ)

zeroStr₁S : (Γ : ObS n) → ∂₁S (zeroStrS Γ) ≡ NatStrS Γ
zeroStr₁S = //-elimP (λ Γ → refl)

zeroStrSynCCat : CCatwithzero synCCat NatStrSynCCat
CCatwithzero.zeroStr zeroStrSynCCat = zeroStrS 
CCatwithzero.zeroStrₛ zeroStrSynCCat {Γ = Γ} = zeroStrₛS Γ
CCatwithzero.zeroStr₁ zeroStrSynCCat {Γ = Γ} = zeroStr₁S Γ
CCatwithzero.zeroStrNat' zeroStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ g₁ → refl)))


{- suc -}
 
sucStrS-// : (Γ : DCtx n) (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (proj Γ)) → DMor n (suc n)
sucStrS-// Γ u uₛ u₁ = dmorTm Γ (Suc (dTm refl u uₛ u₁))

sucStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : _) (u'ₛ : _) (u₁ : _) (u'₁ : _) → sucStrS-// Γ u uₛ u₁ ≃ sucStrS-// Γ' u' u'ₛ u'₁
sucStrS-eq rΓ ru uₛ u'ₛ u₁ u'₁ = dmorTm= dmorTmₛ dmorTmₛ rΓ NatCong (SucCong (dTm= refl ru uₛ u'ₛ u₁ u'₁))

sucStrS : (Γ : ObS n) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ) → MorS n (suc n)
sucStrS = //-elim-Ctx (λ Γ → //-elim-Tm (λ u uₛ u₁ → proj (sucStrS-// Γ u uₛ u₁))
                                        (λ ru uₛ u'ₛ u₁ u'₁ → proj= (sucStrS-eq (ref Γ) ru uₛ u'ₛ u₁ u'₁)))
                      (λ rΓ → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (sucStrS-eq rΓ (ref u) uₛ uₛ u₁ u₁')))

sucStrₛS : (Γ : ObS n) (u : MorS n (suc n)) {uₛ : S.is-section u} {u₁ : ∂₁S u ≡ NatStrS Γ} → S.is-section (sucStrS Γ u uₛ u₁)
sucStrₛS = //-elimP (λ Γ → //-elimP (λ u {uₛ} {u₁} → dmorTmₛ))

sucStr₁S : (Γ : ObS n) (u : MorS n (suc n)) {uₛ : S.is-section u} {u₁ : ∂₁S u ≡ NatStrS Γ} → ∂₁S (sucStrS Γ u uₛ u₁) ≡ NatStrS Γ
sucStr₁S = //-elimP (λ Γ → //-elimP (λ u → refl))

sucStrSynCCat : CCatwithsuc synCCat NatStrSynCCat
CCatwithsuc.sucStr sucStrSynCCat = sucStrS
CCatwithsuc.sucStrₛ sucStrSynCCat {Γ = Γ} {u = u} = sucStrₛS Γ u
CCatwithsuc.sucStr₁ sucStrSynCCat {Γ = Γ} {u = u} = sucStr₁S Γ u
CCatwithsuc.sucStrNat' sucStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ u uₛ u₁ g₁ → refl))))

module sucS = CCatwithsuc sucStrSynCCat

{- natelim -} 

fixSubstTy : {X : TyExpr (suc n)}
           → weakenTy' (prev last) (weakenTy' (prev last) X) [ idMor _ , suc (var (prev last)) ]Ty
           ≡ ((X [ weakenMor (weakenMor (idMor n)) , var last ]Ty) [ weakenMor (weakenMor (idMor (suc n))) , var last ]Ty) [ idMor (suc (suc n)) , suc (var (prev last)) ]Ty
fixSubstTy = ap-[]Ty (weakenTy+-to-[]Ty ∙ ap-[]Ty weakenTy+-to-[]Ty refl) refl


natelimStrS-// : (Γ : DCtx n) (P : DCtx (suc (suc n))) (P= : ftS (proj P) ≡ NatStrS (proj Γ))
                 (dO : DMor n (suc n)) (dOₛ : S.is-section (proj dO)) (dO₁ : ∂₁S (proj dO) ≡ S.star (zeroStrS (proj Γ)) (proj P) P= (zeroStr₁S (proj Γ)))
                 (dS : DMor (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section (proj dS))
                 (dS₁ : ∂₁S (proj dS) ≡ sucS.T-dS₁ (proj Γ) (proj P) P=)
                 (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ NatStrS (proj Γ))
                 → DMor n (suc n)
natelimStrS-// Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁ =
  dmorTm Γ (Natelim (dTy P P=)
                    (dTm refl dO dOₛ dO₁)
                    ddS
                    (dTm refl u uₛ u₁))
         where  ddS : Derivable (((ctx Γ , nat) , getTy P) ⊢ getTm dS :> substTy (weakenTy' (prev last) (weakenTy' (prev last) (getTy P))) (suc (var (prev last))))
                ddS = congTmTy! fixSubstTy (dTm≃ (Ctx≃ft+Ty (reflect P=)) dS dSₛ (reflect dS₁))

abstract 
  natelimStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {P P' : DCtx (suc (suc n))} (rP : P ≃ P') (P= : ftS (proj P) ≡ NatStrS (proj Γ)) (P'= : ftS (proj P') ≡ NatStrS (proj Γ'))
                   {dO dO' : DMor n (suc n)} (rdO : dO ≃ dO') (dOₛ : S.is-section (proj dO)) (dO'ₛ : S.is-section (proj dO'))
                   (dO₁ : ∂₁S (proj dO) ≡ S.star (zeroStrS (proj Γ)) (proj P) P= (zeroStr₁S (proj Γ))) (dO'₁ : ∂₁S (proj dO') ≡ S.star (zeroStrS (proj Γ')) (proj P') P'= (zeroStr₁S (proj Γ')))
                   {dS dS' : DMor (suc (suc n)) (suc (suc (suc n)))} (rdS : dS ≃ dS') (dSₛ : S.is-section (proj dS))(dS'ₛ : S.is-section (proj dS'))
                   (dS₁ : ∂₁S (proj dS) ≡ sucS.T-dS₁ (proj Γ) (proj P) P=)
                   (dS'₁ : ∂₁S (proj dS') ≡ sucS.T-dS₁ (proj Γ') (proj P') P'=)
                   {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u'))
                   (u₁ : ∂₁S (proj u) ≡ NatStrS (proj Γ)) (u'₁ : ∂₁S (proj u') ≡ NatStrS (proj Γ'))
                 → natelimStrS-// Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁ ≃ natelimStrS-// Γ' P' P'= dO' dO'ₛ dO'₁ dS' dS'ₛ dS'₁ u' u'ₛ u'₁
  natelimStrS-eq {Γ = Γ} {Γ'} rΓ {P} {P'} rP P= P'= {dO} {dO'} rdO dOₛ dO'ₛ dO₁ dO'₁ {dS} {dS'} rdS dSₛ dS'ₛ dS₁ dS'₁ {u} {u'} ru uₛ u'ₛ u₁ u'₁ =
               dmorTm= dmorTmₛ dmorTmₛ rΓ (SubstTyFullEq' (der Γ) (der Γ , Nat) (dTy= rP P=) (idMor+= (der Γ) (dTm= refl ru uₛ u'ₛ u₁ u'₁)))
                                          (NatelimCong (dTy P P=) (dTy= rP P=)
                                                       (dTm= refl rdO dOₛ dO'ₛ dO₁ dO'₁)
                                                       ddS=
                                                       (dTm= refl ru uₛ u'ₛ u₁ u'₁))
                          where ddS= : Derivable (((ctx Γ , nat) , getTy P) ⊢ getTm dS == getTm dS' :> substTy (weakenTy' (prev last) (weakenTy' (prev last) (getTy P))) (suc (var (prev last))))
                                ddS= = congTmEqTy! fixSubstTy (dTm=≃ (Ctx≃ft+Ty (reflect P=)) rdS dSₛ dS'ₛ (reflect dS₁) (reflect dS'₁))

natelimStrS1 : (Γ : DCtx n) (P : DCtx (suc (suc n))) (P= : ftS (proj P) ≡ NatStrS (proj Γ))
               (dO : DMor n (suc n)) (dOₛ : S.is-section (proj dO)) (dO₁ : ∂₁S (proj dO) ≡ S.star (zeroStrS (proj Γ)) (proj P) P= (zeroStr₁S (proj Γ)))
               (dS : DMor (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section (proj dS)) (dS₁ : ∂₁S (proj dS) ≡ sucS.T-dS₁ (proj Γ) (proj P) P=)
               (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS (proj Γ))
             → MorS n (suc n)
natelimStrS1 Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ = //-elim-Tm (λ u uₛ u₁ → proj (natelimStrS-// Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁))
                                                       (λ ru uₛ u'ₛ u₁ u'₁ → proj= (natelimStrS-eq (ref Γ) (ref P) P= P= (ref dO) dOₛ dOₛ dO₁ dO₁ (ref dS) dSₛ dSₛ dS₁ dS₁ ru uₛ u'ₛ u₁ u'₁))

natelimStrS2 : (Γ : DCtx n) (P : DCtx (suc (suc n))) (P= : ftS (proj P) ≡ NatStrS (proj Γ))
               (dO : DMor n (suc n)) (dOₛ : S.is-section (proj dO)) (dO₁ : ∂₁S (proj dO) ≡ S.star (zeroStrS (proj Γ)) (proj P) P= (zeroStr₁S (proj Γ)))
               (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : ∂₁S dS ≡ sucS.T-dS₁ (proj Γ) (proj P) P=)
               (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS (proj Γ))
             → MorS n (suc n)
natelimStrS2 Γ P P= dO dOₛ dO₁ = //-elim-Tm (λ dS dSₛ dS₁ → natelimStrS1 Γ P P= dO dOₛ dO₁ dS dSₛ dS₁)
                                            (λ rdS dSₛ dS'ₛ dS₁ dS'₁ → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (natelimStrS-eq (ref Γ) (ref P) P= P= (ref dO) dOₛ dOₛ dO₁ dO₁ rdS dSₛ dS'ₛ dS₁ dS'₁ (ref u) uₛ uₛ u₁ u₁')))

natelimStrS3 : (Γ : DCtx n) (P : DCtx (suc (suc n))) (P= : ftS (proj P) ≡ NatStrS (proj Γ))
               (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : ∂₁S dO ≡ S.star (zeroStrS (proj Γ)) (proj P) P= (zeroStr₁S (proj Γ)))
               (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : ∂₁S dS ≡ sucS.T-dS₁ (proj Γ) (proj P) P=)
               (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS (proj Γ))
             → MorS n (suc n)
natelimStrS3 Γ P P= = //-elim-Tm (λ dO dOₛ dO₁ → natelimStrS2 Γ P P= dO dOₛ dO₁)
                                 (λ rdO dOₛ dO'ₛ dO₁ dO'₁ → //-elimP-Tm (λ dS dSₛ dS₁ dS₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (natelimStrS-eq (ref Γ) (ref P) P= P= rdO dOₛ dO'ₛ dO₁ dO'₁ (ref dS) dSₛ dSₛ dS₁ dS₁' (ref u) uₛ uₛ u₁ u₁'))))

natelimStrS4 : (Γ : DCtx n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS (proj Γ))
               (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : ∂₁S dO ≡ S.star (zeroStrS (proj Γ)) P P= (zeroStr₁S (proj Γ)))
               (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : ∂₁S dS ≡ sucS.T-dS₁ (proj Γ) P P=)
               (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS (proj Γ))
             → MorS n (suc n)
natelimStrS4 Γ = //-elim-Ty (λ P P= → natelimStrS3 Γ P P=)
                            (λ rP P= P'= → //-elimP-Tm (λ dO dOₛ dO₁ dO₁' → //-elimP-Tm (λ dS dSₛ dS₁ dS₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (natelimStrS-eq (ref Γ) rP P= P'= (ref dO) dOₛ dOₛ dO₁ dO₁' (ref dS) dSₛ dSₛ dS₁ dS₁' (ref u) uₛ uₛ u₁ u₁')))))

natelimStrS : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
              (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : ∂₁S dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
              (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : ∂₁S dS ≡ sucS.T-dS₁ Γ P P=)
              (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ)
            → MorS n (suc n)
natelimStrS = //-elim-Ctx (λ Γ → natelimStrS4 Γ)
                          (λ rΓ → //-elimP-Ty (λ P P= P=' → //-elimP-Tm (λ dO dOₛ dO₁ dO₁' → //-elimP-Tm (λ dS dSₛ dS₁ dS₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (natelimStrS-eq rΓ (ref P) P= P=' (ref dO) dOₛ dOₛ dO₁ dO₁' (ref dS) dSₛ dSₛ dS₁ dS₁' (ref u) uₛ uₛ u₁ u₁'))))))

abstract 
  natelimStrₛS : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
                 (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : ∂₁S dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
                 (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : ∂₁S dS ≡ sucS.T-dS₁ Γ P P=)
                 (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ) → S.is-section (natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁)
  natelimStrₛS = //-elimP (λ Γ → //-elimP (λ P P= → //-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → //-elimP (λ u uₛ u₁ → dmorTmₛ)))))

  natelimStr₁S : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
                 (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : ∂₁S dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
                 (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : ∂₁S dS ≡ sucS.T-dS₁ Γ P P=)
                 (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ) → S.∂₁ (natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁) ≡ S.star u P P= u₁
  natelimStr₁S = //-elimP (λ Γ → //-elimP (λ P P= → //-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → //-elimP (λ u uₛ u₁ → eq (box (reflectOb (! (S.is-section₀ uₛ u₁)) , SubstTyMorEq' (der Γ) (der Γ , Nat) (dTy P P=) (MorSymm (der Γ) (der Γ , Nat) (morTm=idMorTm (NatStr=S (proj Γ)) u uₛ u₁))))))))) 

natelimStrSynCCat : CCatwithnatelim synCCat NatStrSynCCat zeroStrSynCCat sucStrSynCCat
CCatwithnatelim.natelimStr natelimStrSynCCat = natelimStrS
CCatwithnatelim.natelimStrₛ natelimStrSynCCat {Γ = Γ} {P = P} {dO = dO} {dS = dS} {u = u} = natelimStrₛS Γ P _ dO _ _ dS _ _ u _ _
CCatwithnatelim.natelimStr₁ natelimStrSynCCat {Γ = Γ} {P = P} {dO = dO} {dS = dS} {u = u} = natelimStr₁S Γ P _ dO _ _ dS _ _ u _ _
CCatwithnatelim.natelimStrNat' natelimStrSynCCat = //-elimP (λ g → //-elimP (λ Δ g₀ → //-elimP (λ Γ → //-elimP (λ P P= → //-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → //-elimP (λ u uₛ u₁ g₁ → up-to-rhsTyEq' (reflectOb g₀) (ap-[]Ty refl (idMor[]Mor (mor g)) ∙ []Ty-substTy))))))))


module natelimS = CCatwithnatelim natelimStrSynCCat

{- ElNat= -}

elnatStrS : (i : ℕ) (Γ : ObS n) → ElStrS i Γ (natStrS i Γ) (natStrₛS i Γ) (natStr₁S i Γ) ≡ NatStrS Γ
elnatStrS i = //-elimP (λ Γ → eq (box (CtxRefl (der Γ) , ElNat=)))


{- BetaNatZero -}

betaNatZeroStrS : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
               (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : S.∂₁ dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
               (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : S.∂₁ dS ≡ sucS.T-dS₁ Γ P P=) →
               natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ (zeroStrS Γ) (zeroStrₛS Γ) (zeroStr₁S Γ) ≡ dO
betaNatZeroStrS = //-elimP (λ Γ → //-elimP (λ P P= → (//-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → eq (box
                           (CtxSymm (reflectOb (S.is-section₀ dOₛ dO₁)))
                           (CtxSymm (reflectOb dO₁))
                           (MorTran (der Γ) (der Γ , SubstTy (dTy P P=) (idMor+ (der Γ) Zero))
                                    (idMor+= (der Γ)
                                             (let ddS : Derivable (((ctx Γ , nat) , getTy P) ⊢ getTm dS :> substTy (weakenTy' (prev last) (weakenTy' (prev last) (getTy P))) (suc (var (prev last))))
                                                  ddS = congTmTy! fixSubstTy (dTm≃ (Ctx≃ft+Ty (reflect P=)) dS dSₛ (reflect dS₁))
                                              in BetaNatZero (dTy P P=) (dTm refl dO dOₛ dO₁) ddS)) (MorSymm (der Γ) (der Γ , SubstTy (dTy P P=) (idMor+ (der Γ) Zero)) (morTm=idMorTm refl dO dOₛ dO₁)))))))))


{- BetaNatSuc -}

betaNatSucStrS : (Γ : ObS n) (P : ObS (suc (suc n))) (P= : ftS P ≡ NatStrS Γ)
                 (dO : MorS n (suc n)) (dOₛ : S.is-section dO) (dO₁ : S.∂₁ dO ≡ S.star (zeroStrS Γ) P P= (zeroStr₁S Γ))
                 (dS : MorS (suc (suc n)) (suc (suc (suc n)))) (dSₛ : S.is-section dS) (dS₁ : S.∂₁ dS ≡ sucS.T-dS₁ Γ P P=)
                 (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ NatStrS Γ) →
                 natelimStrS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ (sucStrS Γ u uₛ u₁) (sucStrₛS Γ u) (sucStr₁S Γ u) ≡ natelimS.Tm-substdS Γ P P= dO dOₛ dO₁ dS dSₛ dS₁ u uₛ u₁ 
betaNatSucStrS = //-elimP (λ Γ → //-elimP (λ P P= → (//-elimP (λ dO dOₛ dO₁ → //-elimP (λ dS dSₛ dS₁ → //-elimP (λ u uₛ u₁ →
                 let ddS : Derivable (((ctx Γ , nat) , getTy P) ⊢ getTm dS :> substTy (weakenTy' (prev last) (weakenTy' (prev last) (getTy P))) (suc (var (prev last))))
                     ddS = congTmTy! fixSubstTy (dTm≃ (Ctx≃ft+Ty (reflect P=)) dS dSₛ (reflect dS₁))
                 in up-to-rhsTyEq2 (congTyEq (ap-[]Ty ([idMor]Ty _ ∙ ! fixSubstTy) refl
                                             ∙ []Ty-assoc _ _ _
                                             ∙ ap-[]Ty refl (Mor+= (Mor+= (Mor+= (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ [idMor]Mor _) refl) refl) refl)
                                             ∙ weakenTyInsert' _ _ _ _ ∙ weakenTyInsert' _ _ _ _)
                                             (! (ap-[]Ty (! ([]Ty-assoc _ _ _)) (Mor+= (weakenMorInsert _ _ _ ∙ idMor[]Mor _) refl)
                                                ∙ []Ty-assoc _ _ _
                                                ∙ ap-[]Ty refl (Mor+= (weakenMorInsert (mor u) _ _  ∙ [idMor]Mor _) refl)))
                                             (SubstTyFullEq' (der Γ) ((der Γ , Nat) , dTy P P=)
                                                             (SubstTyFullEq' ((der Γ , Nat) , dTy P P=) ((der Γ , Nat) , dTy P P=)
                                                                             (dTy=≃ (reflect (! dS₁)) (Ctx≃ft+Ty (reflect P=)))
                                                                             (MorSymm ((der Γ , Nat) , dTy P P=)
                                                                                      ((der Γ , Nat) , dTy P P=)
                                                                                      (getMor=idMor≃ (Ctx≃ft+Ty (reflect P=)) dS dSₛ (reflect dS₁))))
                                                             (MorSymm (der Γ) (der Γ , Nat)
                                                                      (morTm=idMorTm refl u uₛ u₁)
                                                             , TmRefl (Natelim (dTy P P=) (dTm refl dO dOₛ dO₁) ddS (dTm refl u uₛ u₁)))))
                                   (TmTran' (der Γ) (BetaNatSuc (dTy P P=) (dTm refl dO dOₛ dO₁) ddS (dTm refl u uₛ u₁))
                                            (congTmEq refl (! ([]Tm-assoc _ _ (getTm dS) ∙ ap-[]Tm {u = getTm dS} refl (Mor+= (weakenMorInsert (mor u) _ _ ∙ [idMor]Mor _) refl)))
                                                           ([]Ty-substTy ∙ ap-[]Ty (weakenTyInsert' _ _ _ _ ∙ weakenTyInsert' _ _ _ _ ∙ [idMor]Ty _) refl)
                                                           (SubstTmMorEq' (der Γ) ((der Γ , Nat) , dTy P P=) ddS (MorSymm (der Γ) (der Γ , Nat)
                                                                          (morTm=idMorTm refl u uₛ u₁)
                                                                          , TmRefl (Natelim (dTy P P=) (dTm refl dO dOₛ dO₁) ddS (dTm refl u uₛ u₁))))))))))))

