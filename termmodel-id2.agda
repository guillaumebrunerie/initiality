{-# OPTIONS --rewriting --prop #-}

open import common
open import typetheory
open import syntx hiding (getTy)
open import rules
open import reflection hiding (proj)
open import contextualcat
open import quotients
open import termmodel-common
open import termmodel-synccat
open import termmodel-uuel
open import termmodel-id


open CCat hiding (Mor) renaming (id to idC)

abstract 
  jjStrₛS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ idS.T-ftP Γ A A=) (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ reflS.T-d₁ Γ A A= P P=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ A) (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS Γ A A= a aₛ a₁ b bₛ b₁) → S.is-section (jjStrS Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁)
  jjStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → //-elimP (λ p pₛ p₁ → dmorTmₛ)))))))

  jjStr₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ idS.T-ftP Γ A A=) (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ reflS.T-d₁ Γ A A= P P=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ A) (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS Γ A A= a aₛ a₁ b bₛ b₁) → ∂₁S (jjStrS Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁) ≡ idS.T-jjStr₁ Γ A A= P P= a aₛ a₁ b bₛ b₁ p pₛ p₁
  jjStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → //-elimP (λ p pₛ p₁ →
                     eq (box (reflectOb (! (S.is-section₀ pₛ p₁))
                             , congTyEq (! subst3Ty=3substTy) refl
                                         (SubstTyFullEq' (der Γ)
                                                         (der Γ , Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= b bₛ b₁))
                                                         (SubstTyFullEq' (der Γ , Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= b bₛ b₁))
                                                                         ((der Γ , dTy A A=) , Id (WeakTy (dTy A A=)) (WeakTm (dTm A= a aₛ a₁)) (VarLast (dTy A A=)))
                                                                         (SubstTyMorEq' {Δ = ((ctx Γ , getTy A) , weakenTy (getTy A)) , id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)}
                                                                                        ((der Γ , dTy A A=) , Id (WeakTy (dTy A A=)) (WeakTm (dTm A= a aₛ a₁)) (VarLast (dTy A A=)))
                                                                                        (((der Γ , dTy A A=) , WeakTy (dTy A A=)) ,
                                                                                        Id (WeakTy (WeakTy (dTy A A=))) (VarPrevLast (dTy A A=)) (VarLast (WeakTy (dTy A A=))))
                                                                                        (ConvTy (dTy P P=)
                                                                                                (CtxSymm (ConvTyDCtxEq (ConvTyDCtxEq (CtxTy=Ctx A A=)
                                                                                                                                     (WeakTy (dTy A A=))
                                                                                                                                     weakenTy-to-[]Ty)
                                                                                                                       (Id (WeakTy (WeakTy (dTy A A=)))
                                                                                                                           (VarPrevLast (dTy A A=))
                                                                                                                           (VarLast (WeakTy (dTy A A=))))
                                                                                                                           (ap-id-Ty (weakenTy-to-[]Ty ∙ ap-[]Ty weakenTy-to-[]Ty refl) refl refl))))
                                                                                        (congMorEqCtxEq {Δ = ((ctx Γ , getTy A) , weakenTy (getTy A)) ,
                                                                                                             id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)}
                                                                                                        (Ctx+= refl (ap-id-Ty (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _ ∙ ! weakenTy-to-[]Ty) refl refl))
                                                                                                        (WeakMor+Eq' (der Γ , dTy A A=)
                                                                                                                     ((der Γ , dTy A A=) , WeakTy (dTy A A=))
                                                                                                                     (Id (WeakTy (WeakTy (dTy A A=)))
                                                                                                                         (VarPrevLast (dTy A A=))
                                                                                                                         (VarLast (WeakTy (dTy A A=))))
                                                                                                                     (congMorEqCtxEq (Ctx+= refl (weakenSubstTy (getTy A) _))
                                                                                                                                     (WeakMor+Eq' (der Γ)
                                                                                                                                                  (der Γ , dTy A A=)
                                                                                                                                                  (WeakTy (dTy A A=))
                                                                                                                                                  (MorSymm (der Γ)
                                                                                                                                                           (der Γ , dTy A A=)
                                                                                                                                                           (morTm=idMorTm A= a aₛ a₁)))))))
                                                                         (congMorEqCtxEq {Δ = (ctx Γ , getTy A) , id (weakenTy (getTy A)) (weakenTm (getTm a)) (var last)}
                                                                                         (Ctx+= refl (ap-id-Ty (weakenSubstTy (getTy A) (getTm b))
                                                                                                               (weakenSubstTm (getTm a) (getTm b))
                                                                                                               refl))
                                                                                         (WeakMor+Eq' (der Γ)
                                                                                                      (der Γ , dTy A A=)
                                                                                                      (Id (WeakTy (dTy A A=))
                                                                                                          (WeakTm (dTm A= a aₛ a₁))
                                                                                                          (VarLast (dTy A A=)))
                                                                                                      (MorSymm (der Γ)
                                                                                                               (der Γ , dTy A A=)
                                                                                                               (morTm=idMorTm A= b bₛ b₁)))))
                                                         (MorSymm (der Γ)
                                                                  (der Γ , Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= b bₛ b₁))
                                                                  (morTm=idMorTm refl p pₛ p₁))))))))))))
  
jjStrSynCCat : CCatwithjj synCCat IdStrSynCCat reflStrSynCCat
CCatwithjj.jjStr jjStrSynCCat = jjStrS
CCatwithjj.jjStrₛ jjStrSynCCat {Γ = Γ} {A = A} {P = P} {d = d} {a = a} {b = b} {p = p} = jjStrₛS Γ A _ P _ d _ _ a _ _ b _ _ p _ _
CCatwithjj.jjStr₁ jjStrSynCCat {Γ = Γ} {A = A} {P = P} {d = d} {a = a} {b = b} {p = p} = jjStr₁S Γ A _ P _ d _ _ a _ _ b _ _ p _ _
CCatwithjj.jjStrNat' jjStrSynCCat = //-elimP (λ g → //-elimP (λ Δ g₀ → (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → //-elimP (λ p pₛ p₁ g₁ → up-to-rhsTyEq' (reflectOb g₀) (ap-[]Ty refl (idMor[]Mor (mor g)) ∙ []Ty-subst3Ty))))))))))) 
                       
{- ElId= -}

elidStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)
                   (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁) → ElStrS i Γ (idStrS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStrₛS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStr₁S i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ IdStrS Γ (ElStrS i Γ a aₛ a₁) (ElStr=S i Γ a aₛ a₁) u uₛ u₁ v vₛ v₁
elidStrS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → eq (box (CtxRefl (der Γ) , ElId= (dTm refl a aₛ a₁) (dTm refl u uₛ u₁) (dTm refl v vₛ v₁)))))))

{- BetaJ -}

betaIdStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ idS.T-ftP Γ A A=)
             (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ reflS.T-d₁ Γ A A= P P=)
             (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
           → jjStrS Γ A A= P P= d dₛ d₁ a aₛ a₁ a aₛ a₁ (reflStrS Γ A A= a aₛ a₁) (reflStrₛS Γ A A= a aₛ a₁) (reflStr₁S Γ A A= a aₛ a₁) ≡ S.starTm a d (S.is-section₀ dₛ d₁ ∙ reflS.T-d₁=) a₁
betaIdStrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ →
                      let dd = congTmTy! fixTyJJ (dTm≃ (Ctx≃ft+Ty (reflect A=)) d dₛ (reflectd₁ Γ A A= P P= d d₁))
                      in up-to-rhsTyEq2' (CtxSymm (reflectOb (S.is-section₀ aₛ a₁ ∙ A=)))
                                         (congTyEq (ap-[]Ty ([idMor]Ty _ ∙ ! fixTyJJ) refl
                                                   ∙ []Ty-assoc _ _ _
                                                   ∙ ap-[]Ty refl (Mor+= (Mor+= (Mor+= (Mor+= (weakenMorInsert _ _ _ ∙ ([idMor]Mor _)) refl) refl) refl)
                                                                         (ap-refl-Tm (weakenTyInsert _ _ _ ∙ [idMor]Ty _) refl))
                                                   ∙ weakenTyInsert' _ _ _ _ )
                                                   ([]Ty-assoc _ _ _ )
                                                   (SubstTyFullEq' (der Γ) (der Γ , dTy A A=)
                                                                   (SubstTyFullEq' (der Γ , dTy A A=) (der Γ , dTy A A=)
                                                                                   (dTy=≃ (sym (reflectd₁ Γ A A= P P= d d₁)) (Ctx≃ft+Ty (reflect A=)))
                                                                                   (MorSymm (der Γ , dTy A A=) (der Γ , dTy A A=)
                                                                                            (getMor=idMor≃ (Ctx≃ft+Ty (reflect A=)) d dₛ (reflectd₁ Γ A A= P P= d d₁))))
                                                                   (MorSymm (der Γ) (der Γ , dTy A A=)
                                                                               (morTm=idMorTm A= a aₛ a₁))))
                                         (TmTran' (der Γ) (BetaIdRefl (dTy A A=) (dP Γ A A= P P=) dd (dTm A= a aₛ a₁))
                                                          (congTmEqTy ([]Ty-subst3Ty
                                                                      ∙ ap-subst3Ty (weakenTyInsertLemma3 last _ _ _ ∙ weakenTyInsert' _ _ _ _ ∙ [idMor]Ty _)
                                                                                    refl refl
                                                                                    (ap-refl-Tm (weakenSubstTy _ _) refl))
                                                                      (SubstTmMorEq' (der Γ) (der Γ , dTy A A=) dd (MorSymm (der Γ) (der Γ , dTy A A=) (morTm=idMorTm A= a aₛ a₁))))))))))



