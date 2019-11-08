{-# OPTIONS --rewriting --prop --without-K --no-auto-inline --no-fast-reduce #-}

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
open import termmodel-id


open CCat hiding (Mor) renaming (id to idC)

abstract
  jjStr₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ idS.T-ftP Γ A A=) (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ reflS.T-d₁ Γ A A= P P=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ A) (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS Γ A A= a aₛ a₁ b bₛ b₁) → ∂₁S (jjStrS Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁) ≡ idS.T-jjStr₁ Γ A A= P P= a aₛ a₁ b bₛ b₁ p pₛ p₁
  jjStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → //-elimP (λ p pₛ p₁ →
                     eq {a = ((ctx Γ , (getTy' (ctx P) [ ((idMor _ , getRHS (mor a)) , getRHS (mor b)) , getRHS (mor p) ]Ty)) , ‗)}
                        {b = ((ctx (lhs p) ,  (((getTy' (ctx P) [ (weakenMor' last (weakenMor' last (mor a)) , var (prev last)) , var last ]Ty) [ weakenMor' last (mor b) , var last ]Ty) [ mor p ]Ty)) , ‗)}
                        (box (reflectOb (! (S.is-section₀ pₛ p₁)) ,,
                              congTyEq (! subst3Ty=3substTy) refl
                                       (SubstTyMorEq2 (der Γ)
                                                      (der Γ , Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= b bₛ b₁))
                                                      (SubstTyMorEq2 (der Γ , Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= b bₛ b₁))
                                                                     ((der Γ , dTy A A=) , Id (WeakTy (dTy A A=)) (WeakTm (dTm A= a aₛ a₁)) (VarLast (dTy A A=)))
                                                                     (SubstTyMorEq' {Δ = ((ctx Γ , getTy A) , weakenTy (getTy A)) , id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)}
                                                                                    ((der Γ , dTy A A=) , Id (WeakTy (dTy A A=)) (WeakTm (dTm A= a aₛ a₁)) (VarLast (dTy A A=)))
                                                                                    (((der Γ , dTy A A=) , WeakTy (dTy A A=)) ,
                                                                                     Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=))))
                                                                                    (ConvTy (dTy P P=)
                                                                                            (CtxSymm (ConvTyDCtxEq (ConvTyDCtxEq (CtxTy=Ctx A A=)
                                                                                                                                 (WeakTy (dTy A A=))
                                                                                                                                 weakenTy-to-[]Ty)
                                                                                                                   (Id (WeakTy (WeakTy (dTy A A=)))
                                                                                                                       (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=)))
                                                                                                                       (VarLast (WeakTy (dTy A A=))))
                                                                                                                       (ap-id-Ty (weakenTy-to-[]Ty ∙ ap-[]Ty weakenTy-to-[]Ty refl) refl refl))))
                                                                                    (congMorEqCtxEq {Δ = ((ctx Γ , getTy A) , weakenTy (getTy A)) ,
                                                                                                          id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)}
                                                                                                    (Ctx+= refl (ap-id-Ty (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _ ∙ ! weakenTy-to-[]Ty) refl refl))
                                                                                                    (WeakMor+Eq' (der Γ , dTy A A=)
                                                                                                                 ((der Γ , dTy A A=) , WeakTy (dTy A A=))
                                                                                                                 (Id (WeakTy (WeakTy (dTy A A=)))
                                                                                                                     (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=)))
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
CCatwithjj.jjStrNat' jjStrSynCCat = //-elimP (λ g → //-elimP (λ Δ g₀ → (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → //-elimP (λ p pₛ p₁ g₁ → up-to-rhsTyEq' {Γ = (ctx (lhs g) , ‗)}
                       {Δ = (ctx Δ , ‗)}
                       {A = ((getTy' (ctx P) [ ((idMor _ , getRHS (mor a)) , getRHS (mor b)) , getRHS (mor p) ]Ty) [ idMor _ [ mor g ]Mor ]Ty)}
                       {B = ((getTy' (ctx P) [ ((weakenMor' last (weakenMor' last (weakenMor' last (mor g))) , var (prev (prev last))) , var (prev last)) , var last ]Ty)
                             [ ((idMor _ , (getRHS (mor a) [ mor g ]Tm)) , (getRHS (mor b) [ mor g ]Tm)) , (getRHS (mor p) [ mor g ]Tm) ]Ty)}
                       {δ = idMor _ , jj (getTy' (ctx A) [ mor g ]Ty) (getTy' (ctx P) [ ((weakenMor' last (weakenMor' last (weakenMor' last (mor g))) , var (prev (prev last))) , var (prev last)) , var last ]Ty) (getRHS (mor d) [ weakenMor' last (mor g) , var last ]Tm) (getRHS (mor a) [ mor g ]Tm) (getRHS (mor b) [ mor g ]Tm) (getRHS (mor p) [ mor g ]Tm)}
                       {w₁ =  ‗} {w₂ = ‗} {w₃ = ‗} {w₄ =  ‗}
                       (reflectOb g₀)
                       (ap (_[_]Ty (subst3Ty (getTy P) (getTm a) (getTm b) (getTm p))) (idMor[]Mor (mor g)) ∙ []Ty-subst3Ty))))))))))) 
                       
{- ElId= -}

elidStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)
                   (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁) → ElStrS i Γ (idStrS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStrₛS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStr₁S i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ IdStrS Γ (ElStrS i Γ a aₛ a₁) (ElStr=S i Γ a aₛ a₁) u uₛ u₁ v vₛ v₁
elidStrS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → eq (box (CtxRefl (der Γ) ,, ElId= (dTm refl a aₛ a₁) (dTm refl u uₛ u₁) (dTm refl v vₛ v₁)))))))

{- BetaJ -}

betaIdStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ idS.T-ftP Γ A A=)
             (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ reflS.T-d₁ Γ A A= P P=)
             (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
           → jjStrS Γ A A= P P= d dₛ d₁ a aₛ a₁ a aₛ a₁ (reflStrS Γ A A= a aₛ a₁) (reflStrₛS Γ A A= a aₛ a₁) (reflStr₁S Γ A A= a aₛ a₁) ≡ S.starTm a d (S.is-section₀ dₛ d₁ ∙ reflS.T-d₁=) a₁
betaIdStrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ →
                      let dP = ConvTy (dTy P P=) (CtxSymm (ConvTyDCtxEq (ConvTyDCtxEq (CtxTy=Ctx A A=)
                                                                            (WeakTy (dTy A A=))
                                                                            weakenTy-to-[]Ty)
                                                 (Id (WeakTy (WeakTy (dTy A A=)))
                                                     (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=)))
                                                     (VarLast (WeakTy (dTy A A=))))
                                                 (ap-id-Ty (weakenTy-to-[]Ty ∙ ap-[]Ty weakenTy-to-[]Ty refl) refl refl)))
                          dd = congTmTy! fixTyJJ (dTm' {Γ = ((_ , _) ,' (der Γ , dTy A A=))}
                                                       {A = ((_ , _) ,' (der A , ConvTy (congTy fixTyJJ (Subst3Ty (der Γ , dTy A A=) (WeakTy dP) (VarLast (dTy A A=)) (congTmTy (weakenTy-to-[]Ty ∙ ! (weakenTyInsert' (prev last) _ (idMor _) (var last) ∙ weakenTyInsert _ _ _)) (VarLast (dTy A A=))) (congTmTy (ap-id-Ty (! (weakenTyInsert' (prev (prev last)) _ ((weakenMor (idMor _) , var last) , var last) (var last) ∙ weakenTyInsert _ _ _ ∙ [idMor]Ty _)) refl refl) (Refl (WeakTy (dTy A A=)) (VarLast (dTy A A=)))))) (CtxTy=Ctx A A=)))}
                                                       (eq (box (CtxSymm (CtxTy=Ctx A A=)))) d dₛ (reflectOb d₁))
                      in eq (box (CtxSymm (reflectOb (S.is-section₀ aₛ a₁ ∙ A=)))
                            (CtxSymm (reflectOb (S.is-section₀ aₛ a₁ ∙ A=)) ,,  congTyEq {A = (((((getTy P) [ weakenMor+ (weakenMor+ (weakenMor+ (weakenMor (idMor _)))) ]Ty) [ weakenMor+ (weakenMor+ (idMor (suc _) , var last)) ]Ty) [ weakenMor+ (idMor (suc _) , var last) ]Ty) [ idMor (suc _) , refl ((getTy A) [ weakenMor (idMor _) ]Ty) (var last) ]Ty) [ idMor _ , getTm a ]Ty}
                                                                                         (ap (λ z → z [ idMor _ , getTm a ]Ty) (! fixTyJJ ∙ ap (λ z → z [ (((weakenMor' last (idMor _) , var last) , var last) , var last) , refl (weakenTy' last (getTy A)) (var last) ]Ty) weakenTy+++-to-[]Ty ∙ []Ty-assoc _ _ _) ∙ []Ty-assoc _ _ _ ∙ ap (λ z → (getTy P) [ z ]Ty) (Mor+= (Mor+= (Mor+= ([]Mor-assoc _ _ _ ∙ weakenMorInsert _ _ (refl (weakenTy (getTy A) [ idMor _ , getTm a ]Ty) (getTm a)) ∙ weakenMorInsert _ _ (getTm a) ∙ weakenMorInsert _ _ (getTm a) ∙ weakenMorInsert _ _ (getTm a) ∙ idMor[]Mor _ ∙ weakenMorInsert _ _ (getTm a) ∙ idMor[]Mor _) refl) refl) (ap-refl-Tm (weakenSubstTy _ _) refl)))
                                                                                         refl
                                                                                         (SubstTyMorEq2 {Δ = ctx Γ , getTy A} (der Γ) (der Γ , dTy A A=) (dTy= {Γ = ((_ , _) ,' (der Γ , dTy A A=))} {A = ((_ , _ ) , _) ,' ((der Γ , dTy A A=) , congTy fixTyJJ (Subst3Ty (der Γ , dTy A A=) (WeakTy dP) (VarLast (dTy A A=)) (congTmTy (! (weakenTyInsert' (prev last) _ _ _ ∙ [idMor]Ty _)) (VarLast (dTy A A=))) (congTmTy (ap-id-Ty (! (weakenTyInsert' (prev (prev last)) _ (idMor _ , var last) (var last) ∙ substTy-weakenTy)) refl refl) (Refl (WeakTy (dTy A A=)) (VarLast (dTy A A=))))))} (tra (box (CtxTy=Ctx A A= ,, TyRefl (congTy fixTyJJ (Subst3Ty (der Γ , dTy A A=) (WeakTy dP) (VarLast (dTy A A=)) (congTmTy (! (weakenTyInsert' (prev last) _ _ _ ∙ [idMor]Ty _)) (VarLast (dTy A A=))) (congTmTy (ap-id-Ty (! (weakenTyInsert' (prev (prev last)) _ (idMor _ , var last) (var last) ∙ substTy-weakenTy)) refl refl) (Refl (WeakTy (dTy A A=)) (VarLast (dTy A A=)))))))) (reflect (! d₁))) refl) (MorTran (der Γ) (der Γ , dTy A A=) (MorSymm (der Γ) (der Γ , dTy A A=) (morTm=idMorTm A= a aₛ a₁)) (congMorEq refl refl (idMor[]Mor _) refl (SubstMorEq {Γ = ctx Γ} {θ = idMor _} {θ' = getMor d} (MorSymm (der Γ , dTy A A=) (der Γ , dTy A A=) (getMor=idMor {Γ = ((_ , _) , (der Γ , dTy A A=))} {A = ((_ , _) ,' (der A , ConvTy (congTy fixTyJJ (Subst3Ty (der Γ , dTy A A=) (WeakTy dP) (VarLast (dTy A A=)) (congTmTy (weakenTy-to-[]Ty ∙ ! (weakenTyInsert' (prev last) _ (idMor _) (var last) ∙ weakenTyInsert _ _ _)) (VarLast (dTy A A=))) (congTmTy (ap-id-Ty (! (weakenTyInsert' (prev (prev last)) _ ((weakenMor (idMor _) , var last) , var last) (var last) ∙ weakenTyInsert _ _ _ ∙ [idMor]Ty _)) refl refl) (Refl (WeakTy (dTy A A=)) (VarLast (dTy A A=)))))) (CtxTy=Ctx A A=)))} (eq (box (CtxSymm (CtxTy=Ctx A A=)))) d dₛ d₁)) (dMor A= a aₛ a₁))))))
                            (idMor+= (der Γ) (TmTran' (der Γ) (BetaIdRefl (dTy A A=) dP dd (dTm A= a aₛ a₁)) (congTmEqTy ([]Ty-subst3Ty ∙ ap-subst3Ty (weakenTyInsertLemma3 last _ _ (getTm a) ∙ weakenTyInsert' (prev (prev (prev last))) (getTy P) _ _ ∙ [idMor]Ty _) refl refl (ap (λ z → refl z (getRHS (mor a))) (weakenSubstTy _ _))) (SubstTmMorEq dd (idMor+ (der Γ) (dTm A= a aₛ a₁)) (MorSymm (der Γ) (der Γ , dTy A A=) (morTm=idMorTm A= a aₛ a₁))))))))))))


