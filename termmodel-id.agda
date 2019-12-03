{-# OPTIONS --rewriting --prop #-}

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


{- Id -}

IdStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ proj A) (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : ∂₁S (proj b) ≡ proj A) → DCtx (suc n)
IdStrS-// Γ A A= a aₛ a₁ b bₛ b₁ = dctx (der Γ , Id (dTy A A=) (dTm A= a aₛ a₁) (dTm A= b bₛ b₁))


IdStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : _) (A'= : _) {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : _) (a'ₛ : _) (a₁ : _) (a'₁ : _) {b b' : DMor n (suc n)} (rb : b ≃ b') (bₛ : _) (b'ₛ : _) (b₁ : _) (b'₁ : _) → IdStrS-// Γ A A= a aₛ a₁ b bₛ b₁ ≃ IdStrS-// Γ' A' A'= a' a'ₛ a'₁ b' b'ₛ b'₁
IdStrS-eq rΓ rA A= A'= ra aₛ a'ₛ a₁ a'₁ rb bₛ b'ₛ b₁ b'₁ = box (unOb≃ rΓ ,, IdCong (dTy= rA A=) (dTm= A= ra aₛ a'ₛ a₁ a'₁) (dTm= A= rb bₛ b'ₛ b₁ b'₁))

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

module idS = CCatwithId IdStrSynCCat

{- id -}

idStrS-// : (i : ℕ) (Γ : DCtx n) (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (proj Γ)) (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj Γ) (proj a) aₛ a₁)  (v : DMor n (suc n)) (vₛ : S.is-section (proj v)) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj Γ) (proj a) aₛ a₁) → DMor n (suc n)
idStrS-// i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁ = dmorTm Γ (uu i) UU (id i (getTm a) (getTm u) (getTm v))
                                                           (IdUU (dTm refl a aₛ a₁) (dTm refl u uₛ u₁) (dTm refl v vₛ v₁)) 

idStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ UUStrS i (proj Γ)) (a'₁ : ∂₁S (proj a') ≡ UUStrS i (proj Γ')) {u u' : DMor n (suc n)} (ru : u ≃ u') (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u')) (u₁ : ∂₁S (proj u) ≡ ElStrS i (proj Γ) (proj a) aₛ a₁)  (u'₁ : ∂₁S (proj u') ≡ ElStrS i (proj Γ') (proj a') a'ₛ a'₁) {v v' : DMor n (suc n)} (rv : v ≃ v') (vₛ : S.is-section (proj v)) (v'ₛ : S.is-section (proj v')) (v₁ : ∂₁S (proj v) ≡ ElStrS i (proj Γ) (proj a) aₛ a₁) (v'₁ : ∂₁S (proj v') ≡ ElStrS i (proj Γ') (proj a') a'ₛ a'₁) → idStrS-// i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁ ≃ idStrS-// i Γ' a' a'ₛ a'₁ u' u'ₛ u'₁ v' v'ₛ v'₁
idStrS-eq i {Γ} {Γ'} rΓ {a} {a'} ra aₛ a'ₛ a₁ a'₁ {u} {u'} ru uₛ u'ₛ u₁ u'₁ {v} {v'} rv vₛ v'ₛ v₁ v'₁ =
          dmorTm= dmorTmₛ dmorTmₛ rΓ UUCong (IdUUCong (dTm= refl ra aₛ a'ₛ a₁ a'₁)
                                                      (dTm= refl ru uₛ u'ₛ u₁ u'₁)
                                                      (dTm= refl rv vₛ v'ₛ v₁ v'₁))

idStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)  (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁) → MorS n (suc n)
idStrS i = //-elim-Ctx (λ Γ → //-elim-Tm (λ a aₛ a₁ → //-elim-Tm (λ u uₛ u₁ → //-elim-Tm (λ v vₛ v₁ → proj (idStrS-// i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁))
                                                                                         (λ rv vₛ v'ₛ v₁ v'₁ → proj= (idStrS-eq i (ref Γ) (ref a) aₛ aₛ a₁ a₁ (ref u) uₛ uₛ u₁ u₁ rv vₛ v'ₛ v₁ v'₁)))
                                                                 (λ ru uₛ u'ₛ u₁ u'₁ → //-elimP-Tm (λ v vₛ v₁ v₁' → proj= (idStrS-eq i (ref Γ) (ref a) aₛ aₛ a₁ a₁ ru uₛ u'ₛ u₁ u'₁ (ref v) vₛ vₛ v₁ v₁'))))
                                         (λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ u uₛ u₁ u₁' → //-elimP-Tm (λ v vₛ v₁ v₁' → proj= (idStrS-eq i (ref Γ) ra aₛ a'ₛ a₁ a'₁ (ref u) uₛ uₛ u₁ u₁' (ref v) vₛ vₛ v₁ v₁')))))
                       (λ rΓ → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → //-elimP-Tm (λ v vₛ v₁ v₁' → proj= (idStrS-eq i rΓ (ref a) aₛ aₛ a₁ a₁' (ref u) uₛ uₛ u₁ u₁' (ref v) vₛ vₛ v₁ v₁')))))

idStrₛS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)  (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁) → S.is-section (idStrS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁)
idStrₛS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → dmorTmₛ))))

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

reflStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : S.ft (proj A) ≡ proj Γ) (A'= : S.ft (proj A') ≡ proj Γ') {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : ∂₁S (proj a) ≡ (proj A)) (a'₁ : ∂₁S (proj a') ≡ (proj A')) → reflStrS-// Γ A A= a aₛ a₁ ≃ reflStrS-// Γ' A' A'= a' a'ₛ a'₁
reflStrS-eq rΓ {A} {A'} rA A= A'= {a} {a'} ra aₛ a'ₛ a₁ a'₁ = dmorTm= dmorTmₛ dmorTmₛ rΓ (IdCong (dTy= rA A=) (dTm= A= ra aₛ a'ₛ a₁ a'₁) (dTm= A= ra aₛ a'ₛ a₁ a'₁))
                                                                                         (ReflCong (dTy= rA A=) (dTm= A= ra aₛ a'ₛ a₁ a'₁))

reflStrS  : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) → MorS n (suc n)
reflStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Tm (λ a aₛ a₁ → proj (reflStrS-// Γ A A= a aₛ a₁))
                                                              (λ ra aₛ a'ₛ a₁ a'₁ → proj= (reflStrS-eq (ref Γ) (ref A) A= A= ra aₛ a'ₛ a₁ a'₁)))
                                         (λ rA A= A'= → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (reflStrS-eq (ref Γ) rA A= A'= (ref a) aₛ aₛ a₁ a₁'))))
                       (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (reflStrS-eq rΓ (ref A) A= A=' (ref a) aₛ aₛ a₁ a₁'))))
                       
reflStrₛS :  (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) → S.is-section (reflStrS Γ A A= a aₛ a₁)
reflStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → (//-elimP (λ a aₛ a₁ → dmorTmₛ))))

reflStr₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : S.ft A ≡ Γ) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A) → ∂₁S (reflStrS Γ A A= a aₛ a₁) ≡ IdStrS Γ A A= a aₛ a₁ a aₛ a₁
reflStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → (//-elimP (λ a aₛ a₁ → refl))))

reflStrSynCCat : CCatwithrefl IdStrSynCCat
CCatwithrefl.reflStr reflStrSynCCat = reflStrS
CCatwithrefl.reflStrₛ reflStrSynCCat {Γ = Γ} {A = A} {a = a} = reflStrₛS Γ A _ a _ _
CCatwithrefl.reflStr₁ reflStrSynCCat {Γ = Γ} {A = A} {a = a} = reflStr₁S Γ A _ a _ _
CCatwithrefl.reflStrNat' reflStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ a aₛ a₁ g₁ → up-to-rhsTyEq (ap (_[_]Ty (id (getTy A) (getTm a) (getTm a))) (idMor[]Mor (mor g))))))))

module reflS = CCatwithrefl reflStrSynCCat


{- JJ -}

fixTyJJ : {A : TyExpr n} {P : TyExpr (suc (suc (suc n)))} → subst3Ty (weakenTy' (prev (prev (prev last))) P) (var last) (var last) (refl (weakenTy A) (var last)) ≡ (((P [ weakenMor+ (weakenMor+ (weakenMor+ (weakenMor (idMor n)))) ]Ty) [ weakenMor+ (weakenMor+ (idMor (suc n) , var last)) ]Ty) [ weakenMor+ (idMor (suc n) , var last) ]Ty) [ idMor (suc n) , refl (A [ weakenMor (idMor n) ]Ty) (var last) ]Ty
fixTyJJ = ap-[]Ty weakenTy+++-to-[]Ty (Mor+= (Mor+= (Mor+= (Mor+= (! (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _ ∙ weakenMorInsert _ _ _ ∙ [idMor]Mor _)) refl) refl) refl) (ap-refl-Tm weakenTy-to-[]Ty refl)) ∙ ! ([]Ty-assoc _ _ _ ∙ []Ty-assoc _ _ _ )



abstract
  dP : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (P : DCtx (suc (suc (suc (suc n))))) (P= : ftS (proj P) ≡ idS.T-ftP (proj Γ) (proj A) A=)
     → Derivable ((((ctx Γ , getTy A) , weakenTy (getTy A)) , id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)) ⊢ getTy P)
  dP Γ A A= P P= = ConvTy (dTy P P=) (CtxSymm (ConvTyDCtxEq (ConvTyDCtxEq (CtxTy=Ctx A A=)
                                                                            (WeakTy (dTy A A=))
                                                                            weakenTy-to-[]Ty)
                                                (Id (WeakTy (WeakTy (dTy A A=)))
                                                    (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=)))
                                                    (VarLast (WeakTy (dTy A A=))))
                                                (ap-id-Ty (weakenTy-to-[]Ty ∙ ap-[]Ty weakenTy-to-[]Ty refl) refl refl)))
                                                
T-d₁S : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (P : DCtx (suc (suc (suc (suc n))))) (P= : ftS (proj P) ≡ idS.T-ftP (proj Γ) (proj A) A=) → DCtx (suc (suc n))
T-d₁S Γ A A= P P= = dctx {ctx = _ , _} (der A , ConvTy (congTy fixTyJJ (Subst3Ty (der Γ , dTy A A=) (WeakTy (dP Γ A A= P P=)) (VarLast (dTy A A=)) (congTmTy (weakenTy-to-[]Ty ∙ ! (weakenTyInsert' (prev last) _ (idMor _) (var last) ∙ weakenTyInsert _ _ _)) (VarLast (dTy A A=))) (congTmTy (ap-id-Ty (! (weakenTyInsert' (prev (prev last)) _ ((weakenMor (idMor _) , var last) , var last) (var last) ∙ weakenTyInsert _ _ _ ∙ [idMor]Ty _)) refl refl) (Refl (WeakTy (dTy A A=)) (VarLast (dTy A A=)))))) (CtxTy=Ctx A A=))

abstract
  reflectd₁ : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (P : DCtx (suc (suc (suc (suc n))))) (P= : ftS (proj P) ≡ idS.T-ftP (proj Γ) (proj A) A=)
              (d : DMor (suc n) (suc (suc n))) (d₁ : ∂₁S (proj d) ≡ reflS.T-d₁ (proj Γ) (proj A) A= (proj P) P=)
            → dctx (der (∂₁S-// d)) ≃ T-d₁S Γ A A= P P=
  reflectd₁ Γ A A= P P= d d₁ = reflect d₁



jjStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ) (P : DCtx (suc (suc (suc (suc n))))) (P= : S.ft (proj P) ≡ idS.T-ftP (proj Γ) (proj A) A=)
            (d : DMor (suc n) (suc (suc n))) (dₛ : S.is-section (proj d))
            (d₁ : dctx (der (∂₁S-// d)) ≃ T-d₁S Γ A A= P P=) {-⊢ ctx (∂₁S-// d) == (ctx A , ((((getTy' (ctx P) [ weakenMor+ (weakenMor+ (weakenMor+ (weakenMor (idMor n)))) ]Ty) [ weakenMor+ (weakenMor+ (idMor (suc n) , var last)) ]Ty) [ weakenMor+ (idMor (suc n) , var last) ]Ty) [ idMor (suc n) , refl (getTy A [ weakenMor (idMor n) ]Ty) (var last) ]Ty)))-}
            (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : S.∂₁ (proj a) ≡ (proj A))
            (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : S.∂₁ (proj b) ≡ (proj A))
            (p : DMor n (suc n)) (pₛ : S.is-section (proj p)) (p₁ : S.∂₁ (proj p) ≡ idS.IdStr (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) → DMor n (suc n)
jjStrS-// Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁ = dmorTm Γ (subst3Ty (getTy P) (getTm a) (getTm b) (getTm p))
                                                                 (Subst3Ty {C = weakenTy (getTy A)} {D = id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)} (der Γ) (dP Γ A A= P P=) (dTm A= a aₛ a₁) (congTmTy (! (weakenSubstTy (getTy A) (getTm a))) (dTm A= b bₛ b₁)) (congTmTy (! (ap-id-Ty subst2Ty-weakenTy refl refl)) (dTm (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) p pₛ p₁)))
                                                                 (jj (getTy A) (getTy P) (getTm d) (getTm a) (getTm b) (getTm p))
                                                                 (JJ (dTy A A=) (dP Γ A A= P P=) dd (dTm A= a aₛ a₁) (dTm A= b bₛ b₁) (dTm (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) p pₛ p₁))
          where dd : Derivable ((ctx Γ , getTy A) ⊢ getTm d :> subst3Ty (weakenTy' (prev (prev (prev last))) (getTy P)) (var last) (var last) (refl (weakenTy (getTy A)) (var last)))
                dd = congTmTy! fixTyJJ (dTm≃ (Ctx≃ft+Ty (reflect A=)) d dₛ d₁)

abstract
  jjStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : ftS (proj A) ≡ proj Γ) (A'= : ftS (proj A') ≡ proj Γ')
              {P P' : DCtx (suc (suc (suc (suc n))))} (rP : P ≃ P') (P= : ftS (proj P) ≡ idS.T-ftP (proj Γ) (proj A) A=) (P'= : ftS (proj P') ≡ idS.T-ftP (proj Γ') (proj A') A'=)
              {d d' : DMor (suc n) (suc (suc n))} (rd : d ≃ d') (dₛ : S.is-section (proj d)) (d'ₛ : S.is-section (proj d'))
              (d₁ : dctx (der (∂₁S-// d)) ≃ T-d₁S Γ A A= P P=) {-⊢ ctx (∂₁S-// d) == (ctx A , ((((getTy' (ctx P) [ weakenMor+ (weakenMor+ (weakenMor+ (weakenMor (idMor n)))) ]Ty) [ weakenMor+ (weakenMor+ (idMor (suc n) , var last)) ]Ty) [ weakenMor+ (idMor (suc n) , var last) ]Ty) [ idMor (suc n) , refl (getTy A [ weakenMor (idMor n) ]Ty) (var last) ]Ty)))-}
              (d'₁ : dctx (der (∂₁S-// d')) ≃ T-d₁S Γ' A' A'= P' P'=) {-⊢ ctx (∂₁S-// d') == (ctx A' , ((((getTy' (ctx P') [ weakenMor+ (weakenMor+ (weakenMor+ (weakenMor (idMor n)))) ]Ty) [ weakenMor+ (weakenMor+ (idMor (suc n) , var last)) ]Ty) [ weakenMor+ (idMor (suc n) , var last) ]Ty) [ idMor (suc n) , refl (getTy A' [ weakenMor (idMor n) ]Ty) (var last) ]Ty)))-}
              {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : S.∂₁ (proj a) ≡ (proj A)) (a'₁ : ∂₁S (proj a') ≡ (proj A'))
              {b b' : DMor n (suc n)} (rb : b ≃ b') (bₛ : S.is-section (proj b)) (b'ₛ : S.is-section (proj b')) (b₁ : S.∂₁ (proj b) ≡ (proj A)) (b'₁ : ∂₁S (proj b') ≡ proj A')
              {p p' : DMor n (suc n)} (rp : p ≃ p') (pₛ : S.is-section (proj p)) (p'ₛ : S.is-section (proj p')) (p₁ : S.∂₁ (proj p) ≡ proj (IdStrS-// Γ A A= a aₛ a₁ b bₛ b₁)) (p'₁ : ∂₁S (proj p') ≡ proj (IdStrS-// Γ' A' A'= a' a'ₛ a'₁ b' b'ₛ b'₁))
            → jjStrS-// Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁ ≃ jjStrS-// Γ' A' A'= P' P'= d' d'ₛ d'₁ a' a'ₛ a'₁ b' b'ₛ b'₁ p' p'ₛ p'₁
  jjStrS-eq {Γ = Γ} {Γ'} rΓ {A = A} {A'} rA A= A'= {P} {P'} rP P= P'= {d} {d'} rd dₛ d'ₛ d₁ d'₁ {a} {a'} ra aₛ a'ₛ a₁ a'₁ {b} {b'} rb bₛ b'ₛ b₁ b'₁ {p} {p'} rp pₛ p'ₛ p₁ p'₁ =
                  dmorTm= dmorTmₛ dmorTmₛ rΓ (SubstTyFullEq' (der Γ)
                                                             (((der Γ , dTy A A=)
                                                             , WeakTy (dTy A A=))
                                                             , Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=))))
                                                             dP=
                                                             ((idMor+= (der Γ) (dTm= A= ra aₛ a'ₛ a₁ a'₁)
                                                             , congTmEqTy (! (weakenSubstTy (getTy A) (getTm a))) (dTm= A= rb bₛ b'ₛ b₁ b'₁))
                                                             , congTmEqTy! (ap-id-Ty subst2Ty-weakenTy refl refl)
                                                                           (dTm= (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ  b₁) rp pₛ p'ₛ p₁ p'₁)))
                                             (JJCong (dTy A A=) (dTy= rA A=) dP= dd=
                                                     (dTm= A= ra aₛ a'ₛ a₁ a'₁) (dTm= A= rb bₛ b'ₛ b₁ b'₁)
                                                     (dTm= (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) rp pₛ p'ₛ p₁ p'₁))
             where dP= : Derivable ((((ctx Γ , getTy A) , weakenTy (getTy A)) , id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)) ⊢ getTy P == getTy P')
                   dP= = ConvTyEq (dTy= rP P=) (CtxSymm (ConvTyDCtxEq (ConvTyDCtxEq (CtxTy=Ctx A A=)
                                                                                    (WeakTy (dTy A A=))
                                                                                    weakenTy-to-[]Ty)
                                                        (Id (WeakTy (WeakTy (dTy A A=)))
                                                            (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=)))
                                                            (VarLast (WeakTy (dTy A A=))))
                                                        (ap-id-Ty (weakenTy-to-[]Ty ∙ ap-[]Ty weakenTy-to-[]Ty refl) refl refl)))     
                   dd= : Derivable ((ctx Γ , getTy A) ⊢ getTm d == getTm d' :> subst3Ty (weakenTy' (prev (prev (prev last))) (getTy P)) (var last) (var last) (refl (weakenTy (getTy A)) (var last)))
                   dd= = congTmEqTy! fixTyJJ (dTm=≃ (Ctx≃ft+Ty (reflect A=)) rd dₛ d'ₛ d₁ d'₁)

jjStrS1 : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (P : DCtx (suc (suc (suc (suc n))))) (P= : ftS (proj P) ≡ idS.T-ftP (proj Γ) (proj A) A=)
          (d : DMor (suc n) (suc (suc n))) (dₛ : S.is-section (proj d))
          (d₁ : ∂₁S (proj d) ≡ reflS.T-d₁ (proj Γ) (proj A) A= (proj P) P=)
          (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : S.∂₁ (proj a) ≡ proj A)
          (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : S.∂₁ (proj b) ≡ proj A)
          (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) → MorS n (suc n)
jjStrS1 Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ =
  //-elim-Tm (λ p pₛ p₁ → proj (jjStrS-// Γ A A= P P= d dₛ rd₁ a aₛ a₁ b bₛ b₁ p pₛ p₁))
             (λ rp pₛ p'ₛ p₁ p'₁ → proj= (jjStrS-eq (ref Γ) (ref A) A= A= (ref P) P= P= (ref d) dₛ dₛ rd₁ rd₁ (ref a) aₛ aₛ a₁ a₁ (ref b) bₛ bₛ b₁ b₁ rp pₛ p'ₛ p₁ p'₁))
   where
     rd₁ = reflectd₁ Γ A A= P P= d d₁


jjStrS2 : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (P : DCtx (suc (suc (suc (suc n))))) (P= : ftS (proj P) ≡ idS.T-ftP (proj Γ) (proj A) A=)
          (d : DMor (suc n) (suc (suc n))) (dₛ : S.is-section (proj d)) (d₁ : ∂₁S (proj d) ≡ reflS.T-d₁ (proj Γ) (proj A) A= (proj P) P=)
          (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : S.∂₁ (proj a) ≡ proj A)
          (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ proj A)
          (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS (proj Γ) (proj A) A= (proj a) aₛ a₁ b bₛ b₁) → MorS n (suc n)
jjStrS2 Γ A A= P P= d dₛ d₁ a aₛ a₁ = //-elim-Tm (λ b bₛ b₁ → jjStrS1 Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁)
                                                 (λ rb bₛ b'ₛ b₁ b'₁ → //-elimP-Tm (λ p pₛ p₁ p₁' → proj= (jjStrS-eq (ref Γ) (ref A) A= A= (ref P) P= P= (ref d) dₛ dₛ rd₁ rd₁ (ref a) aₛ aₛ a₁ a₁ rb bₛ b'ₛ b₁ b'₁ (ref p) pₛ pₛ p₁ p₁')))
  where
    rd₁ = reflectd₁ Γ A A= P P= d d₁


jjStrS3 : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (P : DCtx (suc (suc (suc (suc n))))) (P= : ftS (proj P) ≡ idS.T-ftP (proj Γ) (proj A) A=)
          (d : DMor (suc n) (suc (suc n))) (dₛ : S.is-section (proj d)) (d₁ : ∂₁S (proj d) ≡ reflS.T-d₁ (proj Γ) (proj A) A= (proj P) P=)
          (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ proj A)
          (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ proj A)
          (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS (proj Γ) (proj A) A= a aₛ a₁ b bₛ b₁) → MorS n (suc n)
jjStrS3 Γ A A= P P= d dₛ d₁ = //-elim-Tm (λ a aₛ a₁ → jjStrS2 Γ A A= P P= d dₛ d₁ a aₛ a₁)
                                         (λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ b bₛ b₁ b₁' → //-elimP-Tm (λ p pₛ p₁ p₁' → proj= (jjStrS-eq (ref Γ) (ref A) A= A= (ref P) P= P= (ref d) dₛ dₛ rd₁ rd₁ ra aₛ a'ₛ a₁ a'₁ (ref b) bₛ bₛ b₁ b₁' (ref p) pₛ pₛ p₁ p₁'))))
  where
    rd₁ = reflectd₁ Γ A A= P P= d d₁


jjStrS4 : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (P : DCtx (suc (suc (suc (suc n))))) (P= : ftS (proj P) ≡ idS.T-ftP (proj Γ) (proj A) A=)
          (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ reflS.T-d₁ (proj Γ) (proj A) A= (proj P) P=)
          (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ proj A)
          (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ proj A)
          (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS (proj Γ) (proj A) A= a aₛ a₁ b bₛ b₁) → MorS n (suc n)
jjStrS4 Γ A A= P P= = //-elim-Tm (λ d dₛ d₁ → jjStrS3 Γ A A= P P= d dₛ d₁)
                                 (λ {d} {d'} rd dₛ d'ₛ d₁ d'₁ → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → //-elimP-Tm (λ p pₛ p₁ p₁' → proj= (jjStrS-eq (ref Γ) (ref A) A= A= (ref P) P= P= rd dₛ d'ₛ (reflectd₁ Γ A A= P P= d d₁) (reflectd₁ Γ A A= P P= d' d'₁) (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁' (ref p) pₛ pₛ p₁ p₁')))))

jjStrS5 : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ idS.T-ftP (proj Γ) (proj A) A=)
          (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ reflS.T-d₁ (proj Γ) (proj A) A= P P=)
          (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ proj A)
          (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ proj A)
          (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS (proj Γ) (proj A) A= a aₛ a₁ b bₛ b₁) → MorS n (suc n)
jjStrS5 Γ A A= = //-elim-Ty (λ P P= → jjStrS4 Γ A A= P P=)
                            (λ {P} {P'} rP P= P'= → //-elimP-Tm (λ d dₛ d₁ d₁' → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → //-elimP-Tm (λ p pₛ p₁ p₁' → proj= (jjStrS-eq (ref Γ) (ref A) A= A= rP P= P'= (ref d) dₛ dₛ (reflect d₁) (reflect d₁') (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁' (ref p) pₛ pₛ p₁ p₁'))))))
                            
jjStrS6 : (Γ : DCtx n) (A : ObS (suc n)) (A= : ftS A ≡ proj Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ idS.T-ftP (proj Γ) A A=)
          (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ reflS.T-d₁ (proj Γ) A A= P P=)
          (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A)
          (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ A)
          (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS (proj Γ) A A= a aₛ a₁ b bₛ b₁) → MorS n (suc n)
jjStrS6 Γ = //-elim-Ty (λ A A= → jjStrS5 Γ A A=)
                       (λ {A} {A'} rA A= A'= → //-elimP-Ty (λ P P= P=' → //-elimP-Tm (λ d dₛ d₁ d₁' → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → //-elimP-Tm (λ p pₛ p₁ p₁' → proj= (jjStrS-eq (ref Γ) rA A= A'= (ref P) P= P=' (ref d) dₛ dₛ (reflect d₁) (reflect d₁') (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁' (ref p) pₛ pₛ p₁ p₁')))))))

jjStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ idS.T-ftP Γ A A=)
         (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ reflS.T-d₁ Γ A A= P P=)
         (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A)
         (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ A)
         (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS Γ A A= a aₛ a₁ b bₛ b₁) → MorS n (suc n)
jjStrS = //-elim-Ctx (λ Γ → jjStrS6 Γ)
                     (λ {Γ} {Γ'} rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ P P= P=' → //-elimP-Tm (λ d dₛ d₁ d₁' → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → //-elimP-Tm (λ p pₛ p₁ p₁' → proj= (jjStrS-eq rΓ (ref A) A= A=' (ref P) P= P=' (ref d) dₛ dₛ (reflect d₁) (reflect d₁') (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁' (ref p) pₛ pₛ p₁ p₁'))))))))
