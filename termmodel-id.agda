{-# OPTIONS --rewriting --prop --without-K --no-auto-inline #-}

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

module idS = CCatwithId IdStrSynCCat

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
 

module reflS = CCatwithrefl reflStrSynCCat

{- JJ (TODO) -}

postulate
  #TODO#S : ∀ {l} {A : Set l} → A
  #TODO# : {P : Prop} → P

{- probably this is already the correct fix but we cannot check it untill agda accepts d₁ -}
fixTyJJ : {A : TyExpr n} {P : TyExpr (suc (suc (suc n)))} → subst3Ty (weakenTy' (prev (prev (prev last))) P) (var last) (var last) (refl (weakenTy A) (var last)) ≡ (((P [ weakenMor+ (weakenMor+ (weakenMor+ (weakenMor (idMor n)))) ]Ty) [ weakenMor+ (weakenMor+ (idMor (suc n) , var last)) ]Ty) [ weakenMor+ (idMor (suc n) , var last) ]Ty) [ idMor (suc n) , refl (weakenTy A) (var last) ]Ty
fixTyJJ = #TODO#

-- star+S-// : (g : DMor n m) (X : DCtx (suc (suc m))) {X' : DCtx (suc m)} (X= : ftS (proj X) ≡ proj X') {X'' : DCtx m} (X'= : ftS (proj X') ≡ proj X'') (g₁ : ∂₁S (proj g) ≡ proj X'') → DCtx (suc (suc n))
-- star+S-// g X X= X'= g₁ = starS-// (qqS-// g _ _ X'= g₁) X _ X= (qq₁S-// g _ _ X'= g₁)

-- star++S-// : (g : DMor n m) (X : DCtx (suc (suc (suc m)))) {X' : DCtx (suc (suc m))} (X= : ftS (proj X) ≡ proj X') {X'' : DCtx (suc m)} (X'= : ftS (proj X') ≡ proj X'') {X''' : DCtx m} (X''= : ftS (proj X'') ≡ proj X''') (g₁ : ∂₁S (proj g) ≡ proj X''') → DCtx (suc (suc (suc n)))
-- star++S-// g X {X'} X= {X''} X'= {X'''} X''= g₁ = star+S-// (qqS-// g X'' _ X''= g₁) X X= X'= (qq₁S-// g _ _ X''= g₁)
  
-- star+++S-// : (g : DMor n m) (X : DCtx (suc (suc (suc (suc m))))) {X' : DCtx (suc (suc (suc m)))} (X= : ftS (proj X) ≡ proj X') {X'' : DCtx (suc (suc m))} (X'= : ftS (proj X') ≡ proj X'') {X''' : DCtx (suc m)} (X''= : ftS (proj X'') ≡ proj X''') {X'''' : DCtx m} (X'''= : ftS (proj X''') ≡ proj X'''') (g₁ : ∂₁S (proj g) ≡ proj X'''') → DCtx (suc (suc (suc (suc n))))
-- star+++S-// g X {X'} X= {X''} X'= {X'''} X''= {X''''} X'''= g₁ = star++S-// (qqS-// g X''' _ X'''= g₁) X X= X'= X''= (qq₁S-// g _ _ X'''= g₁)


-- T-d₁S : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (P : DCtx (suc (suc (suc (suc n))))) (P= : ftS (proj P) ≡ T-ftP IdStrSynCCat (proj Γ) (proj A) A=)
--        → DCtx (suc (suc n))  
-- T-d₁S Γ A A= P P= = starS-// (reflStrS-// A (starS-// (ppS-// A) A _ A= (pp₁S (proj A) ∙ A=)) eq1 (ssS-// (idS-// _ A)) (S.varCₛ last (proj A)) (S.varCL₁ {X = proj A} {X= = A=}))
--                              (star+S-// (ssS-// (idS-// _ A))
--                                         (star++S-// (ssS-// (idS-// _ A)) (star+++S-// (ppS-// A) P P= (T-ftP= IdStrSynCCat) eq12 A= (pp₁S (proj A) ∙ A=)) eq2 eq3 eq4 (S.varCL₁ {X = proj A} {X= = A=}))
--                                         eq5 eq6 eq7)
--                              _
--                              eq8
--                              {!!}
--       where eq1 = S.ft-star ∙ S.pp₀
--             eq2 = S.ft-star ∙ S.qq₀
--             eq3 = S.ft-star ∙ S.qq₀
--             eq4 = S.ft-star ∙ S.qq₀
--             eq5 = S.ft-star ∙ S.qq₀
--             eq6 = S.ft-star ∙ S.qq₀
--             eq7 = S.varCL₁ {X = proj A} {X= = A=} ∙ ! S.star-varCL-star-qqpp
--             eq8 = S.ft-star ∙ S.qq₀
--             eq10 = S.ft-star ∙ S.pp₀
--             eq11 = S.ft-star ∙ S.pp₀
--             eq12 = S.ft-star ∙ S.pp₀



jjStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ) (P : DCtx (suc (suc (suc (suc n))))) (P= : S.ft (proj P) ≡ idS.T-ftP (proj Γ) (proj A) A=)
            (d : DMor (suc n) (suc (suc n))) (dₛ : S.is-section (proj d)) (d₁ : S.∂₁ (proj d) ≡ reflS.T-d₁ (proj Γ) (proj A) A= (proj P) P=)
            (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : S.∂₁ (proj a) ≡ (proj A))
            (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : S.∂₁ (proj b) ≡ (proj A))
            (p : DMor n (suc n)) (pₛ : S.is-section (proj p)) (p₁ : S.∂₁ (proj p) ≡ idS.IdStr (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) → DMor n (suc n)
jjStrS-// Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁ = dmorTm Γ (subst3Ty (getTy P) (getTm a) (getTm b) (getTm p))
                                                                 (Subst3Ty {C = weakenTy (getTy A)} {D = id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)} (der Γ) dP (dTm A= a aₛ a₁) (congTmTy (! (weakenSubstTy (getTy A) (getTm a))) (dTm A= b bₛ b₁)) (congTmTy (! (ap-id-Ty subst2Ty-weakenTy refl refl)) (dTm (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) p pₛ p₁)))
                                                                 (jj (getTy A) (getTy P) (getTm d) (getTm a) (getTm b) (getTm p))
                                                                 (JJ (dTy A A=) dP dd (dTm A= a aₛ a₁) (dTm A= b bₛ b₁) (dTm (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) p pₛ p₁))
          where dP : Derivable ((((ctx Γ , getTy A) , weakenTy (getTy A)) , id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)) ⊢ getTy P)
                dP = dTy {Γ = ((((_ , _) , _) , _) , (((der Γ , dTy A A=) , WeakTy (dTy A A=)) , Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))} P (P= ∙ eq (box (CtxSymm ((CtxTy=Ctx A A= ,, congTyEq refl weakenTy-to-[]Ty (TyRefl (WeakTy (dTy A A=)))) ,,
                                                    congTyEq refl (ap-id-Ty (weakenTy-to-[]Ty ∙ ap (λ z → z [ _ ]Ty) weakenTy-to-[]Ty) refl refl)
                                                                  (TyRefl (Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))))))
                dd : Derivable ((ctx Γ , getTy A) ⊢ getTm d :> subst3Ty (weakenTy' (prev (prev (prev last))) (getTy P)) (var last) (var last) (refl (weakenTy (getTy A)) (var last)))
                dd = congTmTy! #TODO# (dTm {Γ = ((_ , _) , (der Γ , dTy A A=))} {A = #TODO#S} #TODO# d dₛ #TODO#)

{-A = ((ctx A , (((getTy P [ weakenMor+ (weakenMor+ (weakenMor+ (weakenMor (idMor _)))) ]Ty) [ weakenMor+ (weakenMor+ (idMor (suc _) , var last)) ]Ty) [ weakenMor+ (idMor (suc _) , var last) ]Ty) [ idMor (suc _) , refl (weakenTy (getTy A)) (var last) ]Ty) , (der A , ConvTy (SubstTy {Δ = (ctx Γ , getTy A) , id (weakenTy (getTy A)) (var last) (var last)} (SubstTy {Δ = ((ctx Γ , getTy A) , weakenTy (getTy A)) , id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)} (SubstTy {Δ = ((((ctx Γ , getTy A) , weakenTy (getTy A)) , weakenTy' (prev last) (weakenTy (getTy A))) , weakenTy' (prev (prev last)) (id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)))} (SubstTy dP (((WeakMor (WeakMor (WeakMor (WeakMor (idMorDerivable (der Γ))))) , congTmTy {!!} (VarPrev (WeakTy (WeakTy (WeakTy (dTy A A=)))) (VarPrev (WeakTy (WeakTy (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))) , congTmTy {!!} (VarPrev (WeakTy (WeakTy (WeakTy (dTy A A=)))) (VarLast (WeakTy (WeakTy (dTy A A=)))))) , congTmTy {!!} (VarLast (WeakTy (Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))))) ((((WeakMor (WeakMor (WeakMor (idMorDerivable (der Γ)))) , congTmTy {!!} (VarPrev (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))))) , congTmTy {!!} (VarPrev (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))))) , congTmTy {!!} (VarPrev (WeakTy (WeakTy (dTy A A=))) (VarLast (WeakTy (dTy A A=))))) , congTmTy {!!} (VarLast (Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=))))))) ((((WeakMor (WeakMor (idMorDerivable (der Γ))) , congTmTy (weakenTy-to-[]Ty ∙ ap (λ z → z [ _ ]Ty) weakenTy-to-[]Ty ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty (getTy A)) (weakenMorInsert _ _ _ ∙ idMor[]Mor _)) (WeakTm (VarLast (dTy A A=)))) , congTmTy weakenTy-to-[]Ty (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))))) , congTmTy (weakenTy-to-[]Ty ∙ ap-id-Ty (weakenTyInsert _ _ _ ∙ ! (weakenTyInsert _ _ _ ∙ weakenTyInsert _ _ _)) refl refl) (VarLast (Id (WeakTy (dTy A A=)) (VarLast (dTy A A=)) (VarLast (dTy A A=)))))) (idMor+ (der Γ , dTy A A=) (Refl (WeakTy (dTy A A=)) (VarLast (dTy A A=))))) (CtxTy=Ctx A A=)))-} 

jjStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : ftS (proj A) ≡ proj Γ) (A'= : ftS (proj A') ≡ proj Γ') {P P' : DCtx (suc (suc (suc (suc n))))} (rP : P ≃ P') (P= : ftS (proj P) ≡ idS.T-ftP (proj Γ) (proj A) A=) (P'= : ftS (proj P') ≡ idS.T-ftP (proj Γ') (proj A') A'=) {d d' : DMor (suc n) (suc (suc n))} (rd : d ≃ d') (dₛ : S.is-section (proj d)) (d'ₛ : S.is-section (proj d')) (d₁ : ∂₁S (proj d) ≡ reflS.T-d₁ (proj Γ) (proj A) A= (proj P) P=) (d'₁ : ∂₁S (proj d') ≡ reflS.T-d₁ (proj Γ') (proj A') A'= (proj P') P'=) {a a' : DMor n (suc n)} (ra : a ≃ a') (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a')) (a₁ : S.∂₁ (proj a) ≡ (proj A)) (a'₁ : ∂₁S (proj a') ≡ (proj A')) {b b' : DMor n (suc n)} (rb : b ≃ b') (bₛ : S.is-section (proj b)) (b'ₛ : S.is-section (proj b')) (b₁ : S.∂₁ (proj b) ≡ (proj A)) (b'₁ : ∂₁S (proj b') ≡ proj A') {p p' : DMor n (suc n)} (rp : p ≃ p') (pₛ : S.is-section (proj p)) (p'ₛ : S.is-section (proj p')) (p₁ : S.∂₁ (proj p) ≡ proj (IdStrS-// Γ A A= a aₛ a₁ b bₛ b₁)) (p'₁ : ∂₁S (proj p') ≡ proj (IdStrS-// Γ' A' A'= a' a'ₛ a'₁ b' b'ₛ b'₁)) → proj {R = MorEquiv} (jjStrS-// Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁) ≡ proj (jjStrS-// Γ' A' A'= P' P'= d' d'ₛ d'₁ a' a'ₛ a'₁ b' b'ₛ b'₁ p' p'ₛ p'₁)
jjStrS-eq {Γ = Γ} {Γ'} rΓ {A = A} {A'} rA A= A'= {P} {P'} rP P= P'= {d} {d'} rd dₛ d'ₛ d₁ d'₁ {a} {a'} ra aₛ a'ₛ a₁ a'₁ {b} {b'} rb bₛ b'ₛ b₁ b'₁ {p} {p'} rp pₛ p'ₛ p₁ p'₁ =
  dmorTm= rΓ (Subst3Ty {C = weakenTy (getTy A)} {D = id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)} (der Γ) dP (dTm A= a aₛ a₁) (congTmTy (! (weakenSubstTy (getTy A) (getTm a))) (dTm A= b bₛ b₁)) (congTmTy (! (ap-id-Ty subst2Ty-weakenTy refl refl)) (dTm (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) p pₛ p₁)))
             (Subst3Ty {C = weakenTy (getTy A')} {D = id (weakenTy (weakenTy (getTy A'))) (var (prev last)) (var last)} (der Γ') dP' (dTm A'= a' a'ₛ a'₁) (congTmTy (! (weakenSubstTy (getTy A') (getTm a'))) (dTm A'= b' b'ₛ b'₁)) (congTmTy (! (ap-id-Ty subst2Ty-weakenTy refl refl)) (dTm (IdStr=S (proj Γ') (proj A') A'= (proj a') a'ₛ a'₁ (proj b') b'ₛ b'₁) p' p'ₛ p'₁)))
             (Subst3TyEq (der Γ) (ConvTy dP' (CtxSymm (((unOb≃ rΓ ,, dTy= rA A=) ,, WeakTyEq (dTy= rA A=)) ,, IdCong (WeakTyEq (WeakTyEq (dTy= rA A=))) (VarPrevCong (WeakTy (dTy A A=)) (VarLastCong (dTy A A=))) (VarLastCong (WeakTy (dTy A A=))))))
                                 (dTm A= a aₛ a₁) (congTmTy (! (weakenSubstTy (getTy A) (getTm a))) (dTm A= b bₛ b₁)) ((congTmTy (! (ap-id-Ty subst2Ty-weakenTy refl refl)) (dTm (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) p pₛ p₁)))
                                 (dTy= {Γ = ((((_ , _) , _) , _) , (((der Γ , dTy A A=) , WeakTy (dTy A A=)) , Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))} rP (P= ∙ eq (box (CtxSymm ((CtxTy=Ctx A A= ,, congTyEq refl weakenTy-to-[]Ty (TyRefl (WeakTy (dTy A A=)))) ,, congTyEq refl (ap-id-Ty (weakenTy-to-[]Ty ∙ ap (λ z → z [ _ ]Ty) weakenTy-to-[]Ty) refl refl) (TyRefl (Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=))))))))))
                                 (dTm= rA A= ra aₛ a'ₛ a₁ a'₁) (congTmEqTy (! (weakenSubstTy (getTy A) (getTm a))) (dTm= rA A= rb bₛ b'ₛ b₁ b'₁)) (congTmEqTy (! (ap-id-Ty subst2Ty-weakenTy refl refl)) (dTm= (box (unOb≃ rΓ ,, IdCong (dTy= rA A=) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁) (dTm= rA A= rb bₛ b'ₛ b₁ b'₁))) (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ  b₁) rp pₛ p'ₛ p₁ p'₁)))
             (JJ (dTy A A=) dP dd (dTm A= a aₛ a₁) (dTm A= b bₛ b₁) (dTm (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) p pₛ p₁))
             (JJ (dTy A' A'=) dP' dd' (dTm A'= a' a'ₛ a'₁) (dTm A'= b' b'ₛ b'₁) (dTm (IdStr=S (proj Γ') (proj A') A'= (proj a') a'ₛ a'₁ (proj b') b'ₛ b'₁) p' p'ₛ p'₁))
             (JJCong (dTy A A=) (dTy= rA A=) (dTy= {Γ = ((((_ , _) , _) , _) , (((der Γ , dTy A A=) , WeakTy (dTy A A=)) , Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))} rP (P= ∙ eq (box (CtxSymm ((CtxTy=Ctx A A= ,, congTyEq refl weakenTy-to-[]Ty (TyRefl (WeakTy (dTy A A=)))) ,, congTyEq refl (ap-id-Ty (weakenTy-to-[]Ty ∙ ap (λ z → z [ _ ]Ty) weakenTy-to-[]Ty) refl refl) (TyRefl (Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=))))))))))
                     dd= (dTm= rA A= ra aₛ a'ₛ a₁ a'₁) (dTm= rA A= rb bₛ b'ₛ b₁ b'₁) (dTm= (box (unOb≃ rΓ ,, IdCong (dTy= rA A=) (dTm= rA A= ra aₛ a'ₛ a₁ a'₁) (dTm= rA A= rb bₛ b'ₛ b₁ b'₁))) (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) rp pₛ p'ₛ p₁ p'₁))
             where dP : Derivable ((((ctx Γ , getTy A) , weakenTy (getTy A)) , id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)) ⊢ getTy P)
                   dP = dTy {Γ = ((((_ , _) , _) , _) , (((der Γ , dTy A A=) , WeakTy (dTy A A=)) , Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))} P (P= ∙ eq (box (CtxSymm ((CtxTy=Ctx A A= ,, congTyEq refl weakenTy-to-[]Ty (TyRefl (WeakTy (dTy A A=)))) ,,
                                                    congTyEq refl (ap-id-Ty (weakenTy-to-[]Ty ∙ ap (λ z → z [ _ ]Ty) weakenTy-to-[]Ty) refl refl)
                                                                  (TyRefl (Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))))))
                   dP' : Derivable ((((ctx Γ' , getTy A') , weakenTy (getTy A')) , id (weakenTy (weakenTy (getTy A'))) (var (prev last)) (var last)) ⊢ getTy P')
                   dP' = dTy {Γ = ((((_ , _) , _) , _) , (((der Γ' , dTy A' A'=) , WeakTy (dTy A' A'=)) , Id (WeakTy (WeakTy (dTy A' A'=))) (VarPrev (WeakTy (dTy A' A'=)) (VarLast (dTy A' A'=))) (VarLast (WeakTy (dTy A' A'=)))))} P' (P'= ∙ eq (box (CtxSymm ((CtxTy=Ctx A' A'= ,, congTyEq refl weakenTy-to-[]Ty (TyRefl (WeakTy (dTy A' A'=)))) ,,
                                                    congTyEq refl (ap-id-Ty (weakenTy-to-[]Ty ∙ ap (λ z → z [ _ ]Ty) weakenTy-to-[]Ty) refl refl)
                                                                  (TyRefl (Id (WeakTy (WeakTy (dTy A' A'=))) (VarPrev (WeakTy (dTy A' A'=)) (VarLast (dTy A' A'=))) (VarLast (WeakTy (dTy A' A'=)))))))))
                   dd : Derivable ((ctx Γ , getTy A) ⊢ getTm d :> subst3Ty (weakenTy' (prev (prev (prev last))) (getTy P)) (var last) (var last) (refl (weakenTy (getTy A)) (var last)))
                   dd = congTmTy! #TODO# (dTm {Γ = ((_ , _) , (der Γ , dTy A A=))} {A = #TODO#S} #TODO# d dₛ #TODO#)
                   dd' : Derivable ((ctx Γ' , getTy A') ⊢ getTm d' :> subst3Ty (weakenTy' (prev (prev (prev last))) (getTy P')) (var last) (var last) (refl (weakenTy (getTy A')) (var last)))
                   dd' = congTmTy! #TODO# (dTm {Γ = ((_ , _) , (der Γ' , dTy A' A'=))} {A = #TODO#S} #TODO# d' d'ₛ #TODO#)
                   dd= : Derivable ((ctx Γ , getTy A) ⊢ getTm d == getTm d' :> subst3Ty (weakenTy' (prev (prev (prev last))) (getTy P)) (var last) (var last) (refl (weakenTy (getTy A)) (var last)))
                   dd= = congTmEqTy! #TODO# (dTm= {Γ = ((_ , _) , (der Γ , dTy A A=))} {A = #TODO#S} {A' = #TODO#S} #TODO# #TODO# rd dₛ d'ₛ #TODO# #TODO#)

jjStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ idS.T-ftP Γ A A=)
         (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ reflS.T-d₁ Γ A A= P P=)
         (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A)
         (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ A)
         (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS Γ A A= a aₛ a₁ b bₛ b₁) → MorS n (suc n)
jjStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ P P= → //-elim-Tm (λ d dₛ d₁ → //-elim-Tm (λ a aₛ a₁ → //-elim-Tm (λ b bₛ b₁ → //-elim-Tm (λ p pₛ p₁ → proj (jjStrS-// Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁))
                                                                                                                                                         #TODO# {-(λ rp pₛ p'ₛ p₁ p'₁ → proj= (jjStrS-eq (ref Γ) (ref A) A= A= (ref P) P= P= (ref d) dₛ dₛ d₁ d₁ (ref a) aₛ aₛ a₁ a₁ (ref b) bₛ bₛ b₁ b₁ rp pₛ p'ₛ p₁ p'₁))-})
                                                                                                                                 #TODO# {-(λ rb bₛ b'ₛ b₁ b'₁ → //-elimP-Tm (λ p pₛ p₁ p₁' → proj= (jjStrS-eq (ref Γ) (ref A) A= A= (ref P) P= P= (ref d) dₛ dₛ d₁ d₁ (ref a) aₛ aₛ a₁ a₁ rb bₛ b'ₛ b₁ b'₁ (ref p) pₛ pₛ p₁ p₁')))-})
                                                                                                         #TODO# {-(λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ b bₛ b₁ b₁' → //-elimP-Tm (λ p pₛ p₁ p₁' → proj= (jjStrS-eq (ref Γ) (ref A) A= A= (ref P) P= P= (ref d) dₛ dₛ d₁ d₁ ra aₛ a'ₛ a₁ a'₁ (ref b) bₛ bₛ b₁ b₁' (ref p) pₛ pₛ p₁ p₁'))))-})
                                                                                 #TODO# {-(λ rd dₛ d'ₛ d₁ d'₁ → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → //-elimP-Tm (λ p pₛ p₁ p₁' → proj= (jjStrS-eq (ref Γ) (ref A) A= A= (ref P) P= P= rd dₛ d'ₛ d₁ d'₁ (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁' (ref p) pₛ pₛ p₁ p₁')))))-})
                                                            #TODO# {-(λ rP P= P'= → //-elimP-Tm (λ d dₛ d₁ d₁' → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → //-elimP-Tm (λ p pₛ p₁ p₁' → proj= (jjStrS-eq (ref Γ) (ref A) A= A= rP P= P'= (ref d) dₛ dₛ d₁ d₁' (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁' (ref p) pₛ pₛ p₁ p₁'))))))-})
                                       #TODO# {-(λ rA A= A'= → //-elimP-Ty (λ P P= P=' → //-elimP-Tm (λ d dₛ d₁ d₁' → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → //-elimP-Tm (λ p pₛ p₁ p₁' → proj= (jjStrS-eq (ref Γ) rA A= A'= (ref P) P= P=' (ref d) dₛ dₛ d₁ d₁' (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁' (ref p) pₛ pₛ p₁ p₁')))))))-})
                     #TODO# --(λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ P P= P=' → //-elimP-Tm (λ d dₛ d₁ d₁' → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → //-elimP-Tm (λ p pₛ p₁ p₁' → proj= (jjStrS-eq rΓ (ref A) A= A=' (ref P) P= P=' (ref d) dₛ dₛ d₁ d₁' (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁' (ref p) pₛ pₛ p₁ p₁'))))))))
                                                                                                                                                         


jjStrₛS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ idS.T-ftP Γ A A=) (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ reflS.T-d₁ Γ A A= P P=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ A) (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS Γ A A= a aₛ a₁ b bₛ b₁) → S.is-section (jjStrS Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁)
jjStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → //-elimP (λ p pₛ p₁ →
                   let dP = dTy {Γ = ((((_ , _) , _) , _) , (((der Γ , dTy A A=) , WeakTy (dTy A A=)) , Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))}
                                P (P= ∙ eq (box (CtxSymm ((CtxTy=Ctx A A= ,, congTyEq refl weakenTy-to-[]Ty (TyRefl (WeakTy (dTy A A=)))) ,,
                                                 congTyEq refl (ap-id-Ty (weakenTy-to-[]Ty ∙ ap (λ z → z [ _ ]Ty) weakenTy-to-[]Ty) refl refl)
                                                               (TyRefl (Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))))))
                       dd = congTmTy! #TODO# (dTm {Γ = ((_ , _) , (der Γ , dTy A A=))} {A = #TODO#S} #TODO# d dₛ #TODO#)
                       in dmorTmₛ (Subst3Ty {C = weakenTy (getTy A)} {D = id (weakenTy (weakenTy (getTy A))) (var (prev last)) (var last)} (der Γ) dP (dTm A= a aₛ a₁) (congTmTy (! (weakenSubstTy (getTy A) (getTm a))) (dTm A= b bₛ b₁)) (congTmTy (! (ap-id-Ty subst2Ty-weakenTy refl refl)) (dTm (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) p pₛ p₁))) (JJ (dTy A A=) dP dd (dTm A= a aₛ a₁) (dTm A= b bₛ b₁) (dTm (IdStr=S (proj Γ) (proj A) A= (proj a) aₛ a₁ (proj b) bₛ b₁) p pₛ p₁)))))))))

jjStr₁S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ idS.T-ftP Γ A A=) (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ reflS.T-d₁ Γ A A= P P=) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A) (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ A) (p : MorS n (suc n)) (pₛ : S.is-section p) (p₁ : S.∂₁ p ≡ IdStrS Γ A A= a aₛ a₁ b bₛ b₁) → ∂₁S (jjStrS Γ A A= P P= d dₛ d₁ a aₛ a₁ b bₛ b₁ p pₛ p₁) ≡ idS.T-jjStr₁ Γ A A= P P= a aₛ a₁ b bₛ b₁ p pₛ p₁
jjStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → //-elimP (λ p pₛ p₁ → #TODO#)))))))


jjStrSynCCat : CCatwithjj synCCat IdStrSynCCat reflStrSynCCat
CCatwithjj.jjStr jjStrSynCCat = jjStrS
CCatwithjj.jjStrₛ jjStrSynCCat {Γ = Γ} {A = A} {P = P} {d = d} {a = a} {b = b} {p = p} = jjStrₛS Γ A _ P _ d _ _ a _ _ b _ _ p _ _
CCatwithjj.jjStr₁ jjStrSynCCat {Γ = Γ} {A = A} {P = P} {d = d} {a = a} {b = b} {p = p} = jjStr₁S Γ A _ P _ d _ _ a _ _ b _ _ p _ _
CCatwithjj.jjStrNat' jjStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → //-elimP (λ p pₛ p₁ g₁ → #TODO#)))))))))

{- ElId= -}

elidStrS : (i : ℕ) (Γ : ObS n) (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ ElStrS i Γ a aₛ a₁)
                   (v : MorS n (suc n)) (vₛ : S.is-section v) (v₁ : ∂₁S v ≡ ElStrS i Γ a aₛ a₁) → ElStrS i Γ (idStrS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStrₛS i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) (idStr₁S i Γ a aₛ a₁ u uₛ u₁ v vₛ v₁) ≡ IdStrS Γ (ElStrS i Γ a aₛ a₁) (ElStr=S i Γ a aₛ a₁) u uₛ u₁ v vₛ v₁
elidStrS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ u uₛ u₁ → //-elimP (λ v vₛ v₁ → eq (box (CtxRefl (der Γ) ,, ElId= (dTm refl a aₛ a₁) (dTm refl u uₛ u₁) (dTm refl v vₛ v₁)))))))


{- BetaJ (TODO) -}


betaIdStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (P : ObS (suc (suc (suc (suc n))))) (P= : ftS P ≡ idS.T-ftP Γ A A=)
             (d : MorS (suc n) (suc (suc n))) (dₛ : S.is-section d) (d₁ : ∂₁S d ≡ reflS.T-d₁ Γ A A= P P=)
             (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
           → jjStrS Γ A A= P P= d dₛ d₁ a aₛ a₁ a aₛ a₁ (reflStrS Γ A A= a aₛ a₁) (reflStrₛS Γ A A= a aₛ a₁) (reflStr₁S Γ A A= a aₛ a₁) ≡ S.starTm a d (S.is-section₀ dₛ d₁ ∙ reflS.T-d₁=) a₁
betaIdStrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ P P= → //-elimP (λ d dₛ d₁ → //-elimP (λ a aₛ a₁ →
                      let dP = dTy {Γ = ((((_ , _) , _) , _) , (((der Γ , dTy A A=) , WeakTy (dTy A A=)) , Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))}
                                   P (P= ∙ eq (box (CtxSymm ((CtxTy=Ctx A A= ,, congTyEq refl weakenTy-to-[]Ty (TyRefl (WeakTy (dTy A A=)))) ,,
                                                   congTyEq refl (ap-id-Ty (weakenTy-to-[]Ty ∙ ap (λ z → z [ _ ]Ty) weakenTy-to-[]Ty) refl refl)
                                                                 (TyRefl (Id (WeakTy (WeakTy (dTy A A=))) (VarPrev (WeakTy (dTy A A=)) (VarLast (dTy A A=))) (VarLast (WeakTy (dTy A A=)))))))))
                          dd = congTmTy! #TODO# (dTm {Γ = ((_ , _) , (der Γ , dTy A A=))} {A = #TODO#S} #TODO# d dₛ #TODO#)
                      in eq (box (CtxSymm (reflectOb (S.is-section₀ aₛ a₁ ∙ A=)))
                            (CtxSymm (reflectOb (S.is-section₀ aₛ a₁ ∙ A=)) ,,  congTyEq {A = (((((getTy P) [ weakenMor+ (weakenMor+ (weakenMor+ (weakenMor (idMor _)))) ]Ty) [ weakenMor+ (weakenMor+ (idMor (suc _) , var last)) ]Ty) [ weakenMor+ (idMor (suc _) , var last) ]Ty) [ idMor (suc _) , refl (weakenTy (getTy A)) (var last) ]Ty) [ idMor _ , getTm a ]Ty}
                                                                                         (ap (λ z → (((z [ weakenMor+ (weakenMor+ ((weakenMor (idMor _) , var last) , var last)) ]Ty) [ weakenMor+ ((weakenMor (idMor _) , var last) , var last) ]Ty) [ (weakenMor (idMor _) , var last) , refl (weakenTy (getTy A)) (var last) ]Ty) [ idMor _ , getTm a ]Ty)
                                                                                             (! weakenTy+++-to-[]Ty)
                                                                                          ∙ ap (λ z → z [ idMor _ , getTm a ]Ty)
                                                                                               ([]Ty-assoc _ _ _ ∙ []Ty-assoc _ _ _ ∙ ap (λ z → (weakenTy' (prev (prev (prev last))) (getTy P)) [ z ]Ty)
                                                                                                                                         (Mor+= (Mor+= (Mor+= (Mor+= (weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _ ∙ weakenMorInsert _ _ _ ∙ weakenMorInsert _ _ _ ∙ idMor[]Mor _) refl) refl) refl) refl))
                                                                                          ∙ []Ty-assoc _ _ _ ∙ ap (_[_]Ty (weakenTy' (prev (prev (prev last))) (getTy P)))
                                                                                                                  (Mor+= (Mor+= (Mor+= (Mor+= (weakenMorInsert _ _ _ ∙ idMor[]Mor _) refl) refl) refl) (ap (λ z → refl z (getTm a)) (weakenSubstTy _ _)))
                                                                                          ∙ weakenTyInsert' (prev (prev (prev last))) (getTy P) _ (getRHS (mor a)))
                                                                                         refl
                                                                                         (SubstTyMorEq2 {Δ = ctx Γ , getTy A} (der Γ) (der Γ , dTy A A=) (dTy= {Γ = ((_ , _) , (der Γ , dTy A A=))} {A = ((_ , _ ) , _) , ((der Γ , dTy A A=) , congTy fixTyJJ (Subst3Ty (der Γ , dTy A A=) (WeakTy dP) (VarLast (dTy A A=)) (congTmTy (! (weakenTyInsert' (prev last) _ _ _ ∙ [idMor]Ty _)) (VarLast (dTy A A=))) (congTmTy (ap-id-Ty (! (weakenTyInsert' (prev (prev last)) _ (idMor _ , var last) (var last) ∙ substTy-weakenTy)) refl refl) (Refl (WeakTy (dTy A A=)) (VarLast (dTy A A=))))))} (reflect (#TODO# ∙ ! d₁)) #TODO#) (MorTran (der Γ) (der Γ , dTy A A=) (MorSymm (der Γ) (der Γ , dTy A A=) (morTm=idMorTm A= a aₛ a₁)) (congMorEq refl refl (idMor[]Mor _) refl (SubstMorEq {Γ = ctx Γ} {θ = idMor _} {θ' = getMor d} (MorSymm (der Γ , dTy A A=) (der Γ , dTy A A=) (getMor=idMor {Γ = ((_ , _) , (der Γ , dTy A A=))} {A = #TODO#S} #TODO# d dₛ #TODO#)) (dMor A= a aₛ a₁))))))
                            (idMor+= (der Γ) (TmTran' (der Γ) (BetaIdRefl (dTy A A=) dP dd (dTm A= a aₛ a₁)) (congTmEqTy ([]Ty-subst3Ty ∙ ap-subst3Ty (weakenTyInsertLemma3 last _ _ (getTm a) ∙ weakenTyInsert' (prev (prev (prev last))) (getTy P) _ _ ∙ [idMor]Ty _) refl refl (ap (λ z → refl z (getRHS (mor a))) (weakenSubstTy _ _))) (SubstTmMorEq dd (idMor+ (der Γ) (dTm A= a aₛ a₁)) (MorSymm (der Γ) (der Γ , dTy A A=) (morTm=idMorTm A= a aₛ a₁))))))))))))


