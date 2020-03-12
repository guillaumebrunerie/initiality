{-# OPTIONS --rewriting --prop #-}

open import common
open import reflection hiding (proj)
open import typetheory
open import syntx hiding (getTy)
open import rules 
open import contextualcat
open import quotients
open import termmodel-common
open import termmodel-synccat
open import termmodel-uuel

open CCat hiding (Mor) renaming (id to idC)


{- Sum -}

SumStrS-// : (Γ : DCtx n) (A : DCtx (suc n)) (A= : ftS (proj A) ≡ proj Γ) (B : DCtx (suc n)) (B= : ftS (proj B) ≡ proj Γ) → DCtx (suc n)
SumStrS-// Γ A A= B B= = dctx (der Γ , Sum (dTy A A=) (dTy B B=))

SumStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ') {A A' : DCtx (suc n)} (rA : A ≃ A') (A= : _) (A'= : _)
             {B B' : DCtx (suc n)} (rB : B ≃ B') (B= : _) (B'= : _)
           → SumStrS-// Γ A A= B B= ≃ SumStrS-// Γ' A' A'= B' B'=
SumStrS-eq rΓ {A = A} rA A= A'= rB B= B'= = box (unOb≃ rΓ , SumCong (dTy= rA A=) (dTy= rB B=))

SumStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc n)) (B= : ftS B ≡ Γ)
        → ObS (suc n)
SumStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → proj (SumStrS-// Γ A A= B B=))
                                                             (λ rB B= B'= → proj= (SumStrS-eq (ref Γ) (ref A) A= A= rB B= B'=)))
                                        (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → proj= (SumStrS-eq (ref Γ) rA A= A'= (ref B) B= B='))))
                      (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → proj= (SumStrS-eq rΓ (ref A) A= A=' (ref B) B= B='))))

SumStr=S : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc n)) (B= : ftS B ≡ Γ)
         → ftS (SumStrS Γ A A= B B=) ≡ Γ
SumStr=S = //-elimP-Ctx (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → refl)))

SumStrSynCCat : CCatwithSum synCCat
CCatwithSum.SumStr SumStrSynCCat = SumStrS
CCatwithSum.SumStr= SumStrSynCCat = SumStr=S _ _ _ _ _
CCatwithSum.SumStrNat' SumStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B g₁ → refl)))))

{- sum -}

sumStrS-// : (i : ℕ) (Γ : DCtx n)
             (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : ∂₁S (proj a) ≡ UUStrS i (proj Γ))
             (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : ∂₁S (proj b) ≡ UUStrS i (proj Γ))
           → DMor n (suc n)
sumStrS-// i Γ a aₛ a₁ b bₛ b₁ = dmorTm Γ (uu i) UU (sum i (getTm a) (getTm b)) (SumUU (dTm refl a aₛ a₁) (dTm refl b bₛ b₁))


sumStrS-eq : (i : ℕ) {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ')
             {a a' : DMor n (suc n)} (ra : a ≃ a')
             (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a'))
             (a₁ : ∂₁S (proj a) ≡ UUStrS i (proj Γ)) (a'₁ : ∂₁S (proj a') ≡ UUStrS i (proj Γ'))
             {b b' : DMor n (suc n)} (rb : b ≃ b')
             (bₛ : S.is-section (proj b)) (b'ₛ : S.is-section (proj b'))
             (b₁ : ∂₁S (proj b) ≡ UUStrS i (proj Γ)) (b'₁ : ∂₁S (proj b') ≡ UUStrS i (proj Γ'))
           → sumStrS-// i Γ a aₛ a₁ b bₛ b₁ ≃ sumStrS-// i Γ' a' a'ₛ a'₁ b' b'ₛ b'₁
sumStrS-eq i rΓ ra aₛ a'ₛ a₁ a'₁ rb bₛ b'ₛ b₁ b'₁ =
                dmorTm= dmorTmₛ dmorTmₛ rΓ UUCong (SumUUCong (dTm= refl ra aₛ a'ₛ a₁ a'₁)
                                                             (dTm= refl rb bₛ b'ₛ b₁ b'₁))


sumStrS : (i : ℕ) (Γ : ObS n)
          (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ)
          (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i Γ)
        → MorS n (suc n)
sumStrS i = //-elim-Ctx (λ Γ → //-elim-Tm (λ a aₛ a₁ → //-elim-Tm (λ b bₛ b₁ → proj (sumStrS-// i Γ a aₛ a₁ b bₛ b₁))
                                                                  (λ rb bₛ b'ₛ b₁ b'₁ → proj= (sumStrS-eq i (ref Γ) (ref a) aₛ aₛ a₁ a₁ rb bₛ b'ₛ b₁ b'₁)))
                                          (λ ra aₛ a'ₛ a₁ a'₁ → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (sumStrS-eq i (ref Γ) ra aₛ a'ₛ a₁ a'₁ (ref b) bₛ bₛ b₁ b₁'))))
                        (λ rΓ → //-elimP-Tm (λ a aₛ a₁ a₁' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (sumStrS-eq i rΓ (ref a) aₛ aₛ a₁ a₁' (ref b) bₛ bₛ b₁ b₁'))))

sumStrₛS : (i : ℕ) (Γ : ObS n)
           (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ)
           (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i Γ)
         → S.is-section (sumStrS i Γ a aₛ a₁ b bₛ b₁)
sumStrₛS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → dmorTmₛ)))

sumStr₁S : (i : ℕ) (Γ : ObS n)
           (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ)
           (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i Γ)
         → ∂₁S (sumStrS i Γ a aₛ a₁ b bₛ b₁) ≡ UUStrS i Γ
sumStr₁S i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → refl)))

sumStrSynCCat : CCatwithsum synCCat UUStrSynCCat 
CCatwithsum.sumStr sumStrSynCCat = sumStrS
CCatwithsum.sumStrₛ sumStrSynCCat {Γ = Γ} {a = a} {b = b} = sumStrₛS _ Γ a _ _ b _ _
CCatwithsum.sumStr₁ sumStrSynCCat {Γ = Γ} {a = a} {b = b} = sumStr₁S _ Γ a _ _ b _ _
CCatwithsum.sumStrNat' sumStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ g₁ → refl)))))
        
{- inl -}

inlStrS-// : (Γ : DCtx n)
             (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ)
             (B : DCtx (suc n)) (B= : S.ft (proj B) ≡ proj Γ)
             (a : DMor n (suc n)) (aₛ : S.is-section (proj a)) (a₁ : S.∂₁ (proj a) ≡ proj A)
           → DMor n (suc n)
inlStrS-// Γ A A= B B= a aₛ a₁ = dmorTm Γ (sum (getTy A) (getTy B))
                                          (Sum (dTy A A=) (dTy B B=))
                                          (inl (getTy A) (getTy B) (getTm a))
                                          (Inl (dTy A A=) (dTy B B=) (dTm A= a aₛ a₁))

inlStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ')
             {A A' : DCtx (suc n)} (rA : A ≃ A')
             (A= : S.ft (proj A) ≡ proj Γ) (A'= : S.ft (proj A') ≡ proj Γ')
             {B B' : DCtx (suc n)} (rB : B ≃ B')
             (B= : S.ft (proj B) ≡ proj Γ) (B'= : S.ft (proj B') ≡ proj Γ')
             {a a' : DMor n (suc n)} (ra : a ≃ a')
             (aₛ : S.is-section (proj a)) (a'ₛ : S.is-section (proj a'))
             (a₁ : S.∂₁ (proj a) ≡ proj A) (a'₁ : S.∂₁ (proj a') ≡ proj A')
           → inlStrS-// Γ A A= B B= a aₛ a₁ ≃ inlStrS-// Γ' A' A'= B' B'= a' a'ₛ a'₁
inlStrS-eq rΓ rA A= A'= rB B= B'= ra aₛ a'ₛ a₁ a'₁ =
                   dmorTm= dmorTmₛ dmorTmₛ rΓ (SumCong (dTy= rA A=) (dTy= rB B=))
                                              (InlCong (dTy= rA A=) (dTy= rB B=) (dTm= A= ra aₛ a'ₛ a₁ a'₁))
                   
inlStrS : (Γ : ObS n)
          (A : ObS (suc n)) (A= : S.ft A ≡ Γ)
          (B : ObS (suc n)) (B= : S.ft B ≡ Γ)
          (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A)
        → MorS n (suc n)
inlStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → //-elim-Tm (λ a aₛ a₁ → proj (inlStrS-// Γ A A= B B= a aₛ a₁))
                                                                                  (λ ra aₛ a'ₛ a₁ a'₁ → proj= (inlStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= ra aₛ a'ₛ a₁ a'₁)))
                                                             (λ rB B= B'= → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (inlStrS-eq (ref Γ) (ref A) A= A= rB B= B'= (ref a) aₛ aₛ a₁ a₁'))))
                                        (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (inlStrS-eq (ref Γ) rA A= A'= (ref B) B= B=' (ref a) aₛ aₛ a₁ a₁')))))
                      (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ a aₛ a₁ a₁' → proj= (inlStrS-eq rΓ (ref A) A= A=' (ref B) B= B=' (ref a) aₛ aₛ a₁ a₁')))))

inlStrₛS : (Γ : ObS n)
           (A : ObS (suc n)) (A= : S.ft A ≡ Γ)
           (B : ObS (suc n)) (B= : S.ft B ≡ Γ)
           (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A)
         → S.is-section (inlStrS Γ A A= B B= a aₛ a₁)
inlStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ → dmorTmₛ))))

inlStr₁S : (Γ : ObS n)
           (A : ObS (suc n)) (A= : S.ft A ≡ Γ)
           (B : ObS (suc n)) (B= : S.ft B ≡ Γ)
           (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : S.∂₁ a ≡ A)
         → ∂₁S (inlStrS Γ A A= B B= a aₛ a₁) ≡ SumStrS Γ A A= B B=
inlStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ → refl))))

inlStrSynCCat : CCatwithinl synCCat SumStrSynCCat
CCatwithinl.inlStr inlStrSynCCat = inlStrS
CCatwithinl.inlStrₛ inlStrSynCCat {Γ = Γ} {A = A} {B = B} {a = a} = inlStrₛS Γ A _ B _ a _ _
CCatwithinl.inlStr₁ inlStrSynCCat {Γ = Γ} {A = A} {B = B} {a = a} = inlStr₁S Γ A _ B _ a _ _
CCatwithinl.inlStrNat' inlStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ a aₛ a₁ g₁ → up-to-rhsTyEq (ap-[]Ty refl (idMor[]Mor (mor g)))))))))


{- inr -}

inrStrS-// : (Γ : DCtx n)
             (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ)
             (B : DCtx (suc n)) (B= : S.ft (proj B) ≡ proj Γ)
             (b : DMor n (suc n)) (bₛ : S.is-section (proj b)) (b₁ : S.∂₁ (proj b) ≡ proj B)
           → DMor n (suc n)
inrStrS-// Γ A A= B B= b bₛ b₁ = dmorTm Γ (sum (getTy A) (getTy B))
                                          (Sum (dTy A A=) (dTy B B=))
                                          (inr (getTy A) (getTy B) (getTm b))
                                          (Inr (dTy A A=) (dTy B B=) (dTm B= b bₛ b₁))

inrStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ')
             {A A' : DCtx (suc n)} (rA : A ≃ A')
             (A= : S.ft (proj A) ≡ proj Γ) (A'= : S.ft (proj A') ≡ proj Γ')
             {B B' : DCtx (suc n)} (rB : B ≃ B')
             (B= : S.ft (proj B) ≡ proj Γ) (B'= : S.ft (proj B') ≡ proj Γ')
             {b b' : DMor n (suc n)} (rb : b ≃ b')
             (bₛ : S.is-section (proj b)) (b'ₛ : S.is-section (proj b'))
             (b₁ : S.∂₁ (proj b) ≡ proj B) (b'₁ : S.∂₁ (proj b') ≡ proj B')
           → inrStrS-// Γ A A= B B= b bₛ b₁ ≃ inrStrS-// Γ' A' A'= B' B'= b' b'ₛ b'₁
inrStrS-eq rΓ rA A= A'= rB B= B'= rb bₛ b'ₛ b₁ b'₁ =
                   dmorTm= dmorTmₛ dmorTmₛ rΓ (SumCong (dTy= rA A=) (dTy= rB B=))
                                              (InrCong (dTy= rA A=) (dTy= rB B=) (dTm= B= rb bₛ b'ₛ b₁ b'₁))
                   
inrStrS : (Γ : ObS n)
          (A : ObS (suc n)) (A= : S.ft A ≡ Γ)
          (B : ObS (suc n)) (B= : S.ft B ≡ Γ)
          (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ B)
        → MorS n (suc n)
inrStrS = //-elim-Ctx (λ Γ → //-elim-Ty (λ A A= → //-elim-Ty (λ B B= → //-elim-Tm (λ b bₛ b₁ → proj (inrStrS-// Γ A A= B B= b bₛ b₁))
                                                                                  (λ rb bₛ b'ₛ b₁ b'₁ → proj= (inrStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= rb bₛ b'ₛ b₁ b'₁)))
                                                             (λ rB B= B'= → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (inrStrS-eq (ref Γ) (ref A) A= A= rB B= B'= (ref b) bₛ bₛ b₁ b₁'))))
                                        (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (inrStrS-eq (ref Γ) rA A= A'= (ref B) B= B=' (ref b) bₛ bₛ b₁ b₁')))))
                      (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → //-elimP-Tm (λ b bₛ b₁ b₁' → proj= (inrStrS-eq rΓ (ref A) A= A=' (ref B) B= B=' (ref b) bₛ bₛ b₁ b₁')))))

inrStrₛS : (Γ : ObS n)
           (A : ObS (suc n)) (A= : S.ft A ≡ Γ)
           (B : ObS (suc n)) (B= : S.ft B ≡ Γ)
           (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ B)
         → S.is-section (inrStrS Γ A A= B B= b bₛ b₁)
inrStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ b bₛ b₁ → dmorTmₛ))))

inrStr₁S : (Γ : ObS n)
           (A : ObS (suc n)) (A= : S.ft A ≡ Γ)
           (B : ObS (suc n)) (B= : S.ft B ≡ Γ)
           (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : S.∂₁ b ≡ B)
         → ∂₁S (inrStrS Γ A A= B B= b bₛ b₁) ≡ SumStrS Γ A A= B B=
inrStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ b bₛ b₁ → refl))))

inrStrSynCCat : CCatwithinr synCCat SumStrSynCCat
CCatwithinr.inrStr inrStrSynCCat = inrStrS
CCatwithinr.inrStrₛ inrStrSynCCat {Γ = Γ} {A = A} {B = B} {b = b} = inrStrₛS Γ A _ B _ b _ _
CCatwithinr.inrStr₁ inrStrSynCCat {Γ = Γ} {A = A} {B = B} {b = b} = inrStr₁S Γ A _ B _ b _ _
CCatwithinr.inrStrNat' inrStrSynCCat = //-elimP (λ g → JforNat (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ b bₛ b₁ g₁ → up-to-rhsTyEq (ap-[]Ty refl (idMor[]Mor (mor g)))))))))

{- match -}
fixTyda : {A : TyExpr n} {B : TyExpr n} {C : TyExpr (suc n)} 
        → weakenTy' (prev last) C [ idMor (suc n) , inl (weakenTy A) (weakenTy B) (var last) ]Ty
          ≡ (C [ weakenMor (weakenMor (idMor n)) , var last ]Ty) [ idMor (suc n) , inl (A [ weakenMor (idMor n) ]Ty) (B [ weakenMor (idMor n) ]Ty) (var last) ]Ty
fixTyda = ap-[]Ty weakenTy+-to-[]Ty (Mor+= refl (ap-inl-Tm weakenTy-to-[]Ty weakenTy-to-[]Ty refl))

fixTydb : {A : TyExpr n} {B : TyExpr n} {C : TyExpr (suc n)} 
        → weakenTy' (prev last) C [ idMor (suc n) , inr (weakenTy A) (weakenTy B) (var last) ]Ty
          ≡ (C [ weakenMor (weakenMor (idMor n)) , var last ]Ty) [ idMor (suc n) , inr (A [ weakenMor (idMor n) ]Ty) (B [ weakenMor (idMor n) ]Ty) (var last) ]Ty
fixTydb = ap-[]Ty weakenTy+-to-[]Ty (Mor+= refl (ap-inr-Tm weakenTy-to-[]Ty weakenTy-to-[]Ty refl))

T-da₁S : (Γ : DCtx n)
         (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ)               
         (B : DCtx (suc n)) (B= : S.ft (proj B) ≡ proj Γ)
         (C : DCtx (suc (suc n))) (C= : S.ft (proj C) ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
       → DCtx (suc (suc n))
T-da₁S Γ A A= B B= C C= = dctx (der A , ConvTy (congTy fixTyda
                                                       (SubstTy (WeakTy (dTy C C=))
                                                                (idMor+ (der Γ , dTy A A=)
                                                                        (Inl (WeakTy (dTy A A=))
                                                                             (WeakTy (dTy B B=))
                                                                             (VarLast (dTy A A=))))))
                                               (CtxTy=Ctx A A=))
                                        
T-db₁S : (Γ : DCtx n)
         (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ)               
         (B : DCtx (suc n)) (B= : S.ft (proj B) ≡ proj Γ)
         (C : DCtx (suc (suc n))) (C= : S.ft (proj C) ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
       → DCtx (suc (suc n))
T-db₁S Γ A A= B B= C C= = dctx (der B , ConvTy (congTy fixTydb
                                                       (SubstTy (WeakTy (dTy C C=))
                                                                (idMor+ (der Γ , dTy B B=)
                                                                        (Inr (WeakTy (dTy A A=))
                                                                             (WeakTy (dTy B B=))
                                                                             (VarLast (dTy B B=))))))
                                               (CtxTy=Ctx B B=))
abstract
  reflectda₁ : (Γ : DCtx n)
               (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ)               
               (B : DCtx (suc n)) (B= : S.ft (proj B) ≡ proj Γ)
               (C : DCtx (suc (suc n))) (C= : S.ft (proj C) ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
               (da : DMor (suc n) (suc (suc n)))
               (da₁ : ∂₁S (proj da) ≡ CCatwithinl.T-da₁ inlStrSynCCat (proj Γ) (proj A) A= (proj B) B= (proj C) C=)
             → dctx (der (∂₁S-// da)) ≃ T-da₁S Γ A A= B B= C C=
  reflectda₁ Γ A A= B B= C C= da da₁ = reflect da₁ 
            
  reflectdb₁ : (Γ : DCtx n)
               (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ)               
               (B : DCtx (suc n)) (B= : S.ft (proj B) ≡ proj Γ)
               (C : DCtx (suc (suc n))) (C= : S.ft (proj C) ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
               (db : DMor (suc n) (suc (suc n)))
               (db₁ : ∂₁S (proj db) ≡ CCatwithinr.T-db₁ inrStrSynCCat (proj Γ) (proj A) A= (proj B) B= (proj C) C=)
             → dctx (der (∂₁S-// db)) ≃ T-db₁S Γ A A= B B= C C=
  reflectdb₁ Γ A A= B B= C C= db db₁ = reflect db₁ 
            

matchStrS-// : (Γ : DCtx n)
               (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ proj Γ)               
               (B : DCtx (suc n)) (B= : S.ft (proj B) ≡ proj Γ)
               (C : DCtx (suc (suc n))) (C= : S.ft (proj C) ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
               (da : DMor (suc n) (suc (suc n))) (daₛ : S.is-section (proj da))
               (da₁ : dctx (der (∂₁S-// da)) ≃ T-da₁S Γ A A= B B= C C=) {-∂₁S (proj da) ≡ CCatwithinl.T-da₁ inlStrSynCCat (proj Γ) (proj A) A= (proj B) B= (proj C) C=)-}
               (db : DMor (suc n) (suc (suc n))) (dbₛ : S.is-section (proj db))
               (db₁ : dctx (der (∂₁S-// db)) ≃ T-db₁S Γ A A= B B= C C=) {-∂₁S (proj db) ≡ CCatwithinr.T-db₁ inrStrSynCCat (proj Γ) (proj A) A= (proj B) B= (proj C) C=)-}
               (u : DMor n (suc n)) (uₛ : S.is-section (proj u)) (u₁ : S.∂₁ (proj u) ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
             → DMor n (suc n)
matchStrS-// Γ A A= B B= C C= da daₛ da₁ db dbₛ db₁ u uₛ u₁ = dmorTm Γ (substTy (getTy C) (getTm u)) (SubstTy (dTy C C=) (idMor+ (der Γ) (dTm refl u uₛ u₁))) (match (getTy A) (getTy B) (getTy C) (getTm da) (getTm db) (getTm u)) (Match (dTy A A=) (dTy B B=) (dTy C C=) dda ddb (dTm refl u uₛ u₁))
  where dda : Derivable ((ctx Γ , getTy A) ⊢ getTm da :> substTy (weakenTy' (prev last) (getTy C)) (inl (weakenTy (getTy A)) (weakenTy (getTy B)) (var last)))
        dda = congTmTy! fixTyda (dTm≃ (Ctx≃ft+Ty (reflect A=)) da daₛ da₁)
        ddb : Derivable ((ctx Γ , getTy B) ⊢ getTm db :> substTy (weakenTy' (prev last) (getTy C)) (inr (weakenTy (getTy A)) (weakenTy (getTy B)) (var last)))
        ddb = congTmTy! fixTydb (dTm≃ (Ctx≃ft+Ty (reflect B=)) db dbₛ db₁)

matchStrS-eq : {Γ Γ' : DCtx n} (rΓ : Γ ≃ Γ')
               {A A' : DCtx (suc n)} (rA : A ≃ A')
               (A= : S.ft (proj A) ≡ proj Γ) (A'= : S.ft (proj A') ≡ proj Γ')
               {B B' : DCtx (suc n)} (rB : B ≃ B')
               (B= : S.ft (proj B) ≡ proj Γ) (B'= : S.ft (proj B') ≡ proj Γ')
               {C C' : DCtx (suc (suc n))} (rC : C ≃ C')
               (C= : S.ft (proj C) ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
               (C'= : S.ft (proj C') ≡ SumStrS (proj Γ') (proj A') A'= (proj B') B'=)
               {da da' : DMor (suc n) (suc (suc n))} (rda : da ≃ da')
               (daₛ : S.is-section (proj da)) (da'ₛ : S.is-section (proj da'))
               (da₁ : dctx (der (∂₁S-// da)) ≃ T-da₁S Γ A A= B B= C C=) {-∂₁S (proj da) ≡ CCatwithinl.T-da₁ inlStrSynCCat (proj Γ) (proj A) A= (proj B) B= (proj C) C=)-}
               (da'₁ : dctx (der (∂₁S-// da')) ≃ T-da₁S Γ' A' A'= B' B'= C' C'=) {-∂₁S (proj da') ≡ CCatwithinl.T-da₁ inlStrSynCCat (proj Γ') (proj A') A'= (proj B') B'= (proj C') C'=)-}
               {db db' : DMor (suc n) (suc (suc n))} (rdb : db ≃ db')
               (dbₛ : S.is-section (proj db)) (db'ₛ : S.is-section (proj db'))
               (db₁ : dctx (der (∂₁S-// db)) ≃ T-db₁S Γ A A= B B= C C=) {-∂₁S (proj db) ≡ CCatwithinr.T-db₁ inrStrSynCCat (proj Γ) (proj A) A= (proj B) B= (proj C) C=)-}
               (db'₁ : dctx (der (∂₁S-// db')) ≃ T-db₁S Γ' A' A'= B' B'= C' C'=) {-∂₁S (proj db') ≡ CCatwithinr.T-db₁ inrStrSynCCat (proj Γ') (proj A') A'= (proj B') B'= (proj C') C'=)-}
               {u u' : DMor n (suc n)} (ru : u ≃ u')
               (uₛ : S.is-section (proj u)) (u'ₛ : S.is-section (proj u'))
               (u₁ : S.∂₁ (proj u) ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
               (u'₁ : S.∂₁ (proj u') ≡ SumStrS (proj Γ') (proj A') A'= (proj B') B'=)
             → matchStrS-// Γ A A= B B= C C= da daₛ da₁ db dbₛ db₁ u uₛ u₁ ≃ matchStrS-// Γ' A' A'= B' B'= C' C'= da' da'ₛ da'₁ db' db'ₛ db'₁ u' u'ₛ u'₁
matchStrS-eq {Γ = Γ} rΓ {A = A} rA A= A'= {B = B} rB B= B'= {C = C} rC C= C'= {da = da} {da' = da'} rda daₛ da'ₛ da₁ da'₁ {db = db} {db' = db'} rdb dbₛ db'ₛ db₁ db'₁ ru uₛ u'ₛ u₁ u'₁ =
             dmorTm= dmorTmₛ dmorTmₛ rΓ
                     (SubstTyFullEq' (der Γ) (der Γ , Sum (dTy A A=) (dTy B B=)) (dTy= rC C=) (idMor+= (der Γ) (dTm= refl ru uₛ u'ₛ u₁ u'₁)))
                     (MatchCong (dTy= rA A=) (dTy= rB B=) (dTy= rC C=) (dTy A A=) dda= (dTy B B=) ddb= (dTm= refl ru uₛ u'ₛ u₁ u'₁))
  where dda= : Derivable ((ctx Γ , getTy A) ⊢ getTm da == getTm da' :> substTy (weakenTy' (prev last) (getTy C)) (inl (weakenTy (getTy A)) (weakenTy (getTy B)) (var last)))
        dda= = congTmEqTy! fixTyda (dTm=≃ (Ctx≃ft+Ty (reflect A=)) rda daₛ da'ₛ da₁ da'₁)
        ddb= : Derivable ((ctx Γ , getTy B) ⊢ getTm db == getTm db' :> substTy (weakenTy' (prev last) (getTy C)) (inr (weakenTy (getTy A)) (weakenTy (getTy B)) (var last)))
        ddb= = congTmEqTy! fixTydb (dTm=≃ (Ctx≃ft+Ty (reflect B=)) rdb dbₛ db'ₛ db₁ db'₁)



matchStrS1 : (Γ : DCtx n)
             (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ (proj Γ))               
             (B : DCtx (suc n)) (B= : S.ft (proj B) ≡ (proj Γ))
             (C : DCtx (suc (suc n))) (C= : S.ft (proj C) ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
             (da : DMor (suc n) (suc (suc n))) (daₛ : S.is-section (proj da))
             (da₁ : ∂₁S (proj da) ≡ CCatwithinl.T-da₁ inlStrSynCCat (proj Γ) (proj A) A= (proj B) B= (proj C) C=)
             (db : DMor (suc n) (suc (suc n))) (dbₛ : S.is-section (proj db))
             (db₁ : ∂₁S (proj db) ≡ CCatwithinr.T-db₁ inrStrSynCCat (proj Γ) (proj A) A= (proj B) B= (proj C) C=)
             (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
           → MorS n (suc n)
matchStrS1 Γ A A= B B= C C= da daₛ da₁ db dbₛ db₁ = //-elim-Tm (λ u uₛ u₁ → proj (matchStrS-// Γ A A= B B= C C= da daₛ (reflectda₁ Γ A A= B B= C C= da da₁) db dbₛ (reflectdb₁ Γ A A= B B= C C= db db₁) u uₛ u₁))
                                                               (λ ru uₛ u'ₛ u₁ u'₁ → proj= (matchStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= (ref C) C= C= (ref da) daₛ daₛ (reflectda₁ Γ A A= B B= C C= da da₁) (reflectda₁ Γ A A= B B= C C= da da₁) (ref db) dbₛ dbₛ (reflectdb₁ Γ A A= B B= C C= db db₁) (reflectdb₁ Γ A A= B B= C C= db db₁) ru uₛ u'ₛ u₁ u'₁))

matchStrS2 : (Γ : DCtx n)
             (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ (proj Γ))               
             (B : DCtx (suc n)) (B= : S.ft (proj B) ≡ (proj Γ))
             (C : DCtx (suc (suc n))) (C= : S.ft (proj C) ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
             (da : DMor (suc n) (suc (suc n))) (daₛ : S.is-section (proj da))
             (da₁ : ∂₁S (proj da) ≡ CCatwithinl.T-da₁ inlStrSynCCat (proj Γ) (proj A) A= (proj B) B= (proj C) C=)
             (db : MorS (suc n) (suc (suc n))) (dbₛ : S.is-section db)
             (db₁ : ∂₁S db ≡ CCatwithinr.T-db₁ inrStrSynCCat (proj Γ) (proj A) A= (proj B) B= (proj C) C=)
             (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
           → MorS n (suc n)
matchStrS2 Γ A A= B B= C C= da daₛ da₁ = //-elim-Tm (λ db dbₛ db₁ → matchStrS1 Γ A A= B B= C C= da daₛ da₁ db dbₛ db₁)
                                                    (λ {db} {db'} rdb dbₛ db'ₛ db₁ db'₁ → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (matchStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= (ref C) C= C= (ref da) daₛ daₛ (reflectda₁ Γ A A= B B= C C= da da₁) (reflectda₁ Γ A A= B B= C C= da da₁) rdb dbₛ db'ₛ (reflectdb₁ Γ A A= B B= C C= db db₁) (reflectdb₁ Γ A A= B B= C C= db' db'₁) (ref u) uₛ uₛ u₁ u₁')))


matchStrS3 : (Γ : DCtx n)
             (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ (proj Γ))               
             (B : DCtx (suc n)) (B= : S.ft (proj B) ≡ (proj Γ))
             (C : DCtx (suc (suc n))) (C= : S.ft (proj C) ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
             (da : MorS (suc n) (suc (suc n))) (daₛ : S.is-section da)
             (da₁ : ∂₁S da ≡ CCatwithinl.T-da₁ inlStrSynCCat (proj Γ) (proj A) A= (proj B) B= (proj C) C=)
             (db : MorS (suc n) (suc (suc n))) (dbₛ : S.is-section db)
             (db₁ : ∂₁S db ≡ CCatwithinr.T-db₁ inrStrSynCCat (proj Γ) (proj A) A= (proj B) B= (proj C) C=)
             (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
           → MorS n (suc n)
matchStrS3 Γ A A= B B= C C= = //-elim-Tm (λ da daₛ da₁ → matchStrS2 Γ A A= B B= C C= da daₛ da₁)
                                         (λ {da} {da'} rda daₛ da'ₛ da₁ da'₁ → //-elimP-Tm (λ db dbₛ db₁ db₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (matchStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= (ref C) C= C= rda daₛ da'ₛ (reflectda₁ Γ A A= B B= C C= da da₁)(reflectda₁ Γ A A= B B= C C= da' da'₁) (ref db) dbₛ dbₛ (reflectdb₁ Γ A A= B B= C C= db db₁) (reflectdb₁ Γ A A= B B= C C= db db₁') (ref u) uₛ uₛ u₁ u₁'))))

matchStrS4 : (Γ : DCtx n)
             (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ (proj Γ))               
             (B : DCtx (suc n)) (B= : S.ft (proj B) ≡ (proj Γ))
             (C : ObS (suc (suc n))) (C= : S.ft C ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
             (da : MorS (suc n) (suc (suc n))) (daₛ : S.is-section da)
             (da₁ : ∂₁S da ≡ CCatwithinl.T-da₁ inlStrSynCCat (proj Γ) (proj A) A= (proj B) B= C C=)
             (db : MorS (suc n) (suc (suc n))) (dbₛ : S.is-section db)
             (db₁ : ∂₁S db ≡ CCatwithinr.T-db₁ inrStrSynCCat (proj Γ) (proj A) A= (proj B) B= C C=)
             (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ SumStrS (proj Γ) (proj A) A= (proj B) B=)
           → MorS n (suc n)
matchStrS4 Γ A A= B B= = //-elim-Ty (λ C C= → matchStrS3 Γ A A= B B= C C=)
                                    (λ {C} {C'} rC C= C'= → //-elimP-Tm (λ da daₛ da₁ da₁' → //-elimP-Tm (λ db dbₛ db₁ db₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (matchStrS-eq (ref Γ) (ref A) A= A= (ref B) B= B= rC C= C'= (ref da) daₛ daₛ (reflect da₁) (reflect da₁') (ref db) dbₛ dbₛ (reflect db₁) (reflect db₁') (ref u) uₛ uₛ u₁ u₁')))))

matchStrS5 : (Γ : DCtx n)
             (A : DCtx (suc n)) (A= : S.ft (proj A) ≡ (proj Γ))               
             (B : ObS (suc n)) (B= : S.ft B ≡ (proj Γ))
             (C : ObS (suc (suc n))) (C= : S.ft C ≡ SumStrS (proj Γ) (proj A) A= B B=)
             (da : MorS (suc n) (suc (suc n))) (daₛ : S.is-section da)
             (da₁ : ∂₁S da ≡ CCatwithinl.T-da₁ inlStrSynCCat (proj Γ) (proj A) A= B B= C C=)
             (db : MorS (suc n) (suc (suc n))) (dbₛ : S.is-section db)
             (db₁ : ∂₁S db ≡ CCatwithinr.T-db₁ inrStrSynCCat (proj Γ) (proj A) A= B B= C C=)
             (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ SumStrS (proj Γ) (proj A) A= B B=)
           → MorS n (suc n)
matchStrS5 Γ A A= = //-elim-Ty (λ B B= → matchStrS4 Γ A A= B B=)
                               (λ rB B= B'= → //-elimP-Ty (λ C C= C=' → //-elimP-Tm (λ da daₛ da₁ da₁' → //-elimP-Tm (λ db dbₛ db₁ db₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (matchStrS-eq (ref Γ) (ref A) A= A= rB B= B'= (ref C) C= C=' (ref da) daₛ daₛ (reflect da₁) (reflect da₁') (ref db) dbₛ dbₛ (reflect db₁) (reflect db₁') (ref u) uₛ uₛ u₁ u₁'))))))

matchStrS6 : (Γ : DCtx n)
             (A : ObS (suc n)) (A= : S.ft A ≡ (proj Γ))               
             (B : ObS (suc n)) (B= : S.ft B ≡ (proj Γ))
             (C : ObS (suc (suc n))) (C= : S.ft C ≡ SumStrS (proj Γ) A A= B B=)
             (da : MorS (suc n) (suc (suc n))) (daₛ : S.is-section da)
             (da₁ : ∂₁S da ≡ CCatwithinl.T-da₁ inlStrSynCCat (proj Γ) A A= B B= C C=)
             (db : MorS (suc n) (suc (suc n))) (dbₛ : S.is-section db)
             (db₁ : ∂₁S db ≡ CCatwithinr.T-db₁ inrStrSynCCat (proj Γ) A A= B B= C C=)
             (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ SumStrS (proj Γ) A A= B B=)
           → MorS n (suc n)
matchStrS6 Γ = //-elim-Ty (λ A A= → matchStrS5 Γ A A=)
                          (λ rA A= A'= → //-elimP-Ty (λ B B= B=' → //-elimP-Ty (λ C C= C=' → //-elimP-Tm (λ da daₛ da₁ da₁' → //-elimP-Tm (λ db dbₛ db₁ db₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (matchStrS-eq (ref Γ) rA A= A'= (ref B) B= B=' (ref C) C= C=' (ref da) daₛ daₛ (reflect da₁) (reflect da₁') (ref db) dbₛ dbₛ (reflect db₁) (reflect db₁') (ref u) uₛ uₛ u₁ u₁')))))))

matchStrS : (Γ : ObS n)
            (A : ObS (suc n)) (A= : S.ft A ≡ Γ)               
            (B : ObS (suc n)) (B= : S.ft B ≡ Γ)
            (C : ObS (suc (suc n))) (C= : S.ft C ≡ SumStrS Γ A A= B B=)
            (da : MorS (suc n) (suc (suc n))) (daₛ : S.is-section da)
            (da₁ : ∂₁S da ≡ CCatwithinl.T-da₁ inlStrSynCCat Γ A A= B B= C C=)
            (db : MorS (suc n) (suc (suc n))) (dbₛ : S.is-section db)
            (db₁ : ∂₁S db ≡ CCatwithinr.T-db₁ inrStrSynCCat Γ A A= B B= C C=)
            (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ SumStrS Γ A A= B B=)
          → MorS n (suc n)
matchStrS = //-elim-Ctx (λ Γ → matchStrS6 Γ)
                        (λ rΓ → //-elimP-Ty (λ A A= A=' → //-elimP-Ty (λ B B= B=' → //-elimP-Ty (λ C C= C=' → //-elimP-Tm (λ da daₛ da₁ da₁' → //-elimP-Tm (λ db dbₛ db₁ db₁' → //-elimP-Tm (λ u uₛ u₁ u₁' → proj= (matchStrS-eq rΓ (ref A) A= A=' (ref B) B= B=' (ref C) C= C=' (ref da) daₛ daₛ (reflect da₁) (reflect da₁') (ref db) dbₛ dbₛ (reflect db₁) (reflect db₁') (ref u) uₛ uₛ u₁ u₁'))))))))


matchStrₛS : (Γ : ObS n)
             (A : ObS (suc n)) (A= : S.ft A ≡ Γ)               
             (B : ObS (suc n)) (B= : S.ft B ≡ Γ)
             (C : ObS (suc (suc n))) (C= : S.ft C ≡ SumStrS Γ A A= B B=)
             (da : MorS (suc n) (suc (suc n))) (daₛ : S.is-section da)
             (da₁ : ∂₁S da ≡ CCatwithinl.T-da₁ inlStrSynCCat Γ A A= B B= C C=)
             (db : MorS (suc n) (suc (suc n))) (dbₛ : S.is-section db)
             (db₁ : ∂₁S db ≡ CCatwithinr.T-db₁ inrStrSynCCat Γ A A= B B= C C=)
             (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ SumStrS Γ A A= B B=)
           → S.is-section (matchStrS Γ A A= B B= C C= da daₛ da₁ db dbₛ db₁ u uₛ u₁)
matchStrₛS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ C C= → //-elimP (λ da daₛ da₁ → //-elimP (λ db dbₛ db₁ → //-elimP (λ u uₛ u₁ → dmorTmₛ)))))))

matchStr₁S : (Γ : ObS n)
             (A : ObS (suc n)) (A= : S.ft A ≡ Γ)               
             (B : ObS (suc n)) (B= : S.ft B ≡ Γ)
             (C : ObS (suc (suc n))) (C= : S.ft C ≡ SumStrS Γ A A= B B=)
             (da : MorS (suc n) (suc (suc n))) (daₛ : S.is-section da)
             (da₁ : ∂₁S da ≡ CCatwithinl.T-da₁ inlStrSynCCat Γ A A= B B= C C=)
             (db : MorS (suc n) (suc (suc n))) (dbₛ : S.is-section db)
             (db₁ : ∂₁S db ≡ CCatwithinr.T-db₁ inrStrSynCCat Γ A A= B B= C C=)
             (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : S.∂₁ u ≡ SumStrS Γ A A= B B=)
           → S.∂₁ (matchStrS Γ A A= B B= C C= da daₛ da₁ db dbₛ db₁ u uₛ u₁) ≡ S.star u C C= u₁
matchStr₁S = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ C C= → //-elimP (λ da daₛ da₁ → //-elimP (λ db dbₛ db₁ → //-elimP (λ u uₛ u₁ →
                                      (eq (box ((reflectOb (!(S.is-section₀ uₛ u₁))
                                               , SubstTyMorEq' (der Γ) (der Γ , Sum (dTy A A=) (dTy B B=)) (dTy C C=)
                                                                (MorSymm (der Γ) (der Γ , Sum (dTy A A=) (dTy B B=)) (morTm=idMorTm refl u uₛ u₁)))))))))))))


matchStrSynCCat : CCatwithmatch synCCat SumStrSynCCat inlStrSynCCat inrStrSynCCat
CCatwithmatch.matchStr matchStrSynCCat = matchStrS
CCatwithmatch.matchStrₛ matchStrSynCCat {Γ = Γ} {A = A} {B = B} {C = C} {da = da} {db = db} {u = u} = matchStrₛS Γ A _ B _ C _ da _ _ db _ _ u _ _
CCatwithmatch.matchStr₁ matchStrSynCCat {Γ = Γ} {A = A} {B = B} {C = C} {da = da} {db = db} {u = u} = matchStr₁S Γ A _ B _ C _ da _ _ db _ _ u _ _
CCatwithmatch.matchStrNat' matchStrSynCCat = //-elimP (λ g → //-elimP (λ Δ g₀ → (//-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ C C= → //-elimP (λ da daₛ da₁ → //-elimP (λ db dbₛ db₁ → //-elimP (λ u uₛ u₁ g₁ → up-to-rhsTyEq' (reflectOb g₀) (ap-[]Ty refl (idMor[]Mor (mor g)) ∙ []Ty-substTy)))))))))))

{- ElSum= -}

elsumStrS : (i : ℕ) (Γ : ObS n)
            (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ UUStrS i Γ)
            (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ UUStrS i Γ)
          → ElStrS i Γ (sumStrS i Γ a aₛ a₁ b bₛ b₁) (sumStrₛS i Γ a aₛ a₁ b bₛ b₁) (sumStr₁S i Γ a aₛ a₁ b bₛ b₁) ≡ SumStrS Γ (ElStrS i Γ a aₛ a₁) (ElStr=S i Γ a aₛ a₁) (ElStrS i Γ b bₛ b₁) (ElStr=S i Γ b bₛ b₁)
elsumStrS i = //-elimP (λ Γ → //-elimP (λ a aₛ a₁ → //-elimP (λ b bₛ b₁ → eq (box (CtxRefl (der Γ) , ElSum= (dTm refl a aₛ a₁) (dTm refl b bₛ b₁))))))

{- BetaInl -}

betaInlStrS : (Γ : ObS n)
              (A : ObS (suc n)) (A= : S.ft A ≡ Γ)               
              (B : ObS (suc n)) (B= : S.ft B ≡ Γ)
              (C : ObS (suc (suc n))) (C= : S.ft C ≡ SumStrS Γ A A= B B=)
              (da : MorS (suc n) (suc (suc n))) (daₛ : S.is-section da)
              (da₁ : ∂₁S da ≡ CCatwithinl.T-da₁ inlStrSynCCat Γ A A= B B= C C=)
              (db : MorS (suc n) (suc (suc n))) (dbₛ : S.is-section db)
              (db₁ : ∂₁S db ≡ CCatwithinr.T-db₁ inrStrSynCCat Γ A A= B B= C C=)
              (a : MorS n (suc n)) (aₛ : S.is-section a) (a₁ : ∂₁S a ≡ A)
            → matchStrS Γ A A= B B= C C= da daₛ da₁ db dbₛ db₁ (inlStrS Γ A A= B B= a aₛ a₁) (inlStrₛS Γ A A= B B= a aₛ a₁) (inlStr₁S Γ A A= B B= a aₛ a₁) ≡ S.starTm a da (S.is-section₀ daₛ da₁ ∙ CCatwithinl.T-da₁= inlStrSynCCat) a₁
betaInlStrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ C C= → //-elimP (λ da daₛ da₁ → //-elimP (λ db dbₛ db₁ → //-elimP (λ a aₛ a₁ →
                       let dda = congTmTy! fixTyda (dTm≃ (Ctx≃ft+Ty (reflect A=)) da daₛ (reflectda₁ Γ A A= B B= C C= da da₁))
                           ddb = congTmTy! fixTydb (dTm≃ (Ctx≃ft+Ty (reflect B=)) db dbₛ (reflectdb₁ Γ A A= B B= C C= db db₁))
                       in up-to-rhsTyEq2' (reflectOb (! (S.is-section₀ aₛ a₁ ∙ A=)))
                                          (congTyEq (ap-[]Ty ([idMor]Ty _ ∙ ! fixTyda) refl
                                                    ∙ []Ty-assoc _ _ _
                                                    ∙ ap-[]Ty refl (Mor+= (Mor+= (weakenMorInsert _ _ _ ∙ [idMor]Mor _) refl) (ap-inl-Tm substTy-weakenTy substTy-weakenTy refl))
                                                    ∙ weakenTyInsert' _ _ _ _)
                                                    ([]Ty-assoc _ _ _)
                                                    (SubstTyFullEq' (der Γ) (der Γ , dTy A A=)
                                                                    (SubstTyFullEq' (der Γ , dTy A A=) (der Γ , dTy A A=)
                                                                                    (dTy=≃ (sym (reflectda₁ Γ A A= B B= C C= da da₁)) (Ctx≃ft+Ty (reflect A=)))
                                                                                    (MorSymm (der Γ , dTy A A=) (der Γ , dTy A A=)
                                                                                             (getMor=idMor≃ (Ctx≃ft+Ty (reflect A=)) da daₛ (reflectda₁ Γ A A= B B= C C= da da₁))))
                                                    (MorSymm (der Γ) (der Γ , dTy A A=)
                                                             (morTm=idMorTm A= a aₛ a₁))))
                                          (TmTran' (der Γ) (BetaInl (dTy A A=) (dTy B B=) (dTy C C=) dda ddb  (dTm A= a aₛ a₁))
                                                           (congTmEqTy ([]Ty-substTy ∙ ap-substTy (weakenTyInsert' _ _ _ _ ∙ [idMor]Ty _) (ap-inl-Tm substTy-weakenTy substTy-weakenTy refl))
                                                                       (SubstTmMorEq' (der Γ) (der Γ , dTy A A=) dda
                                                                                      (MorSymm (der Γ) (der Γ , dTy A A=) (morTm=idMorTm A= a aₛ a₁))) )))))))))

{- BetaInr -}

betaInrStrS : (Γ : ObS n)
              (A : ObS (suc n)) (A= : S.ft A ≡ Γ)               
              (B : ObS (suc n)) (B= : S.ft B ≡ Γ)
              (C : ObS (suc (suc n))) (C= : S.ft C ≡ SumStrS Γ A A= B B=)
              (da : MorS (suc n) (suc (suc n))) (daₛ : S.is-section da)
              (da₁ : ∂₁S da ≡ CCatwithinl.T-da₁ inlStrSynCCat Γ A A= B B= C C=)
              (db : MorS (suc n) (suc (suc n))) (dbₛ : S.is-section db)
              (db₁ : ∂₁S db ≡ CCatwithinr.T-db₁ inrStrSynCCat Γ A A= B B= C C=)
              (b : MorS n (suc n)) (bₛ : S.is-section b) (b₁ : ∂₁S b ≡ B)
            → matchStrS Γ A A= B B= C C= da daₛ da₁ db dbₛ db₁ (inrStrS Γ A A= B B= b bₛ b₁) (inrStrₛS Γ A A= B B= b bₛ b₁) (inrStr₁S Γ A A= B B= b bₛ b₁) ≡ S.starTm b db (S.is-section₀ dbₛ db₁ ∙ CCatwithinr.T-db₁= inrStrSynCCat) b₁
betaInrStrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ C C= → //-elimP (λ da daₛ da₁ → //-elimP (λ db dbₛ db₁ → //-elimP (λ b bₛ b₁ →
                       let dda = congTmTy! fixTyda (dTm≃ (Ctx≃ft+Ty (reflect A=)) da daₛ (reflectda₁ Γ A A= B B= C C= da da₁))
                           ddb = congTmTy! fixTydb (dTm≃ (Ctx≃ft+Ty (reflect B=)) db dbₛ (reflectdb₁ Γ A A= B B= C C= db db₁))
                       in up-to-rhsTyEq2' (reflectOb (! (S.is-section₀ bₛ b₁ ∙ B=)))
                                          (congTyEq (ap-[]Ty ([idMor]Ty _ ∙ ! fixTydb) refl
                                                    ∙ []Ty-assoc _ _ _
                                                    ∙ ap-[]Ty refl (Mor+= (Mor+= (weakenMorInsert _ _ _ ∙ [idMor]Mor _) refl) (ap-inr-Tm substTy-weakenTy substTy-weakenTy refl))
                                                    ∙ weakenTyInsert' _ _ _ _)
                                                    ([]Ty-assoc _ _ _)
                                                    (SubstTyFullEq' (der Γ) (der Γ , dTy B B=)
                                                                    (SubstTyFullEq' (der Γ , dTy B B=) (der Γ , dTy B B=)
                                                                                    (dTy=≃ (sym (reflectdb₁ Γ A A= B B= C C= db db₁)) (Ctx≃ft+Ty (reflect B=)))
                                                                                    (MorSymm (der Γ , dTy B B=) (der Γ , dTy B B=)
                                                                                             (getMor=idMor≃ (Ctx≃ft+Ty (reflect B=)) db dbₛ (reflectdb₁ Γ A A= B B= C C= db db₁))))
                                                    (MorSymm (der Γ) (der Γ , dTy B B=)
                                                             (morTm=idMorTm B= b bₛ b₁))))
                                          (TmTran' (der Γ) (BetaInr (dTy A A=) (dTy B B=) (dTy C C=) dda ddb (dTm B= b bₛ b₁))
                                                           (congTmEqTy ([]Ty-substTy ∙ ap-substTy (weakenTyInsert' _ _ _ _ ∙ [idMor]Ty _) (ap-inr-Tm substTy-weakenTy substTy-weakenTy refl))
                                                                       (SubstTmMorEq' (der Γ) (der Γ , dTy B B=) ddb
                                                                                      (MorSymm (der Γ) (der Γ , dTy B B=) (morTm=idMorTm B= b bₛ b₁))) )))))))))

{- EtaSum -}

etaSumStrS : (Γ : ObS n) (A : ObS (suc n)) (A= : ftS A ≡ Γ) (B : ObS (suc n)) (B= : ftS B ≡ Γ) (u : MorS n (suc n)) (uₛ : S.is-section u) (u₁ : ∂₁S u ≡ SumStrS Γ A A= B B=)
           → u ≡ CCatwithmatch.T-rhsEtaSum matchStrSynCCat Γ A A= B B= u uₛ u₁
etaSumStrS = //-elimP (λ Γ → //-elimP (λ A A= → //-elimP (λ B B= → //-elimP (λ u uₛ u₁ →
                      eq (box (reflectOb (S.is-section₀ uₛ u₁))
                              (congCtxEq refl (Ctx+= refl (ap-sum-Ty (! ([]Ty-assoc _ _ _ ∙ ap-[]Ty refl (weakenMorInsert _ _ _ ∙ [idMor]Mor _) ∙ [idMor]Ty _))
                                                                     (! ([]Ty-assoc _ _ _ ∙ ap-[]Ty refl (weakenMorInsert _ _ _ ∙ [idMor]Mor _) ∙ [idMor]Ty _))))
                                              (reflectOb u₁))
                              (ConvMorEq (MorTran (der Γ) (der Γ , Sum (dTy A A=) (dTy B B=))
                                                  (morTm=idMorTm refl u uₛ u₁)
                                                  (idMor+= (der Γ) (congTmEq refl (ap-match-Tm refl refl (ap-sum-Ty weakenTy-to-[]Ty weakenTy-to-[]Ty)
                                                                                                         (ap-inl-Tm weakenTy-to-[]Ty weakenTy-to-[]Ty refl)
                                                                                                         (ap-inr-Tm weakenTy-to-[]Ty weakenTy-to-[]Ty refl) refl)
                                                                             refl (EtaSum (dTy A A=) (dTy B B=) (dTm refl u uₛ u₁)))))
                                         (reflectOb (! (S.is-section₀ uₛ u₁)))
                                         (reflectOb (! u₁))))))))

