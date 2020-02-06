{-# OPTIONS --rewriting --prop #-}

open import common
open import typetheory
open import syntx
open import rules
open import contextualcat

module _ (sC : StructuredCCat) where

open StructuredCCat sC
open CCat+ ccat renaming (Mor to MorC; id to idC)

open import partialinterpretation sC
open import interpretationweakening sC
open import interpretationsubstitution sC

{-
In this file we prove that the partial interpretation functions are total when applied to derivable
judgments.
-}


{- Totality of the partial interpretation functions -}

⟦⟧Tyᵈ  : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) → isDefined (⟦ A ⟧Ty (⟦ Γ ⟧Ctx $ Γᵈ))
⟦⟧Tmᵈ  : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → isDefined (⟦ u ⟧Tm (⟦ Γ ⟧Ctx $ Γᵈ))

{- Codomain of the interpretation of a derivable term -}

⟦⟧Tm₁ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {u : TmExpr n} {uᵈ : isDefined (⟦ u ⟧Tm X)} {A : TyExpr n} {Aᵈ : isDefined (⟦ A ⟧Ty X)} (du : Derivable (Γ ⊢ u :> A)) → ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ ⟦ A ⟧Ty X $ Aᵈ

{- Interpretation of definitional equalities -}

⟦⟧TyEq : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A')) {Aᵈ : isDefined (⟦ A ⟧Ty X)} {A'ᵈ : isDefined (⟦ A' ⟧Ty X)}
       → ⟦ A ⟧Ty X $ Aᵈ ≡ ⟦ A' ⟧Ty X $ A'ᵈ
⟦⟧TmEq : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A)) {uᵈ : isDefined (⟦ u ⟧Tm X)} {u'ᵈ : isDefined (⟦ u' ⟧Tm X)}
       → ⟦ u ⟧Tm X $ uᵈ ≡ ⟦ u' ⟧Tm X $ u'ᵈ


{- Proof of totality -}

⟦⟧Tyᵈ Γᵈ UU = tt
⟦⟧Tyᵈ Γᵈ {A = el i v} (El dv) =
  (⟦⟧Tmᵈ Γᵈ dv ,
   ⟦⟧Tmₛ v ,
   ⟦⟧Tm₁ Γᵈ dv , tt)
⟦⟧Tyᵈ Γᵈ {A = sum A B} (Sum dA dB) =
  (⟦⟧Tyᵈ Γᵈ dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ Γᵈ dB ,
   ⟦⟧Ty-ft B , tt)
⟦⟧Tyᵈ Γᵈ {A = pi A B} (Pi dA dB) =
  (Aᵈ ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB ,
   ⟦⟧Ty-ft B , tt)
  where Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
⟦⟧Tyᵈ Γᵈ {A = sig A B} (Sig dA dB) =
  (Aᵈ ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB ,
   ⟦⟧Ty-ft B , tt)
  where
    Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
⟦⟧Tyᵈ Γᵈ Empty = tt
⟦⟧Tyᵈ Γᵈ Unit = tt
⟦⟧Tyᵈ Γᵈ Nat = tt
⟦⟧Tyᵈ Γᵈ {A = id A a b} (Id dA da db) =
  (⟦⟧Tyᵈ Γᵈ dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da ,
   ⟦⟧Tmᵈ Γᵈ db ,
   ⟦⟧Tmₛ b ,
   ⟦⟧Tm₁ Γᵈ db , tt)

⟦⟧Tmᵈ Γᵈ (Var _ _) = tt
⟦⟧Tmᵈ Γᵈ (Conv dA du dA=) = ⟦⟧Tmᵈ Γᵈ du

⟦⟧Tmᵈ Γᵈ {u = uu i} UUUU = tt

⟦⟧Tmᵈ Γᵈ {u = sum i a b} (SumUU da db) =
  (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)
    where
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da
      bᵈ = ⟦⟧Tmᵈ Γᵈ db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ Γᵈ db
⟦⟧Tmᵈ Γᵈ {u = inl A B a} (Inl dA dB da) =
   (Aᵈ , ⟦⟧Ty-ft A , Bᵈ , ⟦⟧Ty-ft B , aᵈ , aₛ , a₁ , tt)
     where
       Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
       Bᵈ = ⟦⟧Tyᵈ Γᵈ dB
       aᵈ = ⟦⟧Tmᵈ Γᵈ da
       aₛ = ⟦⟧Tmₛ a
       a₁ = ⟦⟧Tm₁ Γᵈ da
⟦⟧Tmᵈ Γᵈ {u = inr A B b} (Inr dA dB db) =
   (Aᵈ , ⟦⟧Ty-ft A , Bᵈ , ⟦⟧Ty-ft B , bᵈ , bₛ , b₁ , tt)
     where
       Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
       Bᵈ = ⟦⟧Tyᵈ Γᵈ dB
       bᵈ = ⟦⟧Tmᵈ Γᵈ db
       bₛ = ⟦⟧Tmₛ b
       b₁ = ⟦⟧Tm₁ Γᵈ db
⟦⟧Tmᵈ {Γ = Γ} Γᵈ {u = match A B C da db u} (Match dA dB dC dda ddb du) =
  (Aᵈ , A= , Bᵈ , B= , Cᵈ , C= , daᵈ , daₛ , da₁ , dbᵈ , dbₛ , db₁ , uᵈ , uₛ , u₁ , tt)
    where
      [Γ] = ⟦ Γ ⟧Ctx $ Γᵈ

      Aᵈ : isDefined (⟦ A ⟧Ty [Γ])
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      [A] = ⟦ A ⟧Ty [Γ] $ Aᵈ
      A= = ⟦⟧Ty-ft A

      Bᵈ : isDefined (⟦ B ⟧Ty [Γ])
      Bᵈ = ⟦⟧Tyᵈ Γᵈ dB
      [B] = ⟦ B ⟧Ty [Γ] $ Bᵈ
      B= = ⟦⟧Ty-ft B

      SumABᵈ : isDefined (⟦ sum  A B ⟧Ty [Γ])
      SumABᵈ = (Aᵈ , ⟦⟧Ty-ft A , Bᵈ , ⟦⟧Ty-ft B , tt)
      [SumAB] = ⟦ sum A B ⟧Ty [Γ] $ SumABᵈ
      SumAB-ft = ⟦⟧Ty-ft (sum A B) {Aᵈ = SumABᵈ}

      Cᵈ : isDefined (⟦ C ⟧Ty [SumAB])
      Cᵈ = ⟦⟧Tyᵈ (Γᵈ , SumABᵈ , tt) dC
      [C] = ⟦ C ⟧Ty [SumAB] $ Cᵈ
      C= = ⟦⟧Ty-ft C {Aᵈ = Cᵈ}

      daᵈ = ⟦⟧Tmᵈ (Γᵈ , Aᵈ , tt) dda
      daₛ = ⟦⟧Tmₛ da
      da₁ = ⟦⟧Tm₁ (Γᵈ , Aᵈ , tt) dda ∙ substAwCinla=
          where substAwCinla= : ⟦ substTy (weakenTy' (prev last) C) (inl (weakenTy A) (weakenTy B) (var last)) ⟧Ty  [A] $ _
                              ≡ T-da₁ _ [A] A= [B] B= [C] C=
                substAwCinla= = ⟦subst⟧Ty= (weakenTy' (prev last) C)
                                           AwCᵈ
                                           (inl (weakenTy A) (weakenTy B) (var last))
                                           inlwAwBlastᵈ
                                           inlwAwBlast₁
                                ∙ ! (ap-irr-star (ap-irr-inlStr refl AwA= AwB= refl) AwC=) 
                              where AwSumABᵈ : isDefined (⟦ weakenTy (sum A B) ⟧Ty [A])
                                    AwSumABᵈ = ⟦weaken⟧Tyᵈ (sum A B) SumABᵈ A=                                    
                                    AwSumAB= = ⟦weaken⟧Ty= (sum A B) SumABᵈ A=                                    

                                    AwCᵈ : isDefined (⟦ weakenTy' (prev last) C ⟧Ty _)
                                    AwCᵈ = ⟦weaken⟧Ty+ᵈ C Cᵈ A= SumAB-ft refl
                                    AwC= = ⟦weaken⟧Ty+= C Cᵈ A= SumAB-ft refl
                                    
                                    AwAᵈ : isDefined (⟦ weakenTy A ⟧Ty [A])
                                    AwAᵈ = ⟦weaken⟧Tyᵈ A Aᵈ A=
                                    AwA= = ⟦weaken⟧Ty= A Aᵈ A=
                                    AwA-ft = ⟦⟧Ty-ft (weakenTy A)

                                    AwBᵈ : isDefined (⟦ weakenTy B ⟧Ty [A])
                                    AwBᵈ = ⟦weaken⟧Tyᵈ B Bᵈ A=
                                    AwB= = ⟦weaken⟧Ty= B Bᵈ A=
                                    AwB-ft = ⟦⟧Ty-ft (weakenTy B)

                                    inlwAwBlastᵈ : isDefined (⟦ inl (weakenTy A) (weakenTy B) (var last) ⟧Tm [A])
                                    inlwAwBlastᵈ = (AwAᵈ , AwA-ft , AwBᵈ , AwB-ft , tt , ssₛ , (varCL₁ ∙ AwA=) , tt)
                                    inlwAwBlast₁ = inlStr₁ ∙ ! AwSumAB=

      dbᵈ = ⟦⟧Tmᵈ (Γᵈ , Bᵈ , tt) ddb
      dbₛ = ⟦⟧Tmₛ db
      db₁ = ⟦⟧Tm₁ (Γᵈ , Bᵈ , tt) ddb ∙ substBwCinrb=
          where  substBwCinrb= : ⟦ substTy (weakenTy' (prev last) C) (inr (weakenTy A) (weakenTy B) (var last)) ⟧Ty [B] $ _
                               ≡ T-db₁ _ [A] A= [B] B= [C] C=
                 substBwCinrb= = ⟦subst⟧Ty= (weakenTy' (prev last) C)
                                            BwCᵈ
                                            (inr (weakenTy A) (weakenTy B) (var last))
                                            inrwAwBlastᵈ
                                            inrwAwBlast₁
                                 ∙ ! (ap-irr-star (ap-irr-inrStr refl BwA= BwB= refl) BwC=)
                               where BwSumABᵈ : isDefined (⟦ weakenTy (sum A B) ⟧Ty [B])
                                     BwSumABᵈ = ⟦weaken⟧Tyᵈ (sum A B) SumABᵈ B=                                     
                                     BwSumAB= = ⟦weaken⟧Ty= (sum A B) SumABᵈ B=                                   
      
                                     BwCᵈ : isDefined (⟦ weakenTy' (prev last) C ⟧Ty _)
                                     BwCᵈ = ⟦weaken⟧Ty+ᵈ C Cᵈ B= SumAB-ft refl
                                     BwC= = ⟦weaken⟧Ty+= C Cᵈ B= SumAB-ft refl
                                     
                                     BwAᵈ : isDefined (⟦ weakenTy A ⟧Ty [B])
                                     BwAᵈ = ⟦weaken⟧Tyᵈ A Aᵈ B=
                                     BwA= = ⟦weaken⟧Ty= A Aᵈ B=
                                     BwA-ft = ⟦⟧Ty-ft (weakenTy A)

                                     BwBᵈ : isDefined (⟦ weakenTy B ⟧Ty [B])
                                     BwBᵈ = ⟦weaken⟧Tyᵈ B Bᵈ B=
                                     BwB= = ⟦weaken⟧Ty= B Bᵈ B=
                                     BwB-ft = ⟦⟧Ty-ft (weakenTy B)

                                     inrwAwBlastᵈ : isDefined (⟦ inr (weakenTy A) (weakenTy B) (var last) ⟧Tm [B])
                                     inrwAwBlastᵈ = (BwAᵈ , BwA-ft , BwBᵈ , BwB-ft , tt , ssₛ , (varCL₁ ∙ BwB=) , tt)
                                     inrwAwBlast₁ = inrStr₁ ∙ ! BwSumAB=
            
      uᵈ = ⟦⟧Tmᵈ Γᵈ du
      uₛ = ⟦⟧Tmₛ u
      u₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = SumABᵈ} du

⟦⟧Tmᵈ Γᵈ {u = pi i a b} (PiUU da db) =
  (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)
    where
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da
      bᵈ = ⟦⟧Tmᵈ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
⟦⟧Tmᵈ Γᵈ {u = lam A B u} (Lam dA dB du) =
  (Aᵈ ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt ) dB ,
   ⟦⟧Ty-ft B ,
   ⟦⟧Tmᵈ (Γᵈ , Aᵈ , tt) du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ (Γᵈ , Aᵈ , tt) du , tt)
  where
    Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
⟦⟧Tmᵈ Γᵈ {u = app A B f a} (App dA dB df da) =
  (Aᵈ ,
   A= ,
   Bᵈ ,
   B= ,
   ⟦⟧Tmᵈ Γᵈ df ,
   ⟦⟧Tmₛ f ,
   ⟦⟧Tm₁ Γᵈ {A = pi A B} {Aᵈ = (Aᵈ , A= , Bᵈ , B= , tt)} df ,
   ⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da , tt)
     where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B

⟦⟧Tmᵈ Γᵈ {u = sig i a b} (SigUU da db) =
  (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)
    where
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da
      bᵈ = ⟦⟧Tmᵈ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db
⟦⟧Tmᵈ Γᵈ {u = pair A B a b} (Pair dA dB da db) =
  (Aᵈ ,
   A= ,
   Bᵈ ,
   ⟦⟧Ty-ft B ,
   aᵈ ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da ,
   ⟦⟧Tmᵈ Γᵈ db ,
   ⟦⟧Tmₛ b ,
   (⟦⟧Tm₁ Γᵈ db ∙ ⟦subst⟧Ty= B Bᵈ a aᵈ (⟦⟧Tm₁ Γᵈ da)) , tt)
     where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
⟦⟧Tmᵈ Γᵈ {u = pr1 A B u} (Pr1 dA dB du) =
  (Aᵈ ,
   A= ,
   Bᵈ ,
   B= ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ {A = sig A B} {Aᵈ = (Aᵈ , A= , Bᵈ , B= , tt)} du , tt)
     where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B 
⟦⟧Tmᵈ Γᵈ {u = pr2 A B u} (Pr2 dA dB du) =
  (Aᵈ ,
   A= ,
   Bᵈ ,
   B= ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ {A = sig A B} {Aᵈ = (Aᵈ , A= , Bᵈ , B= , tt)} du , tt)
     where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B  

⟦⟧Tmᵈ Γᵈ EmptyUU = tt
⟦⟧Tmᵈ Γᵈ {u = emptyelim A u} (Emptyelim dA du) =
  (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ du , tt)
⟦⟧Tmᵈ Γᵈ UnitUU = tt
⟦⟧Tmᵈ Γ TT = tt
⟦⟧Tmᵈ Γᵈ {u = unitelim A dtt u} (Unitelim dA ddtt du) =
  (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tmᵈ Γᵈ ddtt ,
   ⟦⟧Tmₛ dtt ,
   (⟦⟧Tm₁ Γᵈ ddtt ∙ ⟦subst⟧Ty= A (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA) tt tt ttStr₁) ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ du , tt)
⟦⟧Tmᵈ Γᵈ {u = nat i} NatUU = tt
⟦⟧Tmᵈ Γᵈ {u = zero} Zero = tt
⟦⟧Tmᵈ Γᵈ {u = suc u} (Suc du) =
  (⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ du , tt)
⟦⟧Tmᵈ {Γ = Γ} Γᵈ {u = natelim P dO dS u} (Natelim dP ddO ddS du) =
  (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt)
    where
      [Γ] = ⟦ Γ ⟧Ctx $ Γᵈ     

      Pᵈ : isDefined (⟦ P ⟧Ty (NatStr [Γ]))
      Pᵈ  = ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP
      [P] = ⟦ P ⟧Ty (NatStr [Γ]) $ Pᵈ
      P=  = ⟦⟧Ty-ft P {Aᵈ = Pᵈ}

      dOᵈ = ⟦⟧Tmᵈ Γᵈ ddO
      dOₛ = ⟦⟧Tmₛ dO
      dO₁ = ⟦⟧Tm₁ Γᵈ ddO ∙ substPzero=
          where substPzero= : ⟦ substTy P zero ⟧Ty [Γ] $ _ ≡ star (⟦ zero ⟧Tm [Γ] $ tt) [P] P= zeroStr₁
                substPzero= = ⟦subst⟧Ty= P Pᵈ zero tt zeroStr₁       
    
      dSᵈ = ⟦⟧Tmᵈ ((Γᵈ , (tt , tt)) , Pᵈ , tt) ddS
      dSₛ = ⟦⟧Tmₛ dS      
      dS₁ = ⟦⟧Tm₁ ((Γᵈ , (tt , tt)) , Pᵈ , tt) ddS ∙ subst_PprevwnatprevwP_sucprevlast=
          where subst_PprevwnatprevwP_sucprevlast= : ⟦ substTy (weakenTy' (prev last) (weakenTy' (prev last) P)) (suc (var (prev last))) ⟧Ty [P] $ _ ≡ T-dS₁ [Γ] [P] P=
                subst_PprevwnatprevwP_sucprevlast= = ⟦subst⟧Ty= (weakenTy' (prev last) (weakenTy' (prev last) P))
                                                      PprevwnatprevwPᵈ
                                                      (suc (var (prev last)))
                                                      sucprevlastᵈ
                                                      sucprevlast₁
                                                   ∙ ! (ap-irr-star refl PprevwnatprevwP=)
                                                   where nat= = ⟦⟧Ty-ft nat {Aᵈ = tt}
                                                   
                                                         natwnatᵈ : isDefined (⟦ weakenTy nat ⟧Ty (NatStr [Γ]))
                                                         natwnatᵈ = ⟦weaken⟧Tyᵈ nat tt nat=

                                                         natwnat= = ⟦weaken⟧Ty= nat tt nat=                                                        

                                                         natprevwPᵈ : isDefined (⟦ weakenTy' (prev last) P ⟧Ty _)
                                                         natprevwPᵈ = ⟦weaken⟧Ty+ᵈ P Pᵈ nat= nat= refl
                                                         natprevwP= = ⟦weaken⟧Ty+= P Pᵈ nat= nat= refl
      
                                                         PprevwnatprevwPᵈ : isDefined (⟦ weakenTy' (prev last) (weakenTy' (prev last) P) ⟧Ty _)
                                                         PprevwnatprevwPᵈ = ⟦weaken⟧Ty+ᵈ (weakenTy' (prev last) P) natprevwPᵈ P= (ft-star ∙ pp₀) refl
                                                         PprevwnatprevwP= = ap-irr-star refl natprevwP= ∙ ⟦weaken⟧Ty+= (weakenTy' (prev last) P) natprevwPᵈ P= (ft-star ∙ pp₀) refl

                                                         Pwnatwnatᵈ : isDefined (⟦ weakenTy (weakenTy nat) ⟧Ty [P])
                                                         Pwnatwnatᵈ = ⟦weaken⟧Tyᵈ (weakenTy nat) natwnatᵈ P=
                                                         Pwnatwnat= = ap-irr-star refl natwnat= ∙ ⟦weaken⟧Ty= (weakenTy nat) natwnatᵈ P=                                                               
                                                         
                                                         sucprevlastᵈ : isDefined (⟦ suc (var (prev last)) ⟧Tm [P])
                                                         sucprevlastᵈ = (tt , ssₛ , (varC+₁ last P= varCL₁ ∙ Pwnatwnat=) , tt)
                                                         sucprevlast₁ = sucStr₁ ∙ ! Pwnatwnat=

      uᵈ  = ⟦⟧Tmᵈ Γᵈ du
      uₛ  = ⟦⟧Tmₛ u
      u₁  = ⟦⟧Tm₁ Γᵈ du


⟦⟧Tmᵈ Γᵈ {u = id i a u v} (IdUU da du dv) =
  (⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da ,
   ⟦⟧Tmᵈ Γᵈ du ,
   ⟦⟧Tmₛ u ,
   ⟦⟧Tm₁ Γᵈ {A = el i a} {Aᵈ = ⟦⟧Tmᵈ Γᵈ da , ⟦⟧Tmₛ a , ⟦⟧Tm₁ Γᵈ da , tt} du ,
   ⟦⟧Tmᵈ Γᵈ dv ,
   ⟦⟧Tmₛ v ,
   ⟦⟧Tm₁ Γᵈ {A = el i a} {Aᵈ = ⟦⟧Tmᵈ Γᵈ da , ⟦⟧Tmₛ a , ⟦⟧Tm₁ Γᵈ da , tt} dv , tt)
⟦⟧Tmᵈ Γᵈ {u = refl A a} (Refl dA da) =
  (⟦⟧Tyᵈ Γᵈ dA ,
   ⟦⟧Ty-ft A ,
   ⟦⟧Tmᵈ Γᵈ da ,
   ⟦⟧Tmₛ a ,
   ⟦⟧Tm₁ Γᵈ da , tt)
⟦⟧Tmᵈ {Γ = Γ} Γᵈ {u = jj A P d a b p} (JJ dA dP dd da db dp) = 
  (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt)
   where
      [Γ] = ⟦ Γ ⟧Ctx $ Γᵈ
      
      Aᵈ : isDefined (⟦ A ⟧Ty [Γ])
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      [A] = ⟦ A ⟧Ty [Γ] $ Aᵈ      
      A= = ⟦⟧Ty-ft A
      
      AwAᵈ : isDefined (⟦ weakenTy A ⟧Ty [A])
      AwAᵈ = ⟦weaken⟧Tyᵈ A Aᵈ A=
      AwA= = ⟦weaken⟧Ty= A Aᵈ A=
      AwA-ft = ⟦⟧Ty-ft (weakenTy A) {Aᵈ = AwAᵈ}
      
      Pᵈ : isDefined (⟦ P ⟧Ty (T-ftP [Γ] [A] A=))
      Pᵈ = cong⟦⟧Tyᵈ {A = P} id= Pᵈ'
         where [AwA] = ⟦ weakenTy A ⟧Ty [A] $ AwAᵈ
                     
               AwAwAᵈ : isDefined (⟦ weakenTy (weakenTy A) ⟧Ty [AwA])
               AwAwAᵈ = ⟦weaken⟧Tyᵈ (weakenTy A) AwAᵈ AwA-ft
               AwAwA= = ⟦weaken⟧Ty= (weakenTy A) AwAᵈ AwA-ft
               AwAwA-ft = ⟦⟧Ty-ft (weakenTy (weakenTy A)) {Aᵈ = AwAwAᵈ}
                         
               idᵈ : isDefined (⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [AwA])
               idᵈ = (AwAwAᵈ , AwAwA-ft
                     , tt , ssₛ , (varC+₁ last AwA-ft (varCL₁ ∙ AwA=) ∙ AwAwA=)
                     , tt , ssₛ , (varCL₁ ∙ AwAwA=) , tt)
               [id] = ⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty _ $ idᵈ
               id= : T-ftP [Γ] [A] A= ≡ [id]
               id= = ap-irr-IdStr AwA=
                                  (ap-irr-star (ap pp AwA=) AwA= ∙ AwAwA=)                          
                                  (ap (varC (prev last)) AwA=)
                                  (ap (varC last) AwA=)
               Pᵈ' : isDefined (⟦ P ⟧Ty [id])    
               Pᵈ' = ⟦⟧Tyᵈ (((Γᵈ , Aᵈ , tt) , AwAᵈ , tt) , idᵈ , tt) dP
      [P] = ⟦ P ⟧Ty (T-ftP [Γ] [A] A=) $ Pᵈ
      P= = ⟦⟧Ty-ft P {Aᵈ = Pᵈ}  
      
                                                    
      dᵈ : isDefined (⟦ d ⟧Tm [A])
      dᵈ = ⟦⟧Tmᵈ (Γᵈ , Aᵈ , tt) dd
      dₛ = ⟦⟧Tmₛ d
      d₁ : ∂₁ (⟦ d ⟧Tm [A] $ dᵈ) ≡ T-d₁ [Γ] [A] A= [P] P=
      d₁ = ⟦⟧Tm₁ (Γᵈ , Aᵈ , tt) dd ∙ subst3_prevprevprevwP_varlast_varlast_refllast=
         where subst3_prevprevprevwP_varlast_varlast_refllast= : ⟦ subst3Ty (weakenTy' (prev (prev (prev last))) P) (var last) (var last) (refl (weakenTy A) (var last)) ⟧Ty [A] $ _
                                                                  ≡  T-d₁ [Γ] [A] A= [P] P=
               subst3_prevprevprevwP_varlast_varlast_refllast= = ⟦subst3⟧Ty= (ft-star ∙ qq₀) (ft-star ∙ qq₀) (ft-star ∙ pp₀)
                                                                              (weakenTy' (prev (prev (prev last))) P) AprevprevprevwPᵈ
                                                                              (var last) varlastᵈ varlast₁
                                                                              (var last) varlastᵈ (varlast₁ ∙ ! star-varCL-star-qqpp)
                                                                              (refl (weakenTy A) (var last)) reflᵈ (refl₁' ∙ T-d₁_refl₁)
                                                                  ∙ ! (ap-irr-star (ap-irr-reflStr refl AwA= refl) (ap-irr-star refl (ap-irr-star refl AprevprevprevwP=)))
                                                                where varlastᵈ : isDefined (⟦ var last ⟧Tm [A])
                                                                      varlastᵈ = tt
                                                                      [varlast] = ⟦ var last ⟧Tm [A] $ varlastᵈ
                                                                      varlast₁ : ∂₁ [varlast] ≡ star (pp [A]) [A] _ _
                                                                      varlast₁ = varCL₁

                                                                      reflᵈ : isDefined (⟦ refl (weakenTy A) (var last) ⟧Tm [A])
                                                                      reflᵈ = (AwAᵈ , AwA-ft , tt , varCₛ last [A] , (varlast₁ ∙ AwA=) , tt)
                                                                      refl₁' : ∂₁ (⟦ refl (weakenTy A) (var last) ⟧Tm [A] $ reflᵈ ) ≡ IdStr [A] (star (pp [A]) [A] _ _) (ft-star ∙ pp₀)
                                                                                                                                            [varlast] ssₛ varlast₁
                                                                                                                                            [varlast] ssₛ varlast₁
                                                                      refl₁' = reflStr₁ ∙ ! (ap-irr-IdStr refl AwA= refl refl)                                                                    
                                                                                                                                            
                                                                      AprevprevprevwPᵈ : isDefined (⟦ weakenTy' (prev (prev (prev last))) P ⟧Ty _)
                                                                      AprevprevprevwPᵈ = ⟦weaken⟧Ty+++ᵈ P Pᵈ A= T-ftP= (ft-star ∙ pp₀) A= refl
                                                                      AprevprevprevwP= = ⟦weaken⟧Ty+++= P Pᵈ A= T-ftP= (ft-star ∙ pp₀) A= refl

      aᵈ : isDefined (⟦ a ⟧Tm [Γ])
      aᵈ = ⟦⟧Tmᵈ Γᵈ da
      aₛ = ⟦⟧Tmₛ a
      a₁ = ⟦⟧Tm₁ Γᵈ da

      bᵈ : isDefined (⟦ b ⟧Tm [Γ])
      bᵈ = ⟦⟧Tmᵈ Γᵈ db
      bₛ = ⟦⟧Tmₛ b
      b₁ = ⟦⟧Tm₁ Γᵈ db

      pᵈ : isDefined (⟦ p ⟧Tm [Γ])
      pᵈ = ⟦⟧Tmᵈ Γᵈ dp
      pₛ = ⟦⟧Tmₛ p
      p₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = (Aᵈ , A= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)} dp


{- Proof of ⟦⟧Tm₁ -}

⟦⟧Tm₁ Γᵈ (Var k dA) = ⟦getTy⟧ k Γᵈ (⟦getTy⟧ᵈ k Γᵈ)
⟦⟧Tm₁ Γᵈ (Conv dA du dA=) = ⟦⟧Tm₁ Γᵈ du ∙ ⟦⟧TyEq Γᵈ dA= {Aᵈ = ⟦⟧Tyᵈ Γᵈ dA}

⟦⟧Tm₁ Γᵈ {u = uu i} UUUU = uuStr₁

⟦⟧Tm₁ Γᵈ {u = sum i a b} (SumUU da db) = sumStr₁
⟦⟧Tm₁ Γᵈ {u = inl A B a} (Inl dA dB da) = inlStr₁
⟦⟧Tm₁ Γᵈ {u = inr A B b} (Inr dA dB db) = inrStr₁
⟦⟧Tm₁ Γᵈ {u = match A B C da db u} (Match dA dB dC dda ddb du) = matchStr₁ ∙ ! (⟦subst⟧Ty= C (⟦⟧Tyᵈ (Γᵈ , (⟦⟧Tyᵈ Γᵈ dA , ⟦⟧Ty-ft A , ⟦⟧Tyᵈ Γᵈ dB , ⟦⟧Ty-ft B , tt) , tt) dC) u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ {Aᵈ = (⟦⟧Tyᵈ Γᵈ dA , ⟦⟧Ty-ft A , ⟦⟧Tyᵈ Γᵈ dB , ⟦⟧Ty-ft B , tt)} du))

⟦⟧Tm₁ Γᵈ {u = pi i a b} (PiUU da db) = piStr₁
⟦⟧Tm₁ Γᵈ {u = lam A B u} (Lam dA dB du) = lamStr₁
⟦⟧Tm₁ Γᵈ {u = app A B f a} (App dA dB df da) = appStr₁ ∙ ! (⟦subst⟧Ty= B (⟦⟧Tyᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))

⟦⟧Tm₁ Γᵈ {u = sig i a b} (SigUU da db) = sigStr₁
⟦⟧Tm₁ Γᵈ {u = pair A B a b} (Pair dA dB da db) = pairStr₁
⟦⟧Tm₁ Γᵈ {u = pr1 A B u} (Pr1 dA dB du) = pr1Str₁
⟦⟧Tm₁ Γᵈ {u = pr2 A B u} (Pr2 dA dB du) =
  pr2Str₁ ∙ ! (⟦subst⟧Ty= B Bᵈ (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , ⟦⟧Tmᵈ Γᵈ du , ⟦⟧Tmₛ u , ⟦⟧Tm₁ Γᵈ {A = sig A B} {Aᵈ = Aᵈ , A= , Bᵈ , B= , tt} du , tt) pr1Str₁)
    where
      Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
      A= = ⟦⟧Ty-ft A
      Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
      B= = ⟦⟧Ty-ft B
      
⟦⟧Tm₁ Γᵈ EmptyUU = emptyStr₁
⟦⟧Tm₁ Γᵈ {u = emptyelim A u} (Emptyelim dA du) = emptyelimStr₁ ∙ ! (⟦subst⟧Ty= A (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA) u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ du))
⟦⟧Tm₁ Γᵈ UnitUU = unitStr₁
⟦⟧Tm₁ Γᵈ TT = ttStr₁
⟦⟧Tm₁ Γᵈ {u = unitelim A dtt u} (Unitelim dA ddtt du) = unitelimStr₁ ∙ ! (⟦subst⟧Ty= A (⟦⟧Tyᵈ (Γᵈ , tt , tt) dA) u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ du))

⟦⟧Tm₁ Γᵈ {u = nat i} NatUU = natStr₁
⟦⟧Tm₁ Γᵈ {u = zero} Zero = zeroStr₁
⟦⟧Tm₁ Γᵈ {u = suc u} (Suc du) = sucStr₁
⟦⟧Tm₁ Γᵈ {u = natelim P dO dS u} (Natelim dP ddO ddS du) = natelimStr₁ ∙ ! (⟦subst⟧Ty= P (⟦⟧Tyᵈ (Γᵈ , tt , tt) dP) u (⟦⟧Tmᵈ Γᵈ du) (⟦⟧Tm₁ Γᵈ du))

⟦⟧Tm₁ Γᵈ {u = id i a u v} (IdUU da du dv) = idStr₁
⟦⟧Tm₁ Γᵈ {u = refl A a} (Refl dA da) = reflStr₁
⟦⟧Tm₁ {Γ = Γ} Γᵈ {u = jj A P d a b p} (JJ dA dP dd da db dp) =
         jjStr₁ ∙ ! subst3_P_a_b_p= 
      where [Γ] = ⟦ Γ ⟧Ctx $ Γᵈ
        
            Aᵈ : isDefined (⟦ A ⟧Ty [Γ])
            Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
            [A] = ⟦ A ⟧Ty [Γ] $ Aᵈ        
            A= = ⟦⟧Ty-ft A
        
            AwAᵈ : isDefined (⟦ weakenTy A ⟧Ty [A])
            AwAᵈ = ⟦weaken⟧Tyᵈ A Aᵈ A=
            AwA= = ⟦weaken⟧Ty= A Aᵈ A=
            AwA-ft = ⟦⟧Ty-ft (weakenTy A) {Aᵈ = AwAᵈ}
      
            Pᵈ : isDefined (⟦ P ⟧Ty (T-ftP [Γ] [A] A=))
            Pᵈ = cong⟦⟧Tyᵈ {A = P} id= Pᵈ'
               where [AwA] = ⟦ weakenTy A ⟧Ty [A] $ AwAᵈ
                     
                     AwAwAᵈ : isDefined (⟦ weakenTy (weakenTy A) ⟧Ty [AwA])
                     AwAwAᵈ = ⟦weaken⟧Tyᵈ (weakenTy A) AwAᵈ AwA-ft
                     AwAwA= = ⟦weaken⟧Ty= (weakenTy A) AwAᵈ AwA-ft
                     AwAwA-ft = ⟦⟧Ty-ft (weakenTy (weakenTy A)) {Aᵈ = AwAwAᵈ}
                         
                     idᵈ : isDefined (⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [AwA])
                     idᵈ = (AwAwAᵈ , AwAwA-ft
                           , tt , ssₛ , (varC+₁ last AwA-ft (varCL₁ ∙ AwA=) ∙ AwAwA=)
                           , tt , ssₛ , (varCL₁ ∙ AwAwA=) , tt)
                     [id] = ⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty _ $ idᵈ
                     id= : T-ftP [Γ] [A] A= ≡ [id]
                     id= = ap-irr-IdStr AwA=
                                        (ap-irr-star (ap pp AwA=) AwA= ∙ AwAwA=)                          
                                        (ap (varC (prev last)) AwA=)
                                        (ap (varC last) AwA=)
                                                              
                     Pᵈ' : isDefined (⟦ P ⟧Ty [id])    
                     Pᵈ' = ⟦⟧Tyᵈ (((Γᵈ , Aᵈ , tt) , AwAᵈ , tt) , idᵈ , tt) dP
            [P] = ⟦ P ⟧Ty (T-ftP [Γ] [A] A=) $ Pᵈ
            P= = ⟦⟧Ty-ft P {Aᵈ = Pᵈ}

            aᵈ : isDefined (⟦ a ⟧Tm [Γ])                     
            aᵈ = ⟦⟧Tmᵈ Γᵈ da
            [a] = ⟦ a ⟧Tm [Γ] $ aᵈ
            aₛ = ⟦⟧Tmₛ a
            a₁ = ⟦⟧Tm₁ Γᵈ da

            bᵈ : isDefined (⟦ b ⟧Tm [Γ])
            bᵈ = ⟦⟧Tmᵈ Γᵈ db
            [b] = ⟦ b ⟧Tm [Γ] $ bᵈ
            bₛ = ⟦⟧Tmₛ b
            b₁ = ⟦⟧Tm₁ Γᵈ db

            pᵈ : isDefined (⟦ p ⟧Tm [Γ])
            pᵈ = ⟦⟧Tmᵈ Γᵈ dp
            [p] = ⟦ p ⟧Tm [Γ] $ pᵈ
            pₛ = ⟦⟧Tmₛ p
            p₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = (Aᵈ , A= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt)} dp
            
            subst3_P_a_b_p= : ⟦ subst3Ty P a b p ⟧Ty [Γ] $ _ ≡ T-jjStr₁ [Γ] [A] A= [P] P= [a] aₛ a₁ [b] bₛ b₁ [p] pₛ p₁
            subst3_P_a_b_p= = ⟦subst3⟧Ty= T-ftP= (ft-star ∙ pp₀) A=
                                          P Pᵈ
                                          a aᵈ a₁
                                          b bᵈ (b₁ ∙ ! (star-pp' A= A= aₛ a₁))
                                          p pᵈ (p₁ ∙ ! (ap-irr-star refl (IdStrNat qq₀ ∙ ap-irr-IdStr [wA][a]= (star-pp (⟦⟧Tm₀ a) ∙ ap-irr-star (ap pp [wA][a]=) [wA][a]=) (star-varC+' (⟦⟧Tmₛ a) ∙ ap-irr-starTm (ap pp [wA][a]=) refl) {u'ₛ = ssₛ} {u'₁ = starTm₁ (pp [A]) A= _ aₛ a₁ (pp₁ ∙ A=)} (star-varCL ∙ ap (varC last) [wA][a]=) {v'ₛ = ssₛ} {v'₁ = varCL₁}) {q = ft-star ∙ qq₀} {q' = IdStr=} {f₁' = b₁} ∙ IdStrNat (⟦⟧Tm₀ b) ∙ ap-irr-IdStr refl [wA][b]= (! (starTm-comp pp₀) ∙ ap-irr-starTm (is-section= A= bₛ b₁) refl ∙ starTm-id (⟦⟧Tm₀ a) aₛ) (star-varCL' ∙ ss-of-section _ bₛ))) 
                            where [wA][a]= : star [a] (star (pp [A]) [A] A= (pp₁ ∙ A=)) (ft-star ∙ pp₀) a₁ ≡ [A]
                                  [wA][a]= = star-pp' A= A= aₛ a₁
                                  [wA][b]= : star [b] (star (pp [A]) [A] A= (pp₁ ∙ A=)) (ft-star ∙ pp₀) b₁ ≡ [A]
                                  [wA][b]= = star-pp' A= A= bₛ b₁
                                                                                            

{- Lemmas following from ⟦⟧TyEq/⟦⟧TmEq -}

⟦⟧TyEq+ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {X' : Ob n} {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A'))
          {Aᵈ : isDefined (⟦ A ⟧Ty X)} {A'ᵈ : isDefined (⟦ A' ⟧Ty X')} → X ≡ X' → ⟦ A ⟧Ty X $ Aᵈ ≡ ⟦ A' ⟧Ty X' $ A'ᵈ
⟦⟧TyEq+ Γᵈ dA= refl = ⟦⟧TyEq Γᵈ dA=


⟦⟧TmEq+ : {Γ : Ctx n} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {X' : Ob n} {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A))
          {uᵈ : isDefined (⟦ u ⟧Tm X)} {u'ᵈ : isDefined (⟦ u' ⟧Tm X')} → X ≡ X' → ⟦ u ⟧Tm X $ uᵈ ≡ ⟦ u' ⟧Tm X' $ u'ᵈ
⟦⟧TmEq+ Γᵈ du= refl = ⟦⟧TmEq Γᵈ du=


{- Proof of ⟦⟧TyEq/⟦⟧TmEq -}

⟦⟧TyEq Γᵈ (TyRefl dA) = refl
⟦⟧TyEq Γᵈ (TySymm dA=) = ! (⟦⟧TyEq Γᵈ dA=)
⟦⟧TyEq Γᵈ (TyTran dB dA= dB=) = ⟦⟧TyEq Γᵈ dA= {A'ᵈ = ⟦⟧Tyᵈ Γᵈ dB} ∙ ⟦⟧TyEq Γᵈ dB=

⟦⟧TyEq Γᵈ UUCong = refl
⟦⟧TyEq Γᵈ (ElCong dv=) = ap-irr-ElStr refl (⟦⟧TmEq Γᵈ dv=)
⟦⟧TyEq Γᵈ {A = sum A B} (SumCong dA= dB=) = ap-irr-SumStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq Γᵈ dB=)
⟦⟧TyEq Γᵈ {A = sig A B} (SigCong dA dA= dB=) = ap-irr-SigStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TyEq Γᵈ {A = pi A B} (PiCong dA dA= dB=) = ap-irr-PiStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TyEq Γᵈ EmptyCong = refl
⟦⟧TyEq Γᵈ UnitCong = refl
⟦⟧TyEq Γᵈ NatCong = refl
⟦⟧TyEq Γᵈ (IdCong dA du dv) = ap-irr-IdStr refl (⟦⟧TyEq Γᵈ dA) (⟦⟧TmEq Γᵈ du) (⟦⟧TmEq Γᵈ dv)

⟦⟧TyEq Γᵈ ElUU= = eluuStr
⟦⟧TyEq Γᵈ (ElSum= da db) = elsumStr
⟦⟧TyEq Γᵈ (ElPi= da db) = elpiStr 
⟦⟧TyEq Γᵈ (ElSig= da db) = elsigStr
⟦⟧TyEq Γᵈ ElEmpty= = elemptyStr
⟦⟧TyEq Γᵈ ElUnit= = elunitStr
⟦⟧TyEq Γᵈ ElNat= = elnatStr
⟦⟧TyEq Γᵈ (ElId= da du dv) = elidStr

⟦⟧TmEq Γᵈ (TmRefl du) = refl
⟦⟧TmEq Γᵈ (TmSymm du=) = ! (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq Γᵈ (TmTran dv du= du'=) = ⟦⟧TmEq Γᵈ du= {u'ᵈ = ⟦⟧Tmᵈ Γᵈ dv} ∙ ⟦⟧TmEq Γᵈ du'=
⟦⟧TmEq Γᵈ (ConvEq dA' du= dA=) = ⟦⟧TmEq Γᵈ du=

⟦⟧TmEq Γᵈ UUUUCong = refl

⟦⟧TmEq Γᵈ {u = sum i a b} (SumUUCong da= db=) = ap-irr-sumStr refl (⟦⟧TmEq Γᵈ da=) (⟦⟧TmEq Γᵈ db=)
⟦⟧TmEq Γᵈ {u = inl A B a} (InlCong dA= dB= da=) = ap-irr-inlStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq Γᵈ dB=) (⟦⟧TmEq Γᵈ da=)
⟦⟧TmEq Γᵈ {u = inr A B b} (InrCong dA= dB= db=) = ap-irr-inrStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq Γᵈ dB=) (⟦⟧TmEq Γᵈ db=)
⟦⟧TmEq Γᵈ {u = match A B C da db u} (MatchCong dA= dB= dC= dA da= dB db= du=) =
       ap-irr-matchStr refl
                       (⟦⟧TyEq Γᵈ dA=)
                       (⟦⟧TyEq Γᵈ dB=)
                       (⟦⟧TyEq+ (Γᵈ , (⟦⟧Tyᵈ Γᵈ dA , ⟦⟧Ty-ft A , ⟦⟧Tyᵈ Γᵈ dB , ⟦⟧Ty-ft B , tt) , tt) dC=
                                (ap-irr-SumStr refl (⟦⟧TyEq Γᵈ dA=) (⟦⟧TyEq Γᵈ dB=)))
                       (⟦⟧TmEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) da= (⟦⟧TyEq Γᵈ dA=))
                       (⟦⟧TmEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dB , tt) db= (⟦⟧TyEq Γᵈ dB=))
                       (⟦⟧TmEq Γᵈ du=)
                       
⟦⟧TmEq Γᵈ {u = pi i a b} (PiUUCong da da= db=) {uᵈ = (aᵈ , aₛ , a₁ , _)} =
       ap-irr-piStr refl
                    (⟦⟧TmEq Γᵈ da=)
                    (⟦⟧TmEq+ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db= (ap-irr-ElStr refl (⟦⟧TmEq Γᵈ da=)))
⟦⟧TmEq Γᵈ {u = lam A B u} (LamCong dA dA= dB= du=) =
       ap-irr-lamStr refl
                     (⟦⟧TyEq Γᵈ dA=)
                     (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
                     (⟦⟧TmEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) du= (⟦⟧TyEq Γᵈ dA=))
⟦⟧TmEq Γᵈ {u = app A B f a} (AppCong dA dA= dB= df= da=) =
       ap-irr-appStr refl
                     (⟦⟧TyEq Γᵈ dA=)
                     (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
                     (⟦⟧TmEq Γᵈ df=) (⟦⟧TmEq Γᵈ da=)

⟦⟧TmEq Γᵈ {u = sig i a b} (SigUUCong da da= db=) {uᵈ = (aᵈ , aₛ , a₁ , bᵈ , _)} {u'ᵈ = (a'ᵈ , _ , _ , b'ᵈ , _)} =
       ap-irr-sigStr refl
                     (⟦⟧TmEq Γᵈ da=)
                     (⟦⟧TmEq+ (Γᵈ , (aᵈ , aₛ , a₁ , tt) , tt) db= (ap-irr-ElStr refl (⟦⟧TmEq Γᵈ da=)))
⟦⟧TmEq Γᵈ {u = pair A B a b} (PairCong dA dA= dB= da= db=) =
       ap-irr-pairStr refl
                      (⟦⟧TyEq Γᵈ dA=)
                      (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
                      (⟦⟧TmEq Γᵈ da=)
                      (⟦⟧TmEq Γᵈ db=)
⟦⟧TmEq Γᵈ {u = pr1 A B u} (Pr1Cong dA dA= dB= du=) =
       ap-irr-pr1Str refl
                     (⟦⟧TyEq Γᵈ dA=)
                     (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
                     (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq Γᵈ {u = pr2 A B u} (Pr2Cong dA dA= dB= du=) =
       ap-irr-pr2Str refl
                     (⟦⟧TyEq Γᵈ dA=)
                     (⟦⟧TyEq+ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dB= (⟦⟧TyEq Γᵈ dA=))
                     (⟦⟧TmEq Γᵈ du=)

⟦⟧TmEq Γᵈ EmptyUUCong = refl
⟦⟧TmEq Γᵈ (EmptyelimCong dA= du=) =
       ap-irr-emptyelimStr refl
                           (⟦⟧TyEq (Γᵈ , tt , tt) dA=)
                           (⟦⟧TmEq Γᵈ du=)

⟦⟧TmEq Γᵈ UnitUUCong = refl
⟦⟧TmEq Γᵈ TTCong = refl
⟦⟧TmEq Γᵈ (UnitelimCong dA= ddtt= du=) =
       ap-irr-unitelimStr refl
                          (⟦⟧TyEq (Γᵈ , tt , tt) dA=)
                          (⟦⟧TmEq Γᵈ ddtt=)
                          (⟦⟧TmEq Γᵈ du=)

⟦⟧TmEq Γᵈ NatUUCong = refl
⟦⟧TmEq Γᵈ ZeroCong = refl
⟦⟧TmEq Γᵈ (SucCong du) = ap-irr-sucStr refl (⟦⟧TmEq Γᵈ du)
⟦⟧TmEq Γᵈ {u = natelim P dO dS u} (NatelimCong dP dP= ddO= ddS= du=) =
       ap-irr-natelimStr refl
                         (⟦⟧TyEq (Γᵈ , tt , tt) dP=)
                         (⟦⟧TmEq Γᵈ ddO=)
                         (⟦⟧TmEq+ ((Γᵈ , tt , tt) , ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP , tt) ddS= (⟦⟧TyEq (Γᵈ , tt , tt) dP=))
                         (⟦⟧TmEq Γᵈ du=)

⟦⟧TmEq Γᵈ (IdUUCong da= du= dv=) =
       ap-irr-idStr refl
                    (⟦⟧TmEq Γᵈ da=)
                    (⟦⟧TmEq Γᵈ du=)
                    (⟦⟧TmEq Γᵈ dv=)
⟦⟧TmEq Γᵈ (ReflCong dA= du=) =
       ap-irr-reflStr refl
                      (⟦⟧TyEq Γᵈ dA=)
                      (⟦⟧TmEq Γᵈ du=)
⟦⟧TmEq {Γ = Γ}  Γᵈ {u = jj A P d a b p} {u' = jj A' P' d' a' b' p'} (JJCong dA dA= dP= dd= da= db= dp=)
       {uᵈ = (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt)}
       {u'ᵈ = (A'ᵈ , A'= , P'ᵈ , P'= , d'ᵈ , d'ₛ , d'₁ , a'ᵈ , a'ₛ , a'₁ , b'ᵈ , b'ₛ , b'₁ , p'ᵈ , p'ₛ , p'₁ , tt)} =       
       ap-irr-jjStr refl
                    (⟦⟧TyEq Γᵈ dA=)
                    (cong⟦⟧TyEq {A = P} (! id=) Pᵈ
                    ∙ ⟦⟧TyEq+ (((Γᵈ , Aᵈ , tt) , (AwAᵈ , tt)) , (idᵈ , tt)) dP= {Aᵈ = cong⟦⟧Tyᵈ {A = P} (! id=) Pᵈ} {A'ᵈ = P'ᵈ}
                              (! id= ∙ ap-irr-IdStr AwA=A'wA' AwAwA=A'wA'wA' (ap (varC (prev last)) AwA=A'wA') (ap (varC last) AwA=A'wA'))) 
                    (⟦⟧TmEq+ (Γᵈ , ((⟦⟧Tyᵈ Γᵈ dA) , tt)) dd= (⟦⟧TyEq Γᵈ dA=))
                    (⟦⟧TmEq Γᵈ da=)
                    (⟦⟧TmEq Γᵈ db=)
                    (⟦⟧TmEq Γᵈ dp=)
                    where [Γ] = ⟦ Γ ⟧Ctx $ Γᵈ               
                          [A] = ⟦ A ⟧Ty [Γ] $ Aᵈ                    
                    
                          AwAᵈ : isDefined (⟦ weakenTy A ⟧Ty [A])
                          AwAᵈ = ⟦weaken⟧Tyᵈ A Aᵈ A=
                          [AwA] = ⟦ weakenTy A ⟧Ty [A] $ AwAᵈ
                          AwA= = ⟦weaken⟧Ty= A Aᵈ A=
                          AwA-ft = ⟦⟧Ty-ft (weakenTy A) {Aᵈ = AwAᵈ}

                          AwAwAᵈ : isDefined (⟦ weakenTy (weakenTy A) ⟧Ty [AwA])
                          AwAwAᵈ = ⟦weaken⟧Tyᵈ (weakenTy A) AwAᵈ AwA-ft
                          AwAwA= = ⟦weaken⟧Ty= (weakenTy A) AwAᵈ AwA-ft
                          AwAwA-ft = ⟦⟧Ty-ft (weakenTy (weakenTy A)) {Aᵈ = AwAwAᵈ}
                         
                          idᵈ : isDefined (⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty [AwA])
                          idᵈ = (AwAwAᵈ , AwAwA-ft
                                , tt , ssₛ , (varC+₁ last AwA-ft (varCL₁ ∙ AwA=) ∙ AwAwA=)
                                , tt , ssₛ , (varCL₁ ∙ AwAwA=) , tt)
                          [id] = ⟦ id (weakenTy (weakenTy A)) (var (prev last)) (var last) ⟧Ty _ $ idᵈ
                          id= : T-ftP [Γ] [A] A= ≡ [id]
                          id= = ap-irr-IdStr AwA=
                                             (ap-irr-star (ap pp AwA=) AwA= ∙ AwAwA=)                          
                                             (ap (varC (prev last)) AwA=)
                                             (ap (varC last) AwA=)
                                             
                          [A'] = ⟦ A' ⟧Ty [Γ] $ A'ᵈ        
                          A=A' : [A] ≡ [A']
                          A=A' = ⟦⟧TyEq Γᵈ dA=
                          AwA=A'wA' : star (pp [A]) [A] A= (pp₁ ∙ A=) ≡ star (pp [A']) [A'] A'= (pp₁ ∙ A'=)
                          AwA=A'wA' = ap-irr-star (ap pp A=A') A=A'
                          AwAwA=A'wA'wA' : star (pp (star (pp [A]) [A] A= (pp₁ ∙ A=))) (star (pp [A]) [A] A= (pp₁ ∙ A=)) (ft-star ∙ pp₀) (pp₁ ∙ ft-star ∙ pp₀)
                                         ≡ star (pp (star (pp [A']) [A'] A'= (pp₁ ∙ A'=))) (star (pp [A']) [A'] A'= (pp₁ ∙ A'=)) (ft-star ∙ pp₀) (pp₁ ∙ ft-star ∙ pp₀)
                          AwAwA=A'wA'wA' = ap-irr-star (ap pp AwA=A'wA') AwA=A'wA'
                     
                          
⟦⟧TmEq Γᵈ {u = match A B C da' db (inl A B a)} (BetaInl dA dB dC dda ddb da) = betaInlStr ∙ ! (⟦subst⟧Tm= da' (⟦⟧Tmᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dda) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))
⟦⟧TmEq Γᵈ {u = match A B C da db' (inr A B b)} (BetaInr dA dB dC dda ddb db) = betaInrStr ∙ ! (⟦subst⟧Tm= db' (⟦⟧Tmᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dB , tt) ddb) b (⟦⟧Tmᵈ Γᵈ db) (⟦⟧Tm₁ Γᵈ db))
⟦⟧TmEq Γᵈ {u = app A B (lam A B u) a} (BetaPi dA dB du da) = betaPiStr ∙ ! (⟦subst⟧Tm= u (⟦⟧Tmᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) du) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))
⟦⟧TmEq Γᵈ (BetaSig1 dA dB da db) = betaSig1Str
⟦⟧TmEq Γᵈ (BetaSig2 dA dB da db) = betaSig2Str
⟦⟧TmEq Γᵈ (BetaUnit dA dtt) = betaUnitStr
⟦⟧TmEq Γᵈ (BetaNatZero dP ddO ddS) = betaNatZeroStr
⟦⟧TmEq {Γ = Γ} Γᵈ {u = natelim P dO dS (suc u)} (BetaNatSuc dP ddO ddS du) =
  betaNatSucStr ∙ ! (⟦subst2⟧Tm= P= NatStr= dS dSᵈ u uᵈ u₁ (natelim P dO dS u) natelimᵈ natelimStr₁)
    where [Γ] = ⟦ Γ ⟧Ctx $ Γᵈ     

          Pᵈ : isDefined (⟦ P ⟧Ty (NatStr [Γ]))
          Pᵈ  = ⟦⟧Tyᵈ (Γᵈ , tt , tt) dP
          [P] = ⟦ P ⟧Ty (NatStr [Γ]) $ Pᵈ
          P=  = ⟦⟧Ty-ft P {Aᵈ = Pᵈ}

          dOᵈ = ⟦⟧Tmᵈ Γᵈ ddO
          dOₛ = ⟦⟧Tmₛ dO
          dO₁ = ⟦⟧Tm₁ Γᵈ ddO ∙ substPzero=
              where substPzero= : ⟦ substTy P zero ⟧Ty [Γ] $ _ ≡ star (⟦ zero ⟧Tm [Γ] $ tt) [P] P= zeroStr₁
                    substPzero= = ⟦subst⟧Ty= P Pᵈ zero tt zeroStr₁       
    
          dSᵈ = ⟦⟧Tmᵈ ((Γᵈ , (tt , tt)) , Pᵈ , tt) ddS
          dSₛ = ⟦⟧Tmₛ dS      
          dS₁ = ⟦⟧Tm₁ ((Γᵈ , (tt , tt)) , Pᵈ , tt) ddS ∙ subst_PprevwnatprevwP_sucprevlast=
              where subst_PprevwnatprevwP_sucprevlast= : ⟦ substTy (weakenTy' (prev last) (weakenTy' (prev last) P)) (suc (var (prev last))) ⟧Ty [P] $ _ ≡ T-dS₁ [Γ] [P] P=
                    subst_PprevwnatprevwP_sucprevlast= = ⟦subst⟧Ty= (weakenTy' (prev last) (weakenTy' (prev last) P))
                                                                    PprevwnatprevwPᵈ
                                                                    (suc (var (prev last)))
                                                                    sucprevlastᵈ
                                                                    sucprevlast₁
                                                         ∙ ! (ap-irr-star refl PprevwnatprevwP=)
                                                       where nat= = ⟦⟧Ty-ft nat {Aᵈ = tt}
                                                   
                                                             natwnatᵈ : isDefined (⟦ weakenTy nat ⟧Ty (NatStr [Γ]))
                                                             natwnatᵈ = ⟦weaken⟧Tyᵈ nat tt nat=
                                                             natwnat= = ⟦weaken⟧Ty= nat tt nat=                                                        
                                                         
                                                             natprevwPᵈ : isDefined (⟦ weakenTy' (prev last) P ⟧Ty _)
                                                             natprevwPᵈ = ⟦weaken⟧Ty+ᵈ P Pᵈ nat= nat= refl
                                                             natprevwP= = ⟦weaken⟧Ty+= P Pᵈ nat= nat= refl
      
                                                             PprevwnatprevwPᵈ : isDefined (⟦ weakenTy' (prev last) (weakenTy' (prev last) P) ⟧Ty _)
                                                             PprevwnatprevwPᵈ = ⟦weaken⟧Ty+ᵈ (weakenTy' (prev last) P) natprevwPᵈ P= (ft-star ∙ pp₀) refl
                                                             PprevwnatprevwP= = ap-irr-star refl natprevwP= ∙ ⟦weaken⟧Ty+= (weakenTy' (prev last) P) natprevwPᵈ P= (ft-star ∙ pp₀) refl

                                                             Pwnatwnatᵈ : isDefined (⟦ weakenTy (weakenTy nat) ⟧Ty [P])
                                                             Pwnatwnatᵈ = ⟦weaken⟧Tyᵈ (weakenTy nat) natwnatᵈ P=
                                                             Pwnatwnat= = ap-irr-star refl natwnat= ∙ ⟦weaken⟧Ty= (weakenTy nat) natwnatᵈ P=                                                               
                                                         
                                                             sucprevlastᵈ : isDefined (⟦ suc (var (prev last)) ⟧Tm [P])
                                                             sucprevlastᵈ = (tt , ssₛ , (varC+₁ last P= varCL₁ ∙ Pwnatwnat=) , tt)
                                                             sucprevlast₁ = sucStr₁ ∙ ! Pwnatwnat=

          uᵈ  = ⟦⟧Tmᵈ Γᵈ du
          uₛ  = ⟦⟧Tmₛ u
          u₁  = ⟦⟧Tm₁ Γᵈ du

          natelimᵈ : isDefined (⟦ natelim P dO dS u ⟧Tm [Γ])
          natelimᵈ = (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt)
             
⟦⟧TmEq {Γ = Γ} Γᵈ {u = jj A P d a a (refl A a)} (BetaIdRefl dA dP dd da) =
  betaIdStr ∙ ! (⟦subst⟧Tm= d (⟦⟧Tmᵈ (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt) dd) a (⟦⟧Tmᵈ Γᵈ da) (⟦⟧Tm₁ Γᵈ da))
    

⟦⟧TmEq {Γ = Γ} Γᵈ {u = u} {u' = match A B _ _ _ _} (EtaSum dA dB du) =
  etaSumStr {uₛ = ⟦⟧Tmₛ u} {u₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = SumABᵈ} du}
  ∙ ap-irr-matchStr refl refl refl
                    (⟦weaken⟧Ty= (sum A B) SumABᵈ SumStr=)
                    (ap-irr-inlStr refl AwA= AwB= refl)
                    (ap-irr-inrStr refl BwA= BwB= refl) refl
    where [Γ] = ⟦ Γ ⟧Ctx $ Γᵈ

          Aᵈ : isDefined (⟦ A ⟧Ty [Γ])
          Aᵈ = ⟦⟧Tyᵈ Γᵈ dA         
          A= = ⟦⟧Ty-ft A         

          Bᵈ : isDefined (⟦ B ⟧Ty [Γ])
          Bᵈ = ⟦⟧Tyᵈ Γᵈ dB
          B= = ⟦⟧Ty-ft B

          AwA= = ⟦weaken⟧Ty= A Aᵈ A=
          AwB= = ⟦weaken⟧Ty= B Bᵈ A=
          BwB= = ⟦weaken⟧Ty= B Bᵈ B=
          BwA= = ⟦weaken⟧Ty= A Aᵈ B=
          
          SumABᵈ : isDefined (⟦ sum A B ⟧Ty [Γ])
          SumABᵈ = (Aᵈ , A= , Bᵈ , B= , tt)
    
⟦⟧TmEq {Γ = Γ} Γᵈ {u = f} {u' = lam A B _} (EtaPi dA dB df) =
  etaPiStr {fₛ = ⟦⟧Tmₛ f} {f₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = PiABᵈ} df}
  ∙ ap-irr-lamStr refl refl refl
                  (ap-irr-appStr refl AwA=
                                      (⟦weaken⟧Ty+= B Bᵈ A= A= AwA=)
                                      (⟦weaken⟧Tm= f (⟦⟧Tmᵈ Γᵈ df) A=)
                                      refl)
    where [Γ] = ⟦ Γ ⟧Ctx $ Γᵈ

          Aᵈ : isDefined (⟦ A ⟧Ty [Γ])
          Aᵈ = ⟦⟧Tyᵈ Γᵈ dA
          [A] = ⟦ A ⟧Ty [Γ] $ Aᵈ
          A= = ⟦⟧Ty-ft A
          AwA= = ⟦weaken⟧Ty= A Aᵈ A=
          
          Bᵈ : isDefined (⟦ B ⟧Ty [A])
          Bᵈ = ⟦⟧Tyᵈ (Γᵈ , Aᵈ , tt) dB
          B= = ⟦⟧Ty-ft B

          PiABᵈ : isDefined (⟦ pi A B ⟧Ty [Γ])
          PiABᵈ = (Aᵈ , A= , Bᵈ , B= , tt)
    
⟦⟧TmEq Γᵈ (EtaSig dA dB du) =
  etaSigStr



{- We are done with the main induction in this file, here are a few additional lemmas needed later. -}

{- Totality of the interpretation function on derivable contexts -}

⟦⟧Ctxᵈ : {Γ : Ctx n} (dΓ : ⊢ Γ) → isDefined (⟦ Γ ⟧Ctx)
⟦⟧Ctxᵈ tt = tt
⟦⟧Ctxᵈ (dΓ , dA) = let Γᵈ = ⟦⟧Ctxᵈ dΓ in (Γᵈ , ⟦⟧Tyᵈ Γᵈ dA , tt)

{- Interpretation of context equalities -}

⟦⟧CtxEq : {Γ Γ' : Ctx n} (dΓ= : ⊢ Γ == Γ') {Γᵈ : isDefined (⟦ Γ ⟧Ctx)} {Γ'ᵈ : isDefined (⟦ Γ' ⟧Ctx)}
        → ⟦ Γ ⟧Ctx $ Γᵈ ≡ ⟦ Γ' ⟧Ctx $ Γ'ᵈ
⟦⟧CtxEq tt = refl
⟦⟧CtxEq (dΓ= , dA=) {Γᵈ = Γᵈ , Aᵈ , tt}
  = ⟦⟧TyEq+ Γᵈ (ConvTyEq dA= (CtxSymm dΓ=)) (⟦⟧CtxEq dΓ=)

{- Totality of the interpretation function on morphisms -}

⟦⟧Morᵈ : {Γ : Ctx n} {Δ : Ctx m} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (Δᵈ : isDefined (⟦ Δ ⟧Ctx)) {δ : Mor n m} (dδ : Γ ⊢ δ ∷> Δ) → isDefined (⟦ δ ⟧Mor (⟦ Γ ⟧Ctx $ Γᵈ) (⟦ Δ ⟧Ctx $ Δᵈ))
⟦⟧Morᵈ {Δ = ◇} _ _ {◇} tt = tt
⟦⟧Morᵈ {Δ = Δ , B} Γᵈ (Δᵈ , Bᵈ , tt) {δ , u} (dδ , du) =
  (δᵈ , uᵈ , δ₁ , u₁ , tt)
    where
      δᵈ' = ⟦⟧Morᵈ Γᵈ Δᵈ dδ
      δᵈ = cong⟦⟧Mor {δ = δ} (! (⟦⟧Ty-ft B)) δᵈ'
      uᵈ = ⟦⟧Tmᵈ Γᵈ du
      δ₁ = ⟦⟧Mor₁ δ
      u₁ = ⟦⟧Tm₁ Γᵈ {Aᵈ = ⟦tsubst⟧Tyᵈ B Bᵈ δ δᵈ'} du ∙ ! (⟦tsubst⟧Ty= B Bᵈ δ δᵈ') ∙ ap-irr-star (ap-irr {B = λ X → isDefined (⟦ δ ⟧Mor _ X)} (λ x z → ⟦ δ ⟧Mor _ x $ z) (! (⟦⟧Ty-ft B))) refl

{- Interpretation of morphism equalities -}

⟦⟧MorEq : {Γ : Ctx n} {Δ : Ctx m} {δ δ' : Mor n m} (Γᵈ : isDefined (⟦ Γ ⟧Ctx)) (let X = ⟦ Γ ⟧Ctx $ Γᵈ) {Y : Ob m} (dδ= : Γ ⊢ δ == δ' ∷> Δ) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} {δ'ᵈ : isDefined (⟦ δ' ⟧Mor X Y)}
        → ⟦ δ ⟧Mor X Y $ δᵈ ≡ ⟦ δ' ⟧Mor X Y $ δ'ᵈ
⟦⟧MorEq Γᵈ tt = refl
⟦⟧MorEq Γᵈ (dδ= , du=) = ap-irr-comp (ap-irr-qq (⟦⟧MorEq Γᵈ dδ=) refl) (⟦⟧TmEq Γᵈ du=)

{- Interpretation of morphism substitution -}

⟦tsubst⟧Morᵈ : {X : Ob n} {Y Y' : Ob m} {Z : Ob k} (Y= : Y ≡ Y') (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (θ : Mor m k) (θᵈ : isDefined (⟦ θ ⟧Mor Y' Z)) → isDefined (⟦ θ [ δ ]Mor ⟧Mor X Z)
⟦tsubst⟧Mor= : {X : Ob n} {Y Y' : Ob m} {Z : Ob k} (Y= : Y ≡ Y') (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (θ : Mor m k) (θᵈ : isDefined (⟦ θ ⟧Mor Y' Z))
             → ⟦ θ [ δ ]Mor ⟧Mor X Z $ (⟦tsubst⟧Morᵈ Y= δ δᵈ θ θᵈ) ≡ comp (⟦ θ ⟧Mor Y' Z $ θᵈ) (⟦ δ ⟧Mor X Y $ δᵈ) (⟦⟧Mor₀ θ) (⟦⟧Mor₁ δ ∙ Y=)

⟦tsubst⟧Morᵈ refl δ δᵈ ◇ tt = tt
⟦tsubst⟧Morᵈ refl δ δᵈ (θ , u) (θᵈ , uᵈ , θ₁ , u₁ , tt) = (⟦tsubst⟧Morᵈ refl δ δᵈ θ θᵈ , ⟦tsubst⟧Tmᵈ u uᵈ δ δᵈ , ⟦⟧Mor₁ (θ [ δ ]Mor) , (⟦tsubst⟧Tm₁ u uᵈ u₁ δ δᵈ ∙ ! (ap-irr-star (⟦tsubst⟧Mor= refl δ δᵈ θ θᵈ) refl ∙ star-comp)) , tt)

⟦tsubst⟧Mor= refl δ δᵈ ◇ θᵈ = ! (ptmor-unique _ _ (comp₀ ∙ ⟦⟧Mor₀ δ) (comp₁ ∙ ptmor₁))
⟦tsubst⟧Mor= refl δ δᵈ (θ , u) (θᵈ , uᵈ , θ₁ , u₁ , tt) =
 let thing = ! assoc ∙ ap-irr-comp (is-section= (ap ft (comp₁ {f = idC _} {g₀ = ⟦⟧Tm₀ u} {f₁ = id₁} ∙ u₁) ∙ ft-star ∙ ⟦⟧Mor₀ θ) (⟦⟧Tmₛ u) (! comp₁)) refl ∙ id-right (⟦⟧Mor₁ δ) in
  ap-irr-comp (ap-irr-qq (⟦tsubst⟧Mor= refl δ δᵈ θ θᵈ) refl ∙ qq-comp) (! (⟦tsubst⟧Tm= u uᵈ δ δᵈ))
  ∙ assoc {f₁ = starTm₁ _ (ft-star ∙ ⟦⟧Mor₀ θ) _ (⟦⟧Tmₛ u) u₁ _} {g₀ = qq₀}
  ∙ ! (assoc ∙ ap-irr-comp refl (ss-qq ∙ ap-irr-comp (ap-irr-qq thing (comp₁ ∙ u₁)) refl))
