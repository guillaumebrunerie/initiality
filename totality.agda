{-# OPTIONS --prop --allow-unsolved-metas #-}

open import common
open import syntx
open import contextualcat
open import rules

module _ (sC : StructuredCCat) where

open StructuredCCat sC renaming (ccat to C)
open CCat C renaming (Mor to MorC)
open import partialinterpretation sC

{- Predicate saying whether an object "respects" a context in the sense that the types in Γ correspond to their interpretation in X.
   We cannot use (X ≡ ⟦ Γ ⟧) instead because it fails the termination checker somehow. -}

respectsCtx : (X : Ob n) (Γ : Ctx n) → Prop
respectsCtx {zero} X ◇ = Unit
respectsCtx {suc n} X (Γ , A) = respectsCtx (ft X) Γ × Σ (isDefined (⟦ A ⟧Ty (ft X))) (λ Aᵈ → ⟦ A ⟧Ty (ft X) $ Aᵈ ≡ X)


{- Totality of the partial interpretation functions -}

⟦⟧Tyᵈ  : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) → isDefined (⟦ A ⟧Ty X)
⟦⟧Tmᵈ  : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → isDefined (⟦ u ⟧Tm X)
⟦⟧Morᵈ : {Γ : Ctx n} {X : Ob n} {Δ : Ctx m} {Y : Ob m} (r : respectsCtx X Γ) (r' : respectsCtx Y Δ) {δ : Mor n m} (dδ : Γ ⊢ δ ∷> Δ) → isDefined (⟦ δ ⟧Mor X Y)

⟦⟧Ty : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) → Ob (suc n)
⟦⟧Ty {X = X} r {A = A} dA = ⟦ A ⟧Ty X $ ⟦⟧Tyᵈ r dA


{- Various lemmas saying that the interpretation functions are well-behaved -}

⟦⟧Mor₀ : {X : Ob n} {Y : Ob m} (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₀ (⟦ δ ⟧Mor X Y $ δᵈ) ≡ X
⟦⟧Mor₁ : {X : Ob n} {Y : Ob m} (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₁ (⟦ δ ⟧Mor X Y $ δᵈ) ≡ Y

⟦⟧Ty-ft : {X : Ob n} (A : TyExpr n) {Aᵈ : isDefined (⟦ A ⟧Ty X)} → ft (⟦ A ⟧Ty X $ Aᵈ) ≡ X

⟦⟧Tmₛ : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → is-section (⟦ u ⟧Tm X $ uᵈ)
⟦⟧Tm₀ : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → ∂₀ (⟦ u ⟧Tm X $ uᵈ) ≡ X
⟦⟧Tm₁ : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} {A : TyExpr n} {Aᵈ : isDefined (⟦ A ⟧Ty X)} (du : Derivable (Γ ⊢ u :> A)) → ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ ⟦ A ⟧Ty X $ Aᵈ

⟦idMor⟧ᵈ : (X Y : Ob n) → isDefined (⟦ idMor n ⟧Mor X Y)
⟦idMor⟧= : {X : Ob n} → ⟦ idMor n ⟧Mor X X $ ⟦idMor⟧ᵈ X X ≡ id X

--⟦weaken+⟧ᵈ : isDefined (⟦ δ ⟧Mor X Y) → isDefined (⟦ weakenMor δ , var last ⟧Mor X+ Y+

respectsCtxExt : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) (A : TyExpr n) {Aᵈ : isDefined (⟦ A ⟧Ty X)}
              → respectsCtx (⟦ A ⟧Ty X $ Aᵈ) (Γ , A)
respectsCtxExt r A {Aᵈ} rewrite ⟦⟧Ty-ft A {Aᵈ} = r , _ , refl


{- Interpretation of definitional equalities -}

⟦⟧TyEq : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A')) (Aᵈ : isDefined (⟦ A ⟧Ty X)) (A'ᵈ : isDefined (⟦ A' ⟧Ty X))
        → ⟦ A ⟧Ty X $ Aᵈ ≡ ⟦ A' ⟧Ty X $ A'ᵈ
⟦⟧TmEq : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A)) (uᵈ : isDefined (⟦ u ⟧Tm X)) (u'ᵈ : isDefined (⟦ u' ⟧Tm X))
        → ⟦ u ⟧Tm X $ uᵈ ≡ ⟦ u' ⟧Tm X $ u'ᵈ


{- Interpretation of total substitutions -}

⟦tsubst⟧Tyᵈ : {X : Ob n} {Y : Ob m} (A : TyExpr m) {δ : Mor n m}
            → isDefined (⟦ A ⟧Ty Y)
            → isDefined (⟦ δ ⟧Mor X Y)
            → isDefined (⟦ A [ δ ]Ty ⟧Ty X)

⟦tsubst⟧Ty= : {X : Ob n} {Y : Ob m} (A : TyExpr m)
              (Aᵈ : isDefined (⟦ A ⟧Ty Y))
              (δ : Mor n m)
              (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            → ⟦ A [ δ ]Ty ⟧Ty X $ ⟦tsubst⟧Tyᵈ A Aᵈ δᵈ
              ≡ star (⟦ δ ⟧Mor X Y $ δᵈ) (⟦ A ⟧Ty Y $ Aᵈ) (⟦⟧Mor₁ δ ∙ ! (⟦⟧Ty-ft A))

⟦tsubst⟧Tmᵈ : {X : Ob n} {Y : Ob m} (u : TmExpr m) {δ : Mor n m}
            → isDefined (⟦ u ⟧Tm Y)
            → isDefined (⟦ δ ⟧Mor X Y)
            → isDefined (⟦ u [ δ ]Tm ⟧Tm X)

⟦tsubst⟧Tm= : {X : Ob n} {Y : Ob m} (u : TmExpr m)
            (uᵈ : isDefined (⟦ u ⟧Tm Y))
            (δ : Mor n m)
            (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            → ⟦ u [ δ ]Tm ⟧Tm X $ ⟦tsubst⟧Tmᵈ u uᵈ δᵈ
              ≡ ss (comp (⟦ u ⟧Tm Y $ uᵈ) (⟦ δ ⟧Mor X Y $ δᵈ) (⟦⟧Mor₁ δ ∙ ! (⟦⟧Tm₀ u)))


{- Definitions -}

⟦⟧Tyᵈ r UU = tt
⟦⟧Tyᵈ r {A = pi A B} (Pi dA dB) = (⟦⟧Tyᵈ r dA , (⟦⟧Tyᵈ (respectsCtxExt r A) dB) , tt)
⟦⟧Tyᵈ r {A = el v} (El dv) = (⟦⟧Tmᵈ r dv , ⟦⟧Tmₛ v , (⟦⟧Tm₁ r v dv ∙ ap UUStr (! (⟦⟧Tm₀ v))) , tt)

⟦⟧Tmᵈ r (VarLast dA) = tt
⟦⟧Tmᵈ r (VarPrev dA dx) = tt
⟦⟧Tmᵈ r (Conv dA du dA=) = ⟦⟧Tmᵈ r du
⟦⟧Tmᵈ r {u = lam A B u} (Lam dA dB du) =
  (⟦⟧Tyᵈ r dA ,
   ⟦⟧Tmᵈ (respectsCtxExt r A) du ,
   ⟦⟧Tmₛ u , tt)
⟦⟧Tmᵈ r {u = app A B f a} (App dA dB df da) =
  let X+ = ⟦ A ⟧Ty _ $ ⟦⟧Tyᵈ r dA
      r+ = respectsCtxExt r A
  in
  (⟦⟧Tyᵈ r dA ,
   ⟦⟧Tyᵈ r+ dB ,
   ⟦⟧Tmᵈ r df ,
   ⟦⟧Tmₛ f ,
   ⟦⟧Tm₁ r f df ,
   ⟦⟧Tmᵈ r da ,
   ⟦⟧Tmₛ a ,
   (⟦⟧Tm₁ r a da ∙ ! (⟦⟧Ty-ft B)) , tt)

⟦⟧Morᵈ {Δ = ◇} r r' {◇} tt = tt
⟦⟧Morᵈ {Δ = Δ , B} r r' {δ , u} (dδ , du) =
  let δᵈ = ⟦⟧Morᵈ r (fst r') dδ
      Bᵈ = fst (snd r')
  in
  (δᵈ ,
   ⟦⟧Tmᵈ r du ,
   ⟦⟧Mor₁ δ ,
   (⟦⟧Tm₁ r u {Aᵈ = ⟦tsubst⟧Tyᵈ B Bᵈ δᵈ} du ∙ ⟦tsubst⟧Ty= B Bᵈ δ δᵈ ∙ ap2-irr star refl (snd (snd r'))) , tt)

⟦⟧Mor₀ ◇ = ptmor₀
⟦⟧Mor₀ (δ , u) = comp₀ ∙ ⟦⟧Tm₀ u

⟦⟧Mor₁ ◇ = ptmor₁ ∙ ! (pt-unique _)
⟦⟧Mor₁ (δ , u) = comp₁ ∙ qq₁

⟦⟧Ty-ft (pi A B)  = PiStr= ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Ty-ft uu = UUStr=
⟦⟧Ty-ft (el v) = ElStr= ∙ ⟦⟧Tm₀ v

⟦⟧Tmₛ (var x) = varCs x _
⟦⟧Tmₛ (lam A B u) = lamStrs
⟦⟧Tmₛ (app A B f a) = appStrs

⟦⟧Tm₀ (var x) = varC₀ x _
⟦⟧Tm₀ (lam A B u) = lamStr₀ (⟦⟧Tmₛ u) ∙ ap ft (⟦⟧Tm₀ u) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (app A B f a) = appStr₀ (⟦⟧Tmₛ a) _ ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A

⟦⟧Tm₁ r (var last) (VarLast du) = {!varC₁ --TODO!}
⟦⟧Tm₁ r (var (prev k)) (VarPrev du du₁) = {!varC₁ --TODO!}
⟦⟧Tm₁ r u (Conv dA du dA=) = ⟦⟧Tm₁ r u du ∙ ⟦⟧TyEq r dA= (⟦⟧Tyᵈ r dA) _
⟦⟧Tm₁ r (lam A B u) (Lam dA dB du) = lamStr₁ ∙ ap PiStr (⟦⟧Tm₁ (respectsCtxExt r A) u du)
⟦⟧Tm₁ {X = X} r (app A B f a) (App dA dB df da) = appStr₁ ∙ ! (⟦tsubst⟧Ty= B (⟦⟧Tyᵈ (respectsCtxExt r A) dB) _ (⟦idMor⟧ᵈ X (ft (⟦ A ⟧Ty X $ ⟦⟧Tyᵈ r dA)) , {!stuff!}) ∙ {!⟦ a ⟧Tm = ⟦ idMor , a ⟧Mor!})

⟦idMor⟧ᵈ {zero} X Y = tt
⟦idMor⟧ᵈ {suc n} X Y = ({!weakening defined!} , tt , ⟦⟧Mor₁ (weakenMor (idMor n)) , {!!} , tt)

⟦idMor⟧= {zero} = ! (ptmor-unique _ (id _) id₀ (id₁ ∙ pt-unique _))
⟦idMor⟧= {suc n} = {!interpretation of weakening!}


⟦⟧TyEq r (TySymm dA=) Aᵈ A'ᵈ = ! (⟦⟧TyEq r dA= A'ᵈ Aᵈ)
⟦⟧TyEq r (TyTran dB dA= dB=) Aᵈ A'ᵈ = ⟦⟧TyEq r dA= Aᵈ (⟦⟧Tyᵈ r dB) ∙ ⟦⟧TyEq r dB= (⟦⟧Tyᵈ r dB) A'ᵈ
⟦⟧TyEq r {A = pi A B} {A' = pi A' B'} (PiCong dA dA= dB=) (Aᵈ , Bᵈ , _) (A'ᵈ , B'ᵈ , _) rewrite ! (⟦⟧TyEq r dA= Aᵈ A'ᵈ) | ! (⟦⟧TyEq (respectsCtxExt r A) dB= Bᵈ B'ᵈ)
  = refl
⟦⟧TyEq r UUCong Aᵈ A'ᵈ = refl
⟦⟧TyEq r (ElCong dv=) (vᵈ , _) (v'ᵈ , _) rewrite ⟦⟧TmEq r dv= vᵈ v'ᵈ = refl

⟦⟧TmEq r (VarLastCong dA) tt tt = refl
⟦⟧TmEq r (VarPrevCong {k = k} {k' = k'} dA dx) tt tt = ap-irr2 weakenCTm (⟦⟧TmEq (fst r) dx tt tt) {b = weakenCTm^s k (var-unweakened k (ft _)) (var-unweakeneds k (ft _)) (var-unweakened₀ k (ft _))} {b' = weakenCTm^s k' (var-unweakened k' (ft _)) (var-unweakeneds k' (ft _)) (var-unweakened₀ k' (ft _))} {c = weakenCTm^₀ k (var-unweakened k (ft _)) (var-unweakeneds k (ft _)) (var-unweakened₀ k (ft _))} {c' = weakenCTm^₀ k' (var-unweakened k' (ft _)) (var-unweakeneds k' (ft _)) (var-unweakened₀ k' (ft _))}
⟦⟧TmEq r (TmSymm du=) uᵈ u'ᵈ = ! (⟦⟧TmEq r du= u'ᵈ uᵈ)
⟦⟧TmEq r (TmTran du= du'=) uᵈ u'ᵈ = ⟦⟧TmEq r du= uᵈ {!add as argument to TmTran!} ∙ ⟦⟧TmEq r du'= {!add as argument to TmTran!} u'ᵈ
⟦⟧TmEq r (ConvEq dA' du= dA=) uᵈ u'ᵈ = ⟦⟧TmEq r du= uᵈ u'ᵈ
⟦⟧TmEq r {u = lam A B u} (LamCong dA dA= dB= du=) (Aᵈ , uᵈ , utmᵈ , _) (A'ᵈ , u'ᵈ , utm'ᵈ , _)
  rewrite ! (⟦⟧TyEq r dA= Aᵈ A'ᵈ)
        | ! (⟦⟧TmEq {X = ⟦ A ⟧Ty _ $ Aᵈ} (respectsCtxExt r A) du= uᵈ u'ᵈ) = refl
⟦⟧TmEq r {u = app A B f a} (AppCong dA dA= dB= df= da=) (Aᵈ , Bᵈ , fᵈ , _ , _ , aᵈ , _) (A'ᵈ , B'ᵈ , f'ᵈ , _ , _ , a'ᵈ , _)
  rewrite ! (⟦⟧TyEq r dA= Aᵈ A'ᵈ)
           | ⟦⟧TyEq {X = ⟦ A ⟧Ty _ $ Aᵈ} (respectsCtxExt r A) dB= Bᵈ B'ᵈ
           | ⟦⟧TmEq r df= fᵈ f'ᵈ
           | ⟦⟧TmEq r da= aᵈ a'ᵈ = refl
⟦⟧TmEq r (Beta dA dB du da) (Aᵈ , Bᵈ , (_ , _ , uᵈ , _) , aᵈ , _) u'ᵈ = {!betaStr ∙ ?!}


⟦tsubst⟧Tyᵈ (pi A B) {δ = δ} (Aᵈ , Bᵈ , tt) δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δᵈ ,
   ⟦tsubst⟧Tyᵈ B Bᵈ {!⟦ weakenMor δ , var last ⟧ is defined!}
  , tt)
⟦tsubst⟧Tyᵈ uu tt δᵈ = tt
⟦tsubst⟧Tyᵈ (el v) {δ = δ} (vᵈ , vs , v₁ , tt) δᵈ =
  (⟦tsubst⟧Tmᵈ v vᵈ δᵈ ,
   ⟦⟧Tmₛ (v [ _ ]Tm) ,
   {!(ap ∂₁ (⟦tsubst⟧Tm= X Y v vᵈ _ δᵈ) ∙ (ss₁ ∙ {!!}) ∙ ap UUStr (ap ∂₀ (! (⟦tsubst⟧Tm= X Y v vᵈ _ δᵈ))))!} , tt)

⟦tsubst⟧Ty= (pi A B) (Aᵈ , Bᵈ , tt) δ δᵈ = ! (PiStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) {p = (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A) ∙ ! (⟦⟧Mor₁ δ)} ∙ {!annoying recursive calls!})
⟦tsubst⟧Ty= uu Aᵈ δ δᵈ = ! (UUStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) {p = ! (⟦⟧Mor₁ δ)} ∙ ap UUStr (⟦⟧Mor₀ δ))
⟦tsubst⟧Ty= (el v) (vᵈ , _) δ δᵈ = ! (ElStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) {p = ⟦⟧Tm₀ v ∙ ! (⟦⟧Mor₁ δ)} ∙ ap-irr2 ElStr (! (⟦tsubst⟧Tm= v vᵈ δ δᵈ)))

⟦tsubst⟧Tmᵈ (var ()) {◇} uᵈ δᵈ
⟦tsubst⟧Tmᵈ (var last) {δ , u} _ (_ , uᵈ , _) = uᵈ
⟦tsubst⟧Tmᵈ (var (prev x)) {δ , u} uᵈ (δᵈ , _) = ⟦tsubst⟧Tmᵈ (var x) tt δᵈ
⟦tsubst⟧Tmᵈ (lam A B u) {δ = δ} (Aᵈ , uᵈ , p) δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δᵈ ,
   ⟦tsubst⟧Tmᵈ u uᵈ {!!} ,
   ⟦⟧Tmₛ (u [ weakenMor δ , var last ]Tm) , tt)
⟦tsubst⟧Tmᵈ (app A B f a) {δ = δ} (Aᵈ , Bᵈ , fᵈ , fs , f₁ , aᵈ , as , a₁ , tt) δᵈ =
  (⟦tsubst⟧Tyᵈ A Aᵈ δᵈ ,
   ⟦tsubst⟧Tyᵈ B Bᵈ {! !} ,
   ⟦tsubst⟧Tmᵈ f fᵈ δᵈ ,
   ⟦⟧Tmₛ (f [ δ ]Tm) ,
   {!!} ,
   ⟦tsubst⟧Tmᵈ a aᵈ δᵈ ,
   ⟦⟧Tmₛ (a [ δ ]Tm) ,
   {!a₁ ?!} , tt)

⟦tsubst⟧Tm= (var x) uᵈ δ δᵈ = {!!}
⟦tsubst⟧Tm= (lam A B u) (Aᵈ , uᵈ , _) δ δᵈ = ! (lamStrNat (⟦ δ ⟧Mor _ _ $ δᵈ) ∙ ap-irr lamStr (! (⟦tsubst⟧Tm= u uᵈ (weakenMor δ , var last) {!!} ∙ ap ss (ap2-irr comp refl {!!}))))
⟦tsubst⟧Tm= (app A B f a) uᵈ δ δᵈ = {!!}

{- Additional results about contexts, context morphisms, and equality -}

respects⟦⟧Ctx : {Γ : Ctx n} {Γᵈ : isDefined (⟦ Γ ⟧Ctx)} → respectsCtx (⟦ Γ ⟧Ctx $ Γᵈ) Γ
respects⟦⟧Ctx {Γ = ◇} = tt
respects⟦⟧Ctx {Γ = Γ , A} {Γᵈ = Γᵈ , Aᵈ , tt} rewrite ⟦⟧Ty-ft A {Aᵈ} = (respects⟦⟧Ctx , Aᵈ , refl)

⟦⟧Ctxᵈ : {Γ : Ctx n} (dΓ : ⊢ Γ) → isDefined (⟦ Γ ⟧Ctx)
⟦⟧Ctxᵈ {Γ = ◇} tt = tt
⟦⟧Ctxᵈ {Γ = Γ , A} (dΓ , dA) = let Γᵈ = ⟦⟧Ctxᵈ dΓ in (Γᵈ , ⟦⟧Tyᵈ respects⟦⟧Ctx dA , tt)

⟦⟧CtxEq : {Γ Γ' : Ctx n} (dΓ= : ⊢ Γ == Γ') {Γᵈ : isDefined (⟦ Γ ⟧Ctx)} {Γ'ᵈ : isDefined (⟦ Γ' ⟧Ctx)}
        → ⟦ Γ ⟧Ctx $ Γᵈ ≡ ⟦ Γ' ⟧Ctx $ Γ'ᵈ
⟦⟧CtxEq {Γ = ◇} {◇} _ = refl
⟦⟧CtxEq {Γ = Γ , A} {Γ' , A'} (dΓ= , _ , _ , dA= , _) {Γᵈ = Γᵈ , Aᵈ , tt} {Γ'ᵈ = Γ'ᵈ , A'ᵈ , tt}
  rewrite ! (⟦⟧CtxEq dΓ= {Γᵈ} {Γ'ᵈ}) | ⟦⟧TyEq respects⟦⟧Ctx dA= Aᵈ A'ᵈ = refl

⟦⟧MorEq : {Γ Γ' : Ctx n} {Δ Δ' : Ctx m} {δ δ' : Mor n m} (X : Ob n) (Y : Ob m) (r : respectsCtx X Γ) (dδ= : Γ ⊢ δ == δ' ∷> Δ) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} {δ'ᵈ : isDefined (⟦ δ' ⟧Mor X Y)}
        → ⟦ δ ⟧Mor X Y $ δᵈ ≡ ⟦ δ' ⟧Mor X Y $ δ'ᵈ
⟦⟧MorEq {Δ = ◇} {δ = ◇} {◇} X Y r tt = refl
⟦⟧MorEq {Γ' = Γ'} {Δ = Δ , B} {δ = δ , u} {δ' , u'} X Y r (dδ= , du=) = ap2-irr comp (ap2-irr qq (⟦⟧MorEq {Γ' = Γ'} {Δ' = Δ} X (ft Y) r dδ=) refl) (⟦⟧TmEq r du= _ _)
