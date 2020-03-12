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

{-
In this file we prove that weakening commutes with the partial interpretation function in the
appropriate sense. Unfortunately we cannot do it as a special case of total substitution because
⟦tsubst⟧Ty+ᵈ calls ⟦weaken⟧Mor+ᵈ on δ, whereas the induction defining ⟦tsubst⟧Tyᵈ is on A. There is
no similar issue defining ⟦weaken⟧ first (as there is no δ that would mess up the termination) and
then ⟦tsubst⟧ (which uses ⟦weaken⟧ which is already defined).
-}

{- Interpreation of equality of weakening, if defined -}


⟦weaken⟧Ty='' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob n} {Y : Ob (n -WeakPos k)} (A : TyExpr n)
              → (Aᵈ : isDefined (⟦ A ⟧Ty X))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
              → {w₁ : _}
              → star (qq^ k X+= X=) (⟦ A ⟧Ty X $ Aᵈ) (⟦⟧Ty-ft A) qq^₁ ≡ ⟦ weakenTy' k A ⟧Ty Z $ w₁

⟦weaken⟧Tm='' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr n)
              → (uᵈ : isDefined (⟦ u ⟧Tm X))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
              → {w₁ : _}
              → starTm (qq^ k X+= X=) (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' k u ⟧Tm Z $ w₁

{- specializations -} 

⟦weaken⟧Ty+=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -WeakPos k)} (A : TyExpr (suc n))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
              → {w₁ : _}
              → star+ (qq^ k X+= X=) (⟦ A ⟧Ty X' $ Aᵈ) (⟦⟧Ty-ft A) p qq^₁ ≡ ⟦ weakenTy' (prev k) A ⟧Ty Z $ w₁
⟦weaken⟧Ty+=' k A Aᵈ X+= X= refl Y= = ap-irr-star (! qq^prev) refl ∙ ⟦weaken⟧Ty='' (prev k) A Aᵈ X+= X= Y=

⟦weaken⟧Tm+=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
              → {w₁ : _}
              → starTm+ (qq^ k X+= X=) p (⟦ u ⟧Tm X' $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' (prev k) u ⟧Tm Z $ w₁
⟦weaken⟧Tm+=' k u uᵈ X+= X= refl Y= = ap ss (ap-irr-comp refl (! qq^prev)) ∙ ⟦weaken⟧Tm='' (prev k) u uᵈ X+= X= Y=


⟦weaken⟧Tm++=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {Y : Ob (n -WeakPos k)} {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} (u : TmExpr (suc (suc n)))
               → (uᵈ : isDefined (⟦ u ⟧Tm X))
               → (X+= : ft X+ ≡ Y) (X''= : ft^ k X'' ≡ Y) {Z : Ob (suc (suc (suc n)))} (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (Y= : star+ (qq^ k X+= X''=) X X= X'= qq^₁ ≡ Z)
               → {w₁ : _}
               → starTm++ (qq^ k X+= X''=) X= X'= (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' (prev (prev k)) u ⟧Tm Z $ w₁
⟦weaken⟧Tm++=' k u uᵈ X+= X''= refl refl Y= = ap ss (ap-irr-comp refl (ap-irr-qq (! qq^prev) refl)) ∙ ⟦weaken⟧Tm+=' (prev k) u uᵈ X+= X''= refl (ap-irr-star qq^prev refl ∙ Y=)


⟦weaken⟧Ty+++=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {Y : Ob (n -WeakPos k)} {X''' : Ob (suc (suc (suc n)))} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc (suc n))))
                → (Aᵈ : isDefined (⟦ A ⟧Ty X'''))
                → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc (suc (suc n))))} (X'''= : ft X''' ≡ X'') (X''= : ft X'' ≡ X') (X'= : ft X' ≡ X) (Z= : star++ (qq^ k X+= X=)  X''' X'''= X''= X'= qq^₁ ≡ Z)
                → {w₁ : _}
               → star+++ (qq^ k X+= X=) (⟦ A ⟧Ty X''' $ Aᵈ) (⟦⟧Ty-ft A) X'''= X''= X'= qq^₁ ≡ ⟦ weakenTy' (prev (prev (prev k))) A ⟧Ty Z $ w₁
⟦weaken⟧Ty+++=' k A Aᵈ X+= X= refl refl refl Z= = ap-irr-star (! (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq qq^prev refl) refl)) refl ∙ ⟦weaken⟧Ty='' (prev (prev (prev k))) A Aᵈ X+= X= (ap-irr-star (qq^prev ∙ ap-irr-qq qq^prev refl) refl ∙ Z=)


⟦weaken⟧Ty='' k (uu i) _ X+= X= Z= =
  UUStrNat qq^₀ ∙ ap-irr-UUStr Z=
⟦weaken⟧Ty='' k (el i v) (vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  ElStrNat qq^₀
  ∙ ap-irr-ElStr Z= (⟦weaken⟧Tm='' k v vᵈ X+= X= Z=)
⟦weaken⟧Ty='' k (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  SumStrNat qq^₀
  ∙ ap-irr-SumStr Z=
                  (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty='' k B Bᵈ X+= X= Z=)
⟦weaken⟧Ty='' k (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  PiStrNat qq^₀
  ∙ ap-irr-PiStr Z=
                 (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                 (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=))
⟦weaken⟧Ty='' k (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  SigStrNat qq^₀
  ∙ ap-irr-SigStr Z=
                  (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=))
⟦weaken⟧Ty='' k empty _ X+= X= Z= = EmptyStrNat (qq^₀ ∙ Z=)
⟦weaken⟧Ty='' k unit _ X+= X= Z= = UnitStrNat (qq^₀ ∙ Z=)
⟦weaken⟧Ty='' k nat _ X+= X= Z= =
  NatStrNat qq^₀ ∙
  ap NatStr Z=
⟦weaken⟧Ty='' k (id A u v) (Aᵈ , A= , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  IdStrNat qq^₀
  ∙ ap-irr-IdStr Z= (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=) (⟦weaken⟧Tm='' k u uᵈ X+= X= Z=) (⟦weaken⟧Tm='' k v vᵈ X+= X= Z=)


⟦weaken⟧Tm='' {n = suc n} last (var x) tt X+= refl refl = star-varCL'' {g₀ = pp^₀ x _} ∙ ap ss (ap-irr-comp refl qq^last ∙ ! ((pp^prev {k = x} X+=)))
⟦weaken⟧Tm='' {n = suc n} (prev k) (var last) tt X+= refl Z= = star-varCL' ∙ ap ss qq^prev ∙ ap ss (! (id-left qq₀) ∙ ap-irr-comp refl (ap idC Z=) {f₁' = id₁ ∙ ! Z=}) ∙ ! ss-comp
⟦weaken⟧Tm='' {n = suc n} (prev k) (var (prev x)) tt X+= refl Z= = star-varCL'' {g₀ = pp^₀ (prev x) _} ∙ ap ss (ap-irr-comp (pp^prev refl) qq^prev ∙ assoc ∙ ap-irr-comp refl (pp-qq ∙ ap-irr-comp refl (ap pp Z=)) ∙ ! (assoc {f₁ = pp₁ ∙ ap ft (! Z=) ∙ ft-star ∙ qq^₀} {g₀ = qq^₀} {h₀ = pp^₀ x _})) ∙ ! (star-varCL'' {g₀ = comp₀ ∙ qq^₀}) ∙ ap ss (ap-irr-comp (! star-varCL'' ∙ ⟦weaken⟧Tm='' k (var x) tt X+= refl refl) refl) ∙ star-varCL'' ∙ ap ss (! (pp^prev {k = weakenVar' k x} (ap ft (! Z=) ∙ ft-star ∙ qq^₀)))

⟦weaken⟧Tm='' k (uu i) tt X+= X= Z= =
  uuStrNat qq^₀
  ∙ ap (uuStr i) Z=

⟦weaken⟧Tm='' k (sum i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  sumStrNat qq^₀
  ∙ ap-irr-sumStr Z=
                  (⟦weaken⟧Tm='' k a aᵈ X+= X= Z=)
                  (⟦weaken⟧Tm='' k b bᵈ X+= X= Z=)
⟦weaken⟧Tm='' k (inl A B a) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , tt) X+= X= Z= =
  inlStrNat qq^₀
  ∙ ap-irr-inlStr Z=
                  (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty='' k B Bᵈ X+= X= Z=)
                  (⟦weaken⟧Tm='' k a aᵈ X+= X= Z=)
⟦weaken⟧Tm='' k (inr A B b) (Aᵈ , A= , Bᵈ , B= , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  inrStrNat qq^₀
  ∙ ap-irr-inrStr Z=
                  (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty='' k B Bᵈ X+= X= Z=)
                  (⟦weaken⟧Tm='' k b bᵈ X+= X= Z=)

⟦weaken⟧Tm='' k (match A B C da db u) (Aᵈ , A= , Bᵈ , B= , Cᵈ , C= , daᵈ , daₛ , da₁ , dbᵈ , dbₛ , db₁ , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  matchStrNat qq^₀
  ∙ ap-irr-matchStr Z=
                    (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                    (⟦weaken⟧Ty='' k B Bᵈ X+= X= Z=)
                    (⟦weaken⟧Ty+=' k C Cᵈ X+= X= SumStr= (SumStrNat qq^₀
                                                         ∙ ap-irr-SumStr Z=
                                                                         (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                                                                         (⟦weaken⟧Ty='' k B Bᵈ X+= X= Z=)))
                    (⟦weaken⟧Tm+=' k da daᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=) )
                    (⟦weaken⟧Tm+=' k db dbᵈ X+= X= (⟦⟧Ty-ft B) (⟦weaken⟧Ty='' k B Bᵈ X+= X= Z=))
                    (⟦weaken⟧Tm='' k u uᵈ X+= X= Z=)

⟦weaken⟧Tm='' k (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  piStrNat qq^₀ 
  ∙ ap-irr-piStr Z=
                 (⟦weaken⟧Tm='' k a aᵈ X+= X= Z=)
                 (⟦weaken⟧Tm+=' k b bᵈ X+= X= ElStr= (ElStrNat qq^₀ ∙ ap-irr-ElStr Z= (⟦weaken⟧Tm='' k a aᵈ X+= X= Z=)))
⟦weaken⟧Tm='' k (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  lamStrNat qq^₀ 
  ∙ ap-irr-lamStr Z=
                  (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=))
                  (⟦weaken⟧Tm+=' k u uᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=))
⟦weaken⟧Tm='' k (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) X+= X= Z= =
  appStrNat qq^₀ 
  ∙ ap-irr-appStr Z=
                  (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=))
                  (⟦weaken⟧Tm='' k f fᵈ X+= X= Z=)
                  (⟦weaken⟧Tm='' k a aᵈ X+= X= Z=)

⟦weaken⟧Tm='' k (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  sigStrNat qq^₀ 
  ∙ ap-irr-sigStr Z=
                  (⟦weaken⟧Tm='' k a aᵈ X+= X= Z=)
                  (⟦weaken⟧Tm+=' k b bᵈ X+= X= ElStr= (ElStrNat qq^₀
                                                      ∙ ap-irr-ElStr Z= (⟦weaken⟧Tm='' k a aᵈ X+= X= Z=)))
⟦weaken⟧Tm='' k (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  pairStrNat qq^₀ 
  ∙ ap-irr-pairStr Z=
                   (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                   (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=))
                   (⟦weaken⟧Tm='' k a aᵈ X+= X= Z=)
                   (⟦weaken⟧Tm='' k b bᵈ X+= X= Z=)
⟦weaken⟧Tm='' k (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  pr1StrNat qq^₀ 
  ∙ ap-irr-pr1Str Z=
                  (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=))
                  (⟦weaken⟧Tm='' k u uᵈ X+= X= Z=)
⟦weaken⟧Tm='' k (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  pr2StrNat qq^₀ 
  ∙ ap-irr-pr2Str Z=
                  (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                  (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=))
                  (⟦weaken⟧Tm='' k u uᵈ X+= X= Z=)

⟦weaken⟧Tm='' k (empty i) tt X+= X= Z= =
  emptyStrNat qq^₀
  ∙ ap (emptyStr i) Z=
⟦weaken⟧Tm='' k (emptyelim A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  emptyelimStrNat qq^₀
  ∙ ap-irr-emptyelimStr Z=
                        (⟦weaken⟧Ty+=' k A Aᵈ X+= X= EmptyStr= (⟦weaken⟧Ty='' k empty tt X+= X= Z=))
                        (⟦weaken⟧Tm='' k u uᵈ X+= X= Z=)
                        
⟦weaken⟧Tm='' k (unit i) tt X+= X= Z= =
  unitStrNat qq^₀
  ∙ ap (unitStr i) Z=
⟦weaken⟧Tm='' k tt tt X+= X= Z= =
  ttStrNat (qq^₀ ∙ Z=)
⟦weaken⟧Tm='' k (unitelim A dtt u) (Aᵈ , A= , dttᵈ , dttₛ , dtt₁ , uᵈ , uₛ , u₁) X+= X= Z= =
  unitelimStrNat qq^₀
  ∙ ap-irr-unitelimStr Z=
                       (⟦weaken⟧Ty+=' k A Aᵈ X+= X= UnitStr= (⟦weaken⟧Ty='' k unit tt X+= X= Z=))
                       (⟦weaken⟧Tm='' k dtt dttᵈ X+= X= Z=)
                       (⟦weaken⟧Tm='' k u uᵈ X+= X= Z=)

⟦weaken⟧Tm='' k (nat i) tt X+= X= Z= =
  natStrNat qq^₀
  ∙ ap (natStr i) Z=
⟦weaken⟧Tm='' k zero tt X+= X= Z= =
  zeroStrNat qq^₀
  ∙ ap zeroStr Z=
⟦weaken⟧Tm='' k (suc u) (uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  sucStrNat qq^₀
  ∙  ap-irr-sucStr Z=
                   (⟦weaken⟧Tm='' k u uᵈ X+= X= Z=)
⟦weaken⟧Tm='' k (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  natelimStrNat qq^₀
  ∙ ap-irr-natelimStr Z=
                      (⟦weaken⟧Ty+=' k P Pᵈ X+= X= NatStr= (⟦weaken⟧Ty='' k nat tt X+= X= Z=)) 
                      (⟦weaken⟧Tm='' k dO dOᵈ X+= X= Z=)
                      (⟦weaken⟧Tm++=' k dS dSᵈ X+= X= (⟦⟧Ty-ft P) NatStr= (⟦weaken⟧Ty+=' k P Pᵈ X+= X= NatStr= (⟦weaken⟧Ty='' k nat tt X+= X= Z=)))
                      (⟦weaken⟧Tm='' k u uᵈ X+= X= Z=)

⟦weaken⟧Tm='' k (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  idStrNat qq^₀ 
  ∙ ap-irr-idStr Z=
                 (⟦weaken⟧Tm='' k a aᵈ X+= X= Z=)
                 (⟦weaken⟧Tm='' k u uᵈ X+= X= Z=)
                 (⟦weaken⟧Tm='' k v vᵈ X+= X= Z=)
⟦weaken⟧Tm='' k (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  reflStrNat qq^₀
  ∙ ap-irr-reflStr Z=
                   (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                   (⟦weaken⟧Tm='' k u uᵈ X+= X= Z=)
⟦weaken⟧Tm='' k (jj A P d a b p) (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt) X+= X= Z= =
  jjStrNat qq^₀
  ∙ ap-irr-jjStr Z=
                 (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)
                 (⟦weaken⟧Ty+++=' k P Pᵈ X+= X= T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat qq^₀ ∙ ap-irr-T-ftP Z= (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=)))
                 (⟦weaken⟧Tm+=' k d dᵈ X+= X= A= (⟦weaken⟧Ty='' k A Aᵈ X+= X= Z=))
                 (⟦weaken⟧Tm='' k a aᵈ X+= X= Z=)
                 (⟦weaken⟧Tm='' k b bᵈ X+= X= Z=)
                 (⟦weaken⟧Tm='' k p pᵈ X+= X= Z=)


{- Interpretation of weakening -}

⟦weaken⟧Tyᵈ' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob n} {Y : Ob (n -WeakPos k)} (A : TyExpr n)
             → isDefined (⟦ A ⟧Ty X)
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → isDefined (⟦ weakenTy' k A ⟧Ty Z)

⟦weaken⟧Tmᵈ' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr n)
             → isDefined (⟦ u ⟧Tm X)
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → isDefined (⟦ weakenTm' k u ⟧Tm Z)

{- helper function dealing with equality and codomain of the interpretation of a weakening -}

⟦weaken⟧Ty=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob n} {Y : Ob (n -WeakPos k)} (A : TyExpr n)
               → (Aᵈ : isDefined (⟦ A ⟧Ty X))
               → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
               → star (qq^ k X+= X=) (⟦ A ⟧Ty X $ Aᵈ) (⟦⟧Ty-ft A) qq^₁ ≡ ⟦ weakenTy' k A ⟧Ty Z $ ⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z=
⟦weaken⟧Ty=' k A Aᵈ X+= X= Z= = ⟦weaken⟧Ty='' k A Aᵈ X+= X= Z= {w₁ = ⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z=}


⟦weaken⟧Tm=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr n)
              → (uᵈ : isDefined (⟦ u ⟧Tm X))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
              → starTm (qq^ k X+= X=) (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' k u ⟧Tm Z $ ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z=
⟦weaken⟧Tm=' k u uᵈ X+= X= Z= = ⟦weaken⟧Tm='' k u uᵈ X+= X= Z= {w₁ = ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z=}

⟦weaken⟧Tm₁' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr n)
             → (uᵈ : isDefined (⟦ u ⟧Tm X))
             → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc n)} (Z= : star^ k X+ X X+= X= ≡ Z)
             → {∂₁u : Ob (suc n)} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ ∂₁u)
             → ∂₁ (⟦ weakenTm' k u ⟧Tm Z $ ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z=) ≡ star (qq^ k X+= X=) ∂₁u (⟦⟧Tm₁-ft u u₁) qq^₁
⟦weaken⟧Tm₁' k u uᵈ X+= X= Y= u₁ = ap ∂₁ (! (⟦weaken⟧Tm=' k u uᵈ X+= X= Y=)) ∙ starTm₁ _ (⟦⟧Tm₁-ft u u₁) _ (⟦⟧Tmₛ u) u₁ qq^₁


{- We prove first a bunch of special cases, using the lemmas above -}

{- Weakening at [prev k] -}

⟦weaken⟧Ty+ᵈ' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -WeakPos k)} (A : TyExpr (suc n))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (X'= : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' X'= qq^₁ ≡ Z)
              → isDefined (⟦ weakenTy' (prev k) A ⟧Ty Z)
⟦weaken⟧Ty+ᵈ' k A Aᵈ X+= X= refl Y= = ⟦weaken⟧Tyᵈ' (prev k) A Aᵈ X+= X= Y=

-- ⟦weaken⟧Ty+=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -WeakPos k)} (A : TyExpr (suc n))
--               → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
--               → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
--               → star+ (qq^ k X+= X=) (⟦ A ⟧Ty X' $ Aᵈ) (⟦⟧Ty-ft A) p qq^₁ ≡ ⟦ weakenTy' (prev k) A ⟧Ty Z $ ⟦weaken⟧Ty+ᵈ' k A Aᵈ X+= X= p Y=
-- ⟦weaken⟧Ty+=' k A Aᵈ X+= X= refl Y= = ap-irr-star (! qq^prev) refl ∙ ⟦weaken⟧Ty=' (prev k) A Aᵈ X+= X= Y=

⟦weaken⟧Tm+ᵈ' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
              → isDefined (⟦ weakenTm' (prev k) u ⟧Tm Z)
⟦weaken⟧Tm+ᵈ' k u uᵈ X+= X= refl Y= = ⟦weaken⟧Tmᵈ' (prev k) u uᵈ X+= X= Y=

-- ⟦weaken⟧Tm+=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X' : Ob (suc n)} {X : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr (suc n))
--               → (uᵈ : isDefined (⟦ u ⟧Tm X'))
--               → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (qq^ k X+= X=) X' p qq^₁ ≡ Z)
--               → starTm+ (qq^ k X+= X=) p (⟦ u ⟧Tm X' $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' (prev k) u ⟧Tm Z $ ⟦weaken⟧Tm+ᵈ' k u uᵈ X+= X= p Y=
-- ⟦weaken⟧Tm+=' k u uᵈ X+= X= refl Y= = ap ss (ap-irr-comp refl (! qq^prev)) ∙ ⟦weaken⟧Tm=' (prev k) u uᵈ X+= X= Y=

⟦weaken⟧Tm+₁' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} {Y : Ob (n -WeakPos k)} (u : TmExpr (suc n))
              → (uᵈ : isDefined (⟦ u ⟧Tm X'))
              → (X+= : ft X+ ≡ Y) (X''= : ft^ k X'' ≡ Y) {Z : Ob (suc (suc n))}
              → (X= : ft X ≡ X')
              → (X'= : ft X' ≡ X'')
              → (Z= : star (qq^ k X+= X''=) X' X'= qq^₁ ≡ Z)
              → (u₁ : ∂₁ (⟦ u ⟧Tm X' $ uᵈ) ≡ X)
              → ∂₁ (⟦ weakenTm' (prev k) u ⟧Tm Z $ ⟦weaken⟧Tm+ᵈ' k u uᵈ X+= X''= X'= Z=) ≡ star+ (qq^ k X+= X''=) X X= X'= qq^₁
⟦weaken⟧Tm+₁' k u uᵈ X+= X''= refl refl Z= u₁ = ⟦weaken⟧Tm₁' (prev k) u uᵈ X+= X''= Z= u₁ ∙ ap-irr-star qq^prev refl

{- Weakening at [prev (prev k)] -}

⟦weaken⟧Tm++ᵈ' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {Y : Ob (n -WeakPos k)} {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} (u : TmExpr (suc (suc n)))
               → (uᵈ : isDefined (⟦ u ⟧Tm X))
               → (X+= : ft X+ ≡ Y) (X''= : ft^ k X'' ≡ Y) {Z : Ob (suc (suc (suc n)))} (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (Y= : star+ (qq^ k X+= X''=) X X= X'= qq^₁ ≡ Z)
               → isDefined (⟦ weakenTm' (prev (prev k)) u ⟧Tm Z)
⟦weaken⟧Tm++ᵈ' k u uᵈ X+= X''= refl refl Y= = ⟦weaken⟧Tm+ᵈ' (prev k) u uᵈ X+= X''= refl (ap-irr-star qq^prev refl ∙ Y=)

-- ⟦weaken⟧Tm++=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {Y : Ob (n -WeakPos k)} {X : Ob (suc (suc n))} {X' : Ob (suc n)} {X'' : Ob n} (u : TmExpr (suc (suc n)))
--                → (uᵈ : isDefined (⟦ u ⟧Tm X))
--                → (X+= : ft X+ ≡ Y) (X''= : ft^ k X'' ≡ Y) {Z : Ob (suc (suc (suc n)))} (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (Y= : star+ (qq^ k X+= X''=) X X= X'= qq^₁ ≡ Z)
--                → starTm++ (qq^ k X+= X''=) X= X'= (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) qq^₁ ≡ ⟦ weakenTm' (prev (prev k)) u ⟧Tm Z $ ⟦weaken⟧Tm++ᵈ' k u uᵈ X+= X''= X= X'= Y=
-- ⟦weaken⟧Tm++=' k u uᵈ X+= X''= refl refl Y= = ap ss (ap-irr-comp refl (ap-irr-qq (! qq^prev) refl)) ∙ ⟦weaken⟧Tm+=' (prev k) u uᵈ X+= X''= refl (ap-irr-star qq^prev refl ∙ Y=)

⟦weaken⟧Tm++₁' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {Y : Ob (n -WeakPos k)} {X : Ob (suc (suc (suc n))) } {X' : Ob (suc (suc n))} {X'' : Ob (suc n)} {X''' : Ob n} (u : TmExpr (suc (suc n)))
               → (uᵈ : isDefined (⟦ u ⟧Tm X'))
               → (X+= : ft X+ ≡ Y) (X'''= : ft^ k X''' ≡ Y) {Z : Ob (suc (suc (suc n)))}
               → (X= : ft X ≡ X') (X'= : ft X' ≡ X'') (X''= : ft X'' ≡ X''')
               → (Z= : star+ (qq^ k X+= X'''=) X' X'= X''= qq^₁ ≡ Z)
               → (u₁ : ∂₁ (⟦ u ⟧Tm X' $ uᵈ) ≡ X)
               → ∂₁ (⟦ weakenTm' (prev (prev k)) u ⟧Tm Z $ ⟦weaken⟧Tm++ᵈ' k u uᵈ X+= X'''= X'= X''= Z=) ≡ star++ (qq^ k X+= X'''=) X X= X'= X''= qq^₁
⟦weaken⟧Tm++₁' k u uᵈ X+= X'''= refl refl refl Y= u₁ = ⟦weaken⟧Tm+₁' (prev k) u uᵈ X+= X'''= refl refl (ap-irr-star qq^prev refl ∙ Y=) u₁ ∙ ap-irr-star (ap-irr-qq qq^prev refl) refl

{- Weakening at [prev (prev (prev k))] -}

⟦weaken⟧Ty+++ᵈ' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {Y : Ob (n -WeakPos k)} {X''' : Ob (suc (suc (suc n)))} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc (suc n))))
                → (Aᵈ : isDefined (⟦ A ⟧Ty X'''))
                → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc (suc (suc n))))} (X'''= : ft X''' ≡ X'') (X''= : ft X'' ≡ X') (X'= : ft X' ≡ X) (Z= : star++ (qq^ k X+= X=)  X''' X'''= X''= X'= qq^₁ ≡ Z)
               → isDefined (⟦ weakenTy' (prev (prev (prev k))) A ⟧Ty Z)
⟦weaken⟧Ty+++ᵈ' k A Aᵈ X+= X= refl refl refl Z= = ⟦weaken⟧Tyᵈ' (prev (prev (prev k))) A Aᵈ X+= X= (ap-irr-star (qq^prev ∙ ap-irr-qq qq^prev refl) refl ∙ Z=)

-- ⟦weaken⟧Ty+++=' : (k : WeakPos n) {X+ : Ob (suc (n -WeakPos k))} {Y : Ob (n -WeakPos k)} {X''' : Ob (suc (suc (suc n)))} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc (suc n))))
--                 → (Aᵈ : isDefined (⟦ A ⟧Ty X'''))
--                 → (X+= : ft X+ ≡ Y) (X= : ft^ k X ≡ Y) {Z : Ob (suc (suc (suc (suc n))))} (X'''= : ft X''' ≡ X'') (X''= : ft X'' ≡ X') (X'= : ft X' ≡ X) (Z= : star++ (qq^ k X+= X=)  X''' X'''= X''= X'= qq^₁ ≡ Z)
--                → star+++ (qq^ k X+= X=) (⟦ A ⟧Ty X''' $ Aᵈ) (⟦⟧Ty-ft A) X'''= X''= X'= qq^₁ ≡ ⟦ weakenTy' (prev (prev (prev k))) A ⟧Ty Z $ ⟦weaken⟧Ty+++ᵈ' k A Aᵈ X+= X= X'''= X''= X'= Z=
-- ⟦weaken⟧Ty+++=' k A Aᵈ X+= X= refl refl refl Z= = ap-irr-star (! (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq qq^prev refl) refl)) refl ∙ ⟦weaken⟧Ty=' (prev (prev (prev k))) A Aᵈ X+= X= (ap-irr-star (qq^prev ∙ ap-irr-qq qq^prev refl) refl ∙ Z=)


{- We can now prove the main lemmas about weakening -}

⟦weaken⟧Tyᵈ' k (uu i) Aᵈ _ _ _ = tt
⟦weaken⟧Tyᵈ' k (el i v) (vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tmᵈ' k v vᵈ X+= X= Z=
  , ⟦⟧Tmₛ (weakenTm' k v)
  , (⟦weaken⟧Tm₁' k v vᵈ X+= X= Z= v₁ ∙ UUStrNat qq^₀ ∙ ap-irr-UUStr Z=)
  , tt)
⟦weaken⟧Tyᵈ' k (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k A)
  , ⟦weaken⟧Tyᵈ' k B Bᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k B)
  , tt)  
⟦weaken⟧Tyᵈ' k (pi A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) , tt)
⟦weaken⟧Tyᵈ' k (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) , tt)
⟦weaken⟧Tyᵈ' k empty Aᵈ _ _ _  = tt
⟦weaken⟧Tyᵈ' k unit Aᵈ _ _ _ = tt
⟦weaken⟧Tyᵈ' k nat Aᵈ _ _ _ = tt
⟦weaken⟧Tyᵈ' k (id A u v) (Aᵈ , A= , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦weaken⟧Tmᵈ' k v vᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weaken⟧Tm₁' k v vᵈ X+= X= Z= v₁ ∙ ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) , tt)

⟦weaken⟧Tmᵈ' k (var x) tt X+= X= Z= = tt

⟦weaken⟧Tmᵈ' k (uu i) tt X+= X= Z= = tt
⟦weaken⟧Tmᵈ' k (sum i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z=
  , ⟦⟧Tmₛ (weakenTm' k a)
  , (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ ⟦weaken⟧Ty=' k (uu i) tt X+= X= Z=)
  , ⟦weaken⟧Tmᵈ' k b bᵈ X+= X= Z=
  , ⟦⟧Tmₛ (weakenTm' k b)
  , (⟦weaken⟧Tm₁' k b bᵈ X+= X= Z= b₁ ∙ ⟦weaken⟧Ty=' k (uu i) tt X+= X= Z=)
  , tt)
⟦weaken⟧Tmᵈ' k (inl A B a) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k A)
  , ⟦weaken⟧Tyᵈ' k B Bᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k B)
  , ⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z=
  , ⟦⟧Tmₛ (weakenTm' k a)
  , (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
  , tt)  
⟦weaken⟧Tmᵈ' k (inr A B b) (Aᵈ , A= , Bᵈ , B= , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k A)
  , ⟦weaken⟧Tyᵈ' k B Bᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k B)
  , ⟦weaken⟧Tmᵈ' k b bᵈ X+= X= Z=
  , ⟦⟧Tmₛ (weakenTm' k b)
  , (⟦weaken⟧Tm₁' k b bᵈ X+= X= Z= b₁ ∙ ⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=)
  , tt)
⟦weaken⟧Tmᵈ' k (match A B C da db u) (Aᵈ , A= , Bᵈ , B= , Cᵈ , C= , daᵈ , daₛ , da₁ , dbᵈ , dbₛ , db₁ , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k A)
  , ⟦weaken⟧Tyᵈ' k B Bᵈ X+= X= Z=
  , ⟦⟧Ty-ft (weakenTy' k B)
  , ⟦weaken⟧Ty+ᵈ' k C Cᵈ X+= X= SumStr=
                  (⟦weaken⟧Ty=' k (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z=)
  , ⟦⟧Ty-ft (weakenTy' (prev k) C)
  , ⟦weaken⟧Tm+ᵈ' k da daᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)
  , ⟦⟧Tmₛ (weakenTm' (prev k) da)
  , (⟦weaken⟧Tm+₁' k da daᵈ X+= X= T-da₁= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) da₁
    ∙ T-da₁Nat qq^₀ ∙ ap-irr-T-da₁ Z= (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) (⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=)
                                      (⟦weaken⟧Ty+=' k C Cᵈ X+= X= SumStr= (⟦weaken⟧Ty=' k (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z=)))
  , ⟦weaken⟧Tm+ᵈ' k db dbᵈ X+= X= (⟦⟧Ty-ft B) (⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=)
  , ⟦⟧Tmₛ (weakenTm' (prev k) db)
  , (⟦weaken⟧Tm+₁' k db dbᵈ X+= X= T-db₁= (⟦⟧Ty-ft B) (⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=) db₁
    ∙ T-db₁Nat qq^₀ ∙ ap-irr-T-db₁ Z= (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) (⟦weaken⟧Ty=' k B Bᵈ X+= X= Z=)
                                      (⟦weaken⟧Ty+=' k C Cᵈ X+= X= SumStr=
                                                     (⟦weaken⟧Ty=' k (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z=)))
  , ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z=
  , ⟦⟧Tmₛ (weakenTm' k u)
  , (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ ⟦weaken⟧Ty=' k (sum A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z=)
  , tt)
⟦weaken⟧Tmᵈ' k (pi i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z=
  , ⟦⟧Tmₛ (weakenTm' k a)
  , (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ ⟦weaken⟧Ty=' k (uu i) tt X+= X= Z=)
  , ⟦weaken⟧Tm+ᵈ' k b bᵈ X+= X= ElStr= (⟦weaken⟧Ty=' k (el i a) (aᵈ , aₛ , a₁ , tt) X+= X= Z=) --(ElStrNat qq^₀ ∙ ap-irr-ElStr Z= (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=))
  , ⟦⟧Tmₛ (weakenTm' (prev k) b)
  , (⟦weaken⟧Tm+₁' k b bᵈ X+= X= UUStr= ElStr= (⟦weaken⟧Ty=' k (el i a) (aᵈ , aₛ , a₁ , tt) X+= X= Z=) b₁
    ∙ UUStrNat qq₀ ∙ ap-irr-UUStr (⟦weaken⟧Ty=' k (el i a) (aᵈ , aₛ , a₁ , tt) X+= X= Z=))
  , tt)
⟦weaken⟧Tmᵈ' k (lam A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weaken⟧Tm+ᵈ' k u uᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) u) ,
   (⟦weaken⟧Tm+₁' k u uᵈ X+= X= (⟦⟧Ty-ft B) (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) u₁ ∙ ⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=)) , tt)
⟦weaken⟧Tmᵈ' k (app A B f a) (Aᵈ , A= , Bᵈ , B= , fᵈ , fₛ , f₁ , aᵈ , aₛ , a₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weaken⟧Tmᵈ' k f fᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k f) ,
   (⟦weaken⟧Tm₁' k f fᵈ X+= X= Z= f₁ ∙ PiStrNat qq^₀
   ∙ ap-irr-PiStr Z= (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))) ,
   ⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁
   ∙ ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   tt)
⟦weaken⟧Tmᵈ' k (sig i a b) (aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= = 
  (⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ ⟦weaken⟧Ty=' k (uu i) tt X+= X= Z=) ,
   ⟦weaken⟧Tm+ᵈ' k b bᵈ X+= X= ElStr= (⟦weaken⟧Ty=' k (el i a) (aᵈ , aₛ , a₁ , tt) X+= X= Z=) ,
   ⟦⟧Tmₛ (weakenTm' (prev k) b) ,
   (⟦weaken⟧Tm+₁' k b bᵈ X+= X= UUStr= ElStr= (⟦weaken⟧Ty=' k (el i a) (aᵈ , aₛ , a₁ , tt) X+= X= Z=) b₁
   ∙ UUStrNat qq₀ ∙ ap-irr-UUStr (⟦weaken⟧Ty=' k (el i a) (aᵈ , aₛ , a₁ , tt) X+= X= Z=)),
   tt)
⟦weaken⟧Tmᵈ' k (pair A B a b) (Aᵈ , A= , Bᵈ , B= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦weaken⟧Tmᵈ' k b bᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k b) ,
   (⟦weaken⟧Tm₁' k b bᵈ X+= X= Z= b₁ ∙ starstar (⟦⟧Ty-ft A) aₛ
   ∙ ap-irr-star (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=) (⟦weaken⟧Ty+=' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=))) ,
   tt)
⟦weaken⟧Tmᵈ' k (pr1 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ ⟦weaken⟧Ty=' k (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z=) , 
   tt)
⟦weaken⟧Tmᵈ' k (pr2 A B u) (Aᵈ , A= , Bᵈ , B= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Ty+ᵈ' k B Bᵈ X+= X= (⟦⟧Ty-ft A) (⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) ,
   ⟦⟧Ty-ft (weakenTy' (prev k) B) ,
   ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ ⟦weaken⟧Ty=' k (sig A B) (Aᵈ , A= , Bᵈ , B= , tt) X+= X= Z=) ,
   tt)

⟦weaken⟧Tmᵈ' k (empty i) tt X+= X= Z= = tt
⟦weaken⟧Tmᵈ' k (emptyelim A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Ty+ᵈ' k A Aᵈ X+= X= EmptyStr= (⟦weaken⟧Ty=' k empty tt X+= X= Z=) ,
    ⟦⟧Ty-ft (weakenTy' (prev k) A) ,
    ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
    ⟦⟧Tmₛ (weakenTm' k u) ,
    (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ (⟦weaken⟧Ty=' k empty tt X+= X= Z=)) ,
    tt)

⟦weaken⟧Tmᵈ' k (unit i) tt X+= X= Z= = tt
⟦weaken⟧Tmᵈ' k tt tt X+= X= Z= = tt
⟦weaken⟧Tmᵈ' k (unitelim A dtt u) (Aᵈ , A= , dttᵈ , dttₛ , dtt₁ , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Ty+ᵈ' k A Aᵈ X+= X= UnitStr= (⟦weaken⟧Ty=' k unit tt X+= X= Z=) ,
    ⟦⟧Ty-ft (weakenTy' (prev k) A) ,
    ⟦weaken⟧Tmᵈ' k dtt dttᵈ X+= X= Z= ,
    ⟦⟧Tmₛ (weakenTm' k dtt) ,
    (⟦weaken⟧Tm₁' k dtt dttᵈ X+= X= Z= dtt₁ ∙ starstar UnitStr= ttStrₛ
    ∙ ap-irr-star (ttStrNat qq^₀ ∙ ap ttStr Z=) (⟦weaken⟧Ty+=' k A Aᵈ X+= X= UnitStr= (⟦weaken⟧Ty=' k unit tt X+= X= Z=))) , -- using ⟦weaken⟧Tm=' k tt tt X+= X= Z= gives termination error
    ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
    ⟦⟧Tmₛ (weakenTm' k u) ,
    (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ (⟦weaken⟧Ty=' k unit tt X+= X= Z=)) , tt)

⟦weaken⟧Tmᵈ' k (nat i) tt X+= X= Z= = tt
⟦weaken⟧Tmᵈ' k zero tt X+= X= Z= = tt
⟦weaken⟧Tmᵈ' k (suc u) (uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ ⟦weaken⟧Ty=' k nat tt X+= X= Z=) , tt)
⟦weaken⟧Tmᵈ' k (natelim P dO dS u) (Pᵈ , P= , dOᵈ , dOₛ , dO₁ , dSᵈ , dSₛ , dS₁ , uᵈ , uₛ , u₁ , tt) X+= X= {Z = Y} Z= =
  (wPᵈ , wP-ft , wdOᵈ , wdOₛ , wdO₁ , wdSᵈ , wdSₛ , wdS₁ , wuᵈ , wuₛ , wu₁ , tt)
    where
      wnat= = NatStrNat qq^₀ ∙ ap NatStr Z= -- using ⟦weaken⟧Ty=' k nat tt X+= X= Z= gives termination error
      wPᵈ = ⟦weaken⟧Ty+ᵈ' k P Pᵈ X+= X= NatStr= wnat=
      wP= = ⟦weaken⟧Ty+=' k P Pᵈ X+= X= NatStr= wnat=
      wP-ft = ⟦⟧Ty-ft (weakenTy' (prev k) P)
      wdOᵈ = ⟦weaken⟧Tmᵈ' k dO dOᵈ X+= X= Z=
      wdOₛ = ⟦⟧Tmₛ (weakenTm' k dO)
      wdO₁ = ⟦weaken⟧Tm₁' k dO dOᵈ X+= X= Z= dO₁ ∙ starstar NatStr= zeroStrₛ ∙ ap-irr-star (zeroStrNat qq^₀ ∙ ap zeroStr Z=) wP= -- using ⟦weaken⟧Tm=' k zero tt X+= X= Z= gives termination error
      wdSᵈ = ⟦weaken⟧Tm++ᵈ' k dS dSᵈ X+= X= (⟦⟧Ty-ft P) NatStr= wP=
      wdSₛ = ⟦⟧Tmₛ (weakenTm' (prev (prev k)) dS)
      wdS₁ = ⟦weaken⟧Tm++₁' k dS dSᵈ X+= X= (ft-star ∙ sucStr₀) P= NatStr= wP= dS₁ ∙
             T-dS₁Nat qq^₀ ∙ ap-irr-T-dS₁ Z= wP=
      wuᵈ = ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z=
      wuₛ = ⟦⟧Tmₛ (weakenTm' k u)
      wu₁ = ⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ wnat=
      
⟦weaken⟧Tmᵈ' k (id i a u v) (aᵈ , aₛ , a₁ , uᵈ , uₛ , u₁ , vᵈ , vₛ , v₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k a) ,
   (⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ ⟦weaken⟧Ty=' k (uu i) tt X+= X= Z=) ,
   ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ ⟦weaken⟧Ty=' k (el i a) (aᵈ , aₛ , a₁ , tt) X+= X= Z=) ,
   ⟦weaken⟧Tmᵈ' k v vᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k v) ,
   (⟦weaken⟧Tm₁' k v vᵈ X+= X= Z= v₁ ∙ ⟦weaken⟧Ty=' k (el i a) (aᵈ , aₛ , a₁ , tt) X+= X= Z=) ,
   tt)
⟦weaken⟧Tmᵈ' k (refl A u) (Aᵈ , A= , uᵈ , uₛ , u₁ , tt) X+= X= Z= =
  (⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z= ,
   ⟦⟧Ty-ft (weakenTy' k A) ,
   ⟦weaken⟧Tmᵈ' k u uᵈ X+= X= Z= ,
   ⟦⟧Tmₛ (weakenTm' k u) ,
   (⟦weaken⟧Tm₁' k u uᵈ X+= X= Z= u₁ ∙ ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=) , tt)
⟦weaken⟧Tmᵈ' k (jj A P d a b p) (Aᵈ , A= , Pᵈ , P= , dᵈ , dₛ , d₁ , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , pᵈ , pₛ , p₁ , tt) X+= X= Z= =
  (wAᵈ , wA-ft , wPᵈ , wP-ft , wdᵈ , wdₛ , wd₁ , waᵈ , waₛ , wa₁ , wbᵈ , wbₛ , wb₁ , wpᵈ , wpₛ , wp₁ , tt)
  where
   wAᵈ = ⟦weaken⟧Tyᵈ' k A Aᵈ X+= X= Z=
   wA= = ⟦weaken⟧Ty=' k A Aᵈ X+= X= Z=
   wA-ft = ⟦⟧Ty-ft (weakenTy' k A)
   wPᵈ = ⟦weaken⟧Ty+++ᵈ' k P Pᵈ X+= X= T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat qq^₀ ∙ ap-irr-T-ftP Z= wA=)
   wP= = ⟦weaken⟧Ty+++=' k P Pᵈ X+= X= T-ftP= (ft-star ∙ pp₀) A= (T-ftPNat qq^₀ ∙ ap-irr-T-ftP Z= wA=)
   wP-ft = ⟦⟧Ty-ft (weakenTy' (prev (prev (prev k))) P)
   wdᵈ = ⟦weaken⟧Tm+ᵈ' k d dᵈ X+= X= A= wA=
   wdₛ = ⟦⟧Tmₛ (weakenTm' (prev k) d)
   wd₁ = ⟦weaken⟧Tm+₁' k d dᵈ X+= X= T-d₁= A= wA= d₁ ∙ T-d₁Nat  qq^₀ ∙ ap-irr-T-d₁ Z= wA= wP=
   waᵈ = ⟦weaken⟧Tmᵈ' k a aᵈ X+= X= Z=
   waₛ = ⟦⟧Tmₛ (weakenTm' k a)
   wa₁ = ⟦weaken⟧Tm₁' k a aᵈ X+= X= Z= a₁ ∙ wA=
   wbᵈ = ⟦weaken⟧Tmᵈ' k b bᵈ X+= X= Z=
   wbₛ = ⟦⟧Tmₛ (weakenTm' k b)
   wb₁ = ⟦weaken⟧Tm₁' k b bᵈ X+= X= Z= b₁ ∙ wA=
   wpᵈ = ⟦weaken⟧Tmᵈ' k p pᵈ X+= X= Z=
   wpₛ = ⟦⟧Tmₛ (weakenTm' k p)
   wp₁ = ⟦weaken⟧Tm₁' k p pᵈ X+= X= Z= p₁ ∙ IdStrNat qq^₀ ∙ ap-irr-IdStr Z= wA= (⟦weaken⟧Tm=' k a aᵈ X+= X= Z=) (⟦weaken⟧Tm=' k b bᵈ X+= X= Z=) -- using ⟦weaken⟧Ty=' k (id A a b) (Aᵈ , A= , aᵈ , aₛ , a₁ , bᵈ , bₛ , b₁ , tt) X+= X= Z= gives a termination error
   
{- We are done with the main induction in this file, here are a few additional lemmas needed later. -}


{- Weakening at [last] -}

⟦weaken⟧Tyᵈ : {X+ : Ob (suc n)} {X : Ob n} (A : TyExpr n)
            → (Aᵈ : isDefined (⟦ A ⟧Ty X))
            → (X= : ft X+ ≡ X)
            → isDefined (⟦ weakenTy A ⟧Ty X+)
⟦weaken⟧Tyᵈ A Aᵈ X= = ⟦weaken⟧Tyᵈ' last A Aᵈ X= refl refl

⟦weaken⟧Ty= : {X+ : Ob (suc n)} {X : Ob n} (A : TyExpr n)
            → (Aᵈ : isDefined (⟦ A ⟧Ty X))
            → (X= : ft X+ ≡ X)
            → star (pp X+) (⟦ A ⟧Ty X $ Aᵈ) (⟦⟧Ty-ft A) (pp₁ ∙ X=) ≡ ⟦ weakenTy A ⟧Ty X+ $ ⟦weaken⟧Tyᵈ A Aᵈ X=
⟦weaken⟧Ty= A Aᵈ X= = ap-irr-star (! qq^last) refl ∙ ⟦weaken⟧Ty=' last A Aᵈ X= refl refl

⟦weaken⟧Tmᵈ : {X+ : Ob (suc n)} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ X)
            → isDefined (⟦ weakenTm u ⟧Tm X+)
⟦weaken⟧Tmᵈ u uᵈ X= = ⟦weaken⟧Tmᵈ' last u uᵈ X= refl refl

⟦weaken⟧Tm= : {X+ : Ob (suc n)} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ X)
            → starTm (pp X+) (⟦ u ⟧Tm X $ uᵈ) (⟦⟧Tm₀ u) (pp₁ ∙ X=) ≡ ⟦ weakenTm u ⟧Tm X+ $ ⟦weaken⟧Tmᵈ u uᵈ X=
⟦weaken⟧Tm= u uᵈ X= = ap-irr-starTm (! qq^last) refl ∙ ⟦weaken⟧Tm=' last u uᵈ X= refl refl

⟦weaken⟧Tm₁ : {X+ : Ob (suc n)} {X : Ob n} (u : TmExpr n)
            → (uᵈ : isDefined (⟦ u ⟧Tm X))
            → (X= : ft X+ ≡ X)
            → {∂₁u : Ob (suc n)} (u₁ : ∂₁ (⟦ u ⟧Tm X $ uᵈ) ≡ ∂₁u)
            → ∂₁ (⟦ weakenTm u ⟧Tm X+ $ ⟦weaken⟧Tmᵈ u uᵈ X=) ≡ star (pp X+) ∂₁u (⟦⟧Tm₁-ft u u₁) (pp₁ ∙ X=)
⟦weaken⟧Tm₁ u uᵈ X= refl = ⟦weaken⟧Tm₁' last u uᵈ X= refl refl refl ∙ ap3-irr2 star qq^last refl refl

{- Weakening at [prev last] -}

⟦weaken⟧Ty+ᵈ : {X+ : Ob (suc n)} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc n))
             → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
             → (X= : ft X+ ≡ X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (pp X+) X' p (pp₁ ∙ X=) ≡ Y)
             → isDefined (⟦ weakenTy' (prev last) A ⟧Ty Y)
⟦weaken⟧Ty+ᵈ A Aᵈ X= p Y= = ⟦weaken⟧Ty+ᵈ' last A Aᵈ X= refl p (ap-irr-star qq^last refl ∙ Y=)

⟦weaken⟧Ty+= : {X+ : Ob (suc n)} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc n))
             → (Aᵈ : isDefined (⟦ A ⟧Ty X'))
             → (X= : ft X+ ≡ X) {Y : Ob (suc (suc n))} (p : ft X' ≡ X) (Y= : star (pp X+) X' p (pp₁ ∙ X=) ≡ Y)
             → star (qq (pp X+) X' p (pp₁ ∙ X=)) (⟦ A ⟧Ty X' $ Aᵈ) (⟦⟧Ty-ft A) qq₁ ≡ ⟦ weakenTy' (prev last) A ⟧Ty Y $ ⟦weaken⟧Ty+ᵈ A Aᵈ X= p Y=
⟦weaken⟧Ty+= A Aᵈ X= refl Y= = ap-irr-star (ap-irr-qq (! qq^last) refl) refl ∙ ⟦weaken⟧Ty+=' last A Aᵈ X= refl refl (ap-irr-star qq^last refl ∙ Y=)

{- Weakening at [prev (prev last)] -}

⟦weaken⟧Ty++ᵈ : {X+ : Ob (suc n)} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc n)))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X''))
              → (X= : ft X+ ≡ X) {Y : Ob (suc (suc (suc n)))} (p : ft X'' ≡ X') (p' : ft X' ≡ X) (Y= : star (qq (pp X+) X' p' (pp₁ ∙ X=)) X'' p qq₁ ≡ Y)
              → isDefined (⟦ weakenTy' (prev (prev last)) A ⟧Ty Y)
⟦weaken⟧Ty++ᵈ A Aᵈ X= refl refl Y= = ⟦weaken⟧Tyᵈ' (prev (prev last)) A Aᵈ X= refl (ap-irr-star (qq^prev ∙ ap-irr-qq qq^last refl) refl ∙ Y=)

⟦weaken⟧Ty++= : {X+ : Ob (suc n)} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc n)))
              → (Aᵈ : isDefined (⟦ A ⟧Ty X''))
              → (X= : ft X+ ≡ X) {Y : Ob (suc (suc (suc n)))} (p : ft X'' ≡ X') (p' : ft X' ≡ X) (Y= : star (qq (pp X+) X' p' (pp₁ ∙ X=)) X'' p qq₁ ≡ Y)
              → star (qq (qq (pp X+) X' p' (pp₁ ∙ X=)) X'' p qq₁) (⟦ A ⟧Ty X'' $ Aᵈ) (⟦⟧Ty-ft A) qq₁ ≡ ⟦ weakenTy' (prev (prev last)) A ⟧Ty Y $ ⟦weaken⟧Ty++ᵈ A Aᵈ X= p p' Y=
⟦weaken⟧Ty++= A Aᵈ X= refl refl Y= = ap-irr-star (ap-irr-qq (ap-irr-qq (! qq^last) refl ∙ ! qq^prev) refl ∙ ! qq^prev) refl ∙ ⟦weaken⟧Ty=' (prev (prev last)) A Aᵈ X= refl (ap-irr-star (qq^prev ∙ ap-irr-qq qq^last refl) refl ∙ Y=)

{- Weakening at [prev (prev (prev last))] -}

⟦weaken⟧Ty+++ᵈ : {X+ : Ob (suc n)} {X''' : Ob (suc (suc (suc n)))} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc (suc n))))
               → (Aᵈ : isDefined (⟦ A ⟧Ty X'''))
               → (X= : ft X+ ≡ X) {Y : Ob (suc (suc (suc (suc n))))} (p : ft X''' ≡ X'') (p' : ft X'' ≡ X') (p'' : ft X' ≡ X) (Y= : star (qq (qq (pp X+) X' p'' (pp₁ ∙ X=)) X'' p' qq₁) X''' p qq₁ ≡ Y)
               → isDefined (⟦ weakenTy' (prev (prev (prev last))) A ⟧Ty Y)
⟦weaken⟧Ty+++ᵈ A Aᵈ X= refl refl refl Y= = ⟦weaken⟧Tyᵈ' (prev (prev (prev last))) A Aᵈ X= refl (ap-irr-star (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq qq^last refl) refl) refl ∙ Y=)

⟦weaken⟧Ty+++= : {X+ : Ob (suc n)} {X''' : Ob (suc (suc (suc n)))} {X'' : Ob (suc (suc n))} {X' : Ob (suc n)} {X : Ob n} (A : TyExpr (suc (suc (suc n))))
               → (Aᵈ : isDefined (⟦ A ⟧Ty X'''))
               → (X= : ft X+ ≡ X) {Y : Ob (suc (suc (suc (suc n))))} (p : ft X''' ≡ X'') (p' : ft X'' ≡ X') (p'' : ft X' ≡ X) (Y= : star (qq (qq (pp X+) X' p'' (pp₁ ∙ X=)) X'' p' qq₁) X''' p qq₁ ≡ Y)
               → star (qq (qq (qq (pp X+) X' p'' (pp₁ ∙ X=)) X'' p' qq₁) X''' p qq₁) (⟦ A ⟧Ty X''' $ Aᵈ) (⟦⟧Ty-ft A) qq₁ ≡ ⟦ weakenTy' (prev (prev (prev last))) A ⟧Ty Y $ ⟦weaken⟧Ty+++ᵈ A Aᵈ X= p p' p'' Y=
⟦weaken⟧Ty+++= A Aᵈ X= refl refl refl Y= = ! (ap-irr-star (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq qq^last refl) refl) refl) refl) ∙ ⟦weaken⟧Ty=' (prev (prev (prev last))) A Aᵈ X= refl (ap-irr-star (qq^prev ∙ ap-irr-qq (qq^prev ∙ ap-irr-qq qq^last refl) refl) refl ∙ Y=)

{- Weakening of morphisms -}

⟦weaken⟧Morᵈ : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y : Ob m} (δ : Mor n m)
           → isDefined (⟦ δ ⟧Mor X Y)
           → isDefined (⟦ weakenMor δ ⟧Mor X+ Y)
⟦weaken⟧Mor= : {X+ : Ob (suc n)} {X : Ob n} (X= : ft X+ ≡ X) {Y : Ob m} (δ : Mor n m)
           → (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
           → ⟦ weakenMor δ ⟧Mor X+ Y $ ⟦weaken⟧Morᵈ X= δ δᵈ ≡ comp (⟦ δ ⟧Mor X Y $ δᵈ) (pp X+) (⟦⟧Mor₀ δ ∙ ! X=) pp₁

⟦weaken⟧Morᵈ refl ◇ tt = tt
⟦weaken⟧Morᵈ {X+ = X+} refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) = (⟦weaken⟧Morᵈ refl δ δᵈ , ⟦weaken⟧Tmᵈ u uᵈ refl , ⟦⟧Mor₁ (weakenMor δ) , (⟦weaken⟧Tm₁ u uᵈ refl u₁ ∙ ! star-comp ∙ ! (ap3-irr2 star (⟦weaken⟧Mor= refl δ δᵈ) refl refl)) , tt)

⟦weaken⟧Mor= refl ◇ tt = ! (ptmor-unique _ _ (comp₀ ∙ pp₀) (comp₁ ∙ pt-unique _))
⟦weaken⟧Mor= refl (δ , u) (δᵈ , uᵈ , δ₁ , u₁ , tt) =
  ap-irr-comp
    (ap-irr-qq
      (⟦weaken⟧Mor= refl δ δᵈ)
      refl
     ∙ qq-comp
     ∙ ap-irr-comp refl
       ((ap-irr-qq (! (ap-irr-comp (is-section= (ft-star ∙ ⟦⟧Mor₀ δ) (⟦⟧Tmₛ u) u₁) refl ∙ id-right pp₁) ∙ assoc) refl)))
    (! (⟦weaken⟧Tm= u uᵈ refl))
  ∙ assoc {g₁ = qq₁} {h₀ = qq₀}
  ∙ ! (ap-irr-comp refl (ss-qq {f₁ = comp₁ ∙ u₁}))
  ∙ ! assoc

⟦weaken⟧Mor+ᵈ : {Z : Ob (suc n)} {X : Ob n} {Y' : Ob (suc m)} {Y : Ob m}
                (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'= : ft Y' ≡ Y) 
              → (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → isDefined (⟦ weakenMor+ δ ⟧Mor Z Y')
⟦weaken⟧Mor+ᵈ δ δᵈ refl Z= = (⟦weaken⟧Morᵈ (ap ft (! Z=) ∙ ft-star ∙ ⟦⟧Mor₀ δ) δ δᵈ , (tt , (⟦⟧Mor₁ (weakenMor δ) , (varCL₁ {X= = refl} ∙ ap-irr-star refl (! Z=) ∙ ! star-comp ∙ ap-irr-star (! (⟦weaken⟧Mor= (ap ft (! Z=) ∙ ft-star ∙ ⟦⟧Mor₀ δ) δ δᵈ)) refl) , tt)))

⟦weaken⟧Mor+= : {Z : Ob (suc n)} {X : Ob n} {Y' : Ob (suc m)} {Y : Ob m}
                (δ : Mor n m) (δᵈ : isDefined (⟦ δ ⟧Mor X Y)) (Y'= : ft Y' ≡ Y) 
              → (Z= : star (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ) ≡ Z)
              → ⟦ weakenMor+ δ ⟧Mor Z Y' $ ⟦weaken⟧Mor+ᵈ δ δᵈ Y'= Z= ≡ qq (⟦ δ ⟧Mor X Y $ δᵈ) Y' Y'= (⟦⟧Mor₁ δ)
⟦weaken⟧Mor+= δ δᵈ refl Z= = ap-irr-comp (ap-irr-qq (⟦weaken⟧Mor= (ap ft (! Z=) ∙ ft-star ∙ ⟦⟧Mor₀ δ) δ δᵈ ∙ refl) refl ∙ qq-comp) refl {f₁' = varCL₁ {X= = refl}} ∙ assoc {g₀ = qq₀ ∙ ap-irr-star refl Z=} ∙ ap-irr-comp refl (ap-irr-comp (ap-irr-qq (! (id-left pp₀)) Z=) refl ∙ (! ss-qq)) ∙ id-left (qq₀ ∙ Z=)


{- [getTy k Γ] is defined and is the codomain of the interpretation of [var k] -}

⟦getTy⟧ᵈ : (k : VarPos n) {Γ : Ctx n} (Γᵈ : isDefined ⟦ Γ ⟧Ctx)
         → isDefined (⟦ getTy k Γ ⟧Ty (⟦ Γ ⟧Ctx $ Γᵈ))
⟦getTy⟧ᵈ last {Γ = Γ , A} (Γᵈ , (Aᵈ , tt)) = ⟦weaken⟧Tyᵈ A Aᵈ (⟦⟧Ty-ft A)
⟦getTy⟧ᵈ (prev k) {Γ = Γ , A} Γᵈ = ⟦weaken⟧Tyᵈ (getTy k Γ) (⟦getTy⟧ᵈ k (fst Γᵈ)) (⟦⟧Ty-ft A)

⟦getTy⟧ : (k : VarPos n) {Γ : Ctx n} (Γᵈ : isDefined ⟦ Γ ⟧Ctx) (Aᵈ : isDefined (⟦ getTy k Γ ⟧Ty (⟦ Γ ⟧Ctx $ _)))
        → ∂₁ (⟦ var k ⟧Tm (⟦ Γ ⟧Ctx $ Γᵈ) $ tt) ≡
          ⟦ getTy k Γ ⟧Ty (⟦ Γ ⟧Ctx $ Γᵈ) $ Aᵈ
⟦getTy⟧ last {Γ = Γ , A} Γᵈ Aᵈ = varCL₁ ∙ ⟦weaken⟧Ty= A (fst (snd Γᵈ)) (⟦⟧Ty-ft A)
⟦getTy⟧ (prev k) {Γ = Γ , A} Γᵈ Aᵈ = varC+₁ k (⟦⟧Ty-ft A) (⟦getTy⟧ k (fst Γᵈ) (⟦getTy⟧ᵈ k (fst Γᵈ))) ∙ ⟦weaken⟧Ty= (getTy k Γ) (⟦getTy⟧ᵈ k (fst Γᵈ)) (⟦⟧Ty-ft A)
