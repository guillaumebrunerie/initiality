{-# OPTIONS --rewriting --prop #-}

open import common
open import typetheory
open import syntx
open import rules
open import contextualcat
open import quotients


open import termmodel-common public
open import termmodel-synccat public
open import termmodel-uuel public
open import termmodel-sum public
open import termmodel-pi public
open import termmodel-sig public
open import termmodel-empty public
open import termmodel-unit public
open import termmodel-nat public
open import termmodel-id public
open import termmodel-id2 public

open CCat hiding (Mor) renaming (id to idC)

open StructuredCCat

strSynCCat : StructuredCCat

ccat strSynCCat = synCCat

ccatUU strSynCCat = UUStrSynCCat
ccatEl strSynCCat = ElStrSynCCat
ccatSum strSynCCat = SumStrSynCCat
ccatPi strSynCCat = PiStrSynCCat
ccatSig strSynCCat = SigStrSynCCat
ccatEmpty strSynCCat = EmptyStrSynCCat
ccatUnit strSynCCat = UnitStrSynCCat
ccatNat strSynCCat = NatStrSynCCat
ccatId strSynCCat = IdStrSynCCat

ccatuu strSynCCat = uuStrSynCCat
ccatsum strSynCCat = sumStrSynCCat
ccatinl strSynCCat = inlStrSynCCat
ccatinr strSynCCat = inrStrSynCCat
ccatmatch strSynCCat = matchStrSynCCat
ccatpi strSynCCat = piStrSynCCat
ccatlam strSynCCat = lamStrSynCCat
ccatapp strSynCCat = appStrSynCCat
ccatsig strSynCCat = sigStrSynCCat
ccatpair strSynCCat = pairStrSynCCat
ccatpr1 strSynCCat = pr1StrSynCCat
ccatpr2 strSynCCat = pr2StrSynCCat
ccatempty strSynCCat = emptyStrSynCCat
ccatemptyelim strSynCCat = emptyelimStrSynCCat
ccatunit strSynCCat = unitStrSynCCat
ccattt strSynCCat = ttStrSynCCat
ccatunitelim strSynCCat = unitelimStrSynCCat
ccatnat strSynCCat = natStrSynCCat
ccatzero strSynCCat = zeroStrSynCCat
ccatsuc strSynCCat = sucStrSynCCat
ccatnatelim strSynCCat = natelimStrSynCCat
ccatid strSynCCat = idStrSynCCat
ccatrefl strSynCCat = reflStrSynCCat
ccatjj strSynCCat = jjStrSynCCat

betaInlStr strSynCCat {Γ = Γ} {A = A} {B = B} {C = C} {da = da} {db = db} {a = a} = betaInlStrS Γ A _ B _ C _ da _ _ db _ _ a _ _
betaInrStr strSynCCat {Γ = Γ} {A = A} {B = B} {C = C} {da = da} {db = db} {b = b} = betaInrStrS Γ A _ B _ C _ da _ _ db _ _ b _ _
betaPiStr strSynCCat {Γ = Γ} {A = A} {B = B} {u = u} {a = a} = betaPiStrS Γ A _ B _ u _ _ a _ _
betaSig1Str strSynCCat {Γ = Γ} {A = A} {B = B} {a = a} {b = b} = betaSig1StrS Γ A _ B _ a _ _ b _ _
betaSig2Str strSynCCat {Γ = Γ} {A = A} {B = B}  {a = a} {b = b} = betaSig2StrS Γ A _ B _ a _ _ b _ _
betaUnitStr strSynCCat {Γ = Γ} {A = A} {dtt = dtt} = betaUnitStrS Γ A _ dtt _ _ 
betaNatZeroStr strSynCCat {Γ = Γ} {P = P} {dO = dO} {dS = dS} = betaNatZeroStrS Γ P _ dO _ _ dS _ _
betaNatSucStr strSynCCat {Γ = Γ} {P = P} {dO = dO} {dS = dS} {u = u} = betaNatSucStrS Γ P _ dO _ _ dS _ _ u _ _
betaIdStr strSynCCat {Γ = Γ} {A = A} {P = P} {d = d} {a = a}  = betaIdStrS Γ A _ P _ d _ _  a _ _

etaSumStr strSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = etaSumStrS Γ A _ B _ u _ _
etaPiStr strSynCCat {Γ = Γ} {A = A} {B = B} {f = f} {fₛ = fₛ} {f₁ = f₁} = etaPiStrS Γ A _ B _ f fₛ f₁
etaSigStr strSynCCat {Γ = Γ} {A = A} {B = B} {u = u} = etaSigStrS Γ A _ B _ u _ _

eluuStr strSynCCat {Γ = Γ} = eluuStrS _ Γ
elsumStr strSynCCat {Γ = Γ} {a = a} {b = b} = elsumStrS _ Γ a _ _ b _ _
elpiStr strSynCCat {Γ = Γ} {a = a} {b = b} = elpiStrS _ Γ a _ _ b _ _
elsigStr strSynCCat {Γ = Γ} {a = a} {b = b} = elsigStrS _ Γ a _ _ b _ _
elemptyStr strSynCCat {Γ = Γ} = elemptyStrS _ Γ
elunitStr strSynCCat {Γ = Γ} = elunitStrS _ Γ
elnatStr strSynCCat {Γ = Γ} = elnatStrS _ Γ
elidStr strSynCCat {Γ = Γ} {a = a} {u = u} {v = v} = elidStrS _ Γ a _ _ u _ _ v _ _
 
