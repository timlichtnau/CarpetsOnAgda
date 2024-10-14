{-# OPTIONS --cubical --without-K #-}
open import CarpetCubical3
open import CubicalBasics.PointedTypesCubical
--open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
--open import Data.Product
open import Agda.Builtin.Unit
open import CubicalBasics.PropositionReasoning
--open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)

--open import Function.Base using (_∘_)
--open import Relation.Binary.Definitions 
--open import Relation.Binary.Structures using (IsPartialOrder ; IsPreorder)
open import Equalizer3
open import SemiLattices
open import CubicalBasics.cubical-prelude hiding (_∨_ ; _∧_)
open import CubicalBasics.cubicalEqualityReasoning
open import HomoAlgStd

--import Relation.Binary.Reasoning.Base.Single
import HomoAlgOnCarpets
import SmartImplication
--open import Relation.Binary renaming (_⇒_ to _==>_)
--open import DoublePreorderReasoning
open import FibreArgumentation
import SupporterInduction
import NaiveImplication
module FiberInduction {o e} (carpet : Carpet {o} {ℓ} {e} ) where
open HomoAlgOnCarpets carpet 
open CarpetHelper carpet  
open SmartImplication carpet 
open NaiveImplication carpet 
open SupporterInduction carpet 

private variable
  j k l : Carrier

open Monad (truncMonad)



record IndScheme (B B' : SubPtd (𝕏 j)) {q : j ≤ k} (P : SubEl) : Type (suc lzero ⊔ e ⊔ o) where
  field
    ker=>P : Ker q =>' P
    B=>B' : (j , B) =>' (j , B')
    edge : UNC B=>B' ≤ k
    B'=>P : (j , B') =>' P

IndSchemeToSupScheme :  {B B' : SubPtd (𝕏 j)} {q : j ≤ k} {P : SubEl} → IndScheme B B' {q = q} P → SupScheme B B' (j , B) P 
IndSchemeToSupScheme {q = q}  record { ker=>P = ker=>P ; B=>B' = B=>B' ; edge = edge ; B'=>P = B'=>P } = record {
  A=>B = refl=>' ;
  A=>B' = B=>B' ;
  edge = sup  q edge ; --sup reflexivity edge ;
  B'=>P = B'=>P ; Ker=>P = ker=>P }
--THIS MEANS IN PARTICULAR THAT fibInduction follows from supporter Induction

fibindhelper : {B B' : SubPtd (𝕏 j)} {P : SubEl} {q : j ≤ k}  →
      (K=>P : Ker q =>' P)
   → ( B=>B' : (j , B) =>' (j , B') )
   → (ed : UNC B=>B' ≤ k)
   → (B'=>P : (j , B') =>' P)
   → (j , B) =>'[ UNC B'=>P ∨ UNC K=>P ] P
fibindhelper ker=>p b=>b' edge b'=>p = IncUncert'' (SupInd (IndSchemeToSupScheme (record { ker=>P = ker=>p ; B=>B' = b=>b' ; edge = edge ; B'=>P = b'=>p })) ) (( (left' (back b'=>p) ■ uB)) ∨R)
{--
j ∨
(NaiveImplication.uncert (back b'=>p) ∨
 NaiveImplication.uncert (back ker=>p))
--}
syntax fibindhelper ker=>p b=>b' edge b'=>p = ROUNDTRIP b=>b' ∶ b'=>p MOVECHILDREN edge < ker=>p >

{--
fibInd :  {A B : SubPtd (𝕏 j)} {P : SubEl} {q : j ≤ k} → IndScheme A B P → (j , A) =>' P -- THE UNC of the result will be the sup of B=>P and KER=>P
-- (p : (j , A) =>' (j , B)) →   (ed : j ≤ uncert (back p)) → (ed' : uncert (back p) ≤ k) → {ed'' : j ≤ k} → (b=>p : (j , B) =>' P ) → ((ker=>p) : (j , ker (ϕ ed'') ) =>' P) →  (j , A) =>' P
fibInd {q = ed''}  record {B=>B' = p ; edge = ed' ;  B'=>P = b=>p ; ker=>P = ker=>p } = NOTHING (_ , fibInd' p  (back b=>p) (back (intro⊂ (kerf⊂kergf  ed' ed'') ∷  ker=>p ))) where
  open Reasoning
  ed = left' (back p)
  fibInd' :   {A B : SubPtd (𝕏 j)} {P : SubEl} → (p : (j , A) =>' (j , B)) →
    (b=>p : (j , B) => P ) → ((ker=>p) : (j , ker (ϕ (left' (back p))) ) => P) →  (j , A) ~~ uncert b=>p ∨ uncert ker=>p ~> P 
  fibInd' {j = j} {A = A} {B = B} {P = P } p b=>p ker=>p  = λ x →
    pf ← ((=>'toFib p ( left' (back p))) x) ,
    ind'  {B = A} b=>p ker=>p x pf where
      =>'toFib : {A B : SubPtd (𝕏 j)} → (p : (j , A) =>' (j , B)) →
       (ed : j ≤ uncert (back p)) → 
       (x : 【 A 】) →
        ∥ (Σ[ y ∈ 【 B 】 ] ((proj₁ x) ≣[ ϕ ed ] (proj₁ y))) ∥₋₁ 
      =>'toFib {A = A} {B = B} p' ed = 
        λ x → fmap (Σmap λ a y → ≡ToFib {A = A} {B = B} x ed y) (provider (back p') x)  
--}
