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
open import HomoAlgStd hiding (fib)

--import Relation.Binary.Reasoning.Base.Single
import HomoAlgOnCarpets
import SmartImplication
--open import Relation.Binary renaming (_⇒_ to _===>_)
--open import DoublePreorderReasoning
open import FibreArgumentation
import NaiveImplication
module SupporterInduction {o e} (carpet : Carpet {o} {ℓ} {e} ) where

open CarpetHelper carpet  
open SmartImplication carpet 

private variable
  j k l : Carrier

open Monad (truncMonad)
private
  open NaiveImplication carpet
  open HomoAlgOnCarpets carpet 
  ≡ToFib : {A B : SubPtd (𝕏 j)} {k : Carrier} {x' : X j} → (x : 【 A 】) → (ed : j ≤ k) → (y : (j , proj₁ x) ≡[ k ] (j , x')) → fib (ϕ ed) (proj₁ x) x'
  ≡ToFib x ed y = fibInverse (ϕ ed) (isEmb (eq' y))


  ind' :  {B B' : SubPtd (𝕏 j)} {P : SubEl} {k : Carrier} {ed : j ≤ k} →
    (b=>p : (j , B')  => P)
    (ker=>p : Ker ed => P)
    ((x , xp) : 【 B 】) →
    (Σ[ (y , yp) ∈ 【 B' 】 ] (x ≣[ ϕ ed ] y)) →
    (j , B) ~ (x , xp) ~ uncert (b=>p) ∨ uncert (ker=>p)  ~> P
  ind'  {j = j} {B = A} {B' = B} {P = P } {ed = ed} b=>p ker=>p = ind where
    ind :  ((x , xp) : 【 A 】) → (Σ[ (y , yp) ∈ 【 B 】 ] (x ≣[ ϕ ed ] y)) →  (j , A) ~ (x , xp) ~ uncert (b=>p) ∨ uncert (ker=>p)  ~> P
    ind (x , xp) ((y , yp) , (kern 0=fx _)) = fmap (Σmap (λ a → deeper uB')) (provider ker=>p (x , (sym (0=fx))))
    ind (x , xp) ((.x , yp) , inh) = fmap (Σmap (λ a → deeper uB)) (provider (b=>p) (x , yp))  

record SupScheme (B B' : SubPtd (𝕏 j)) {q : j ≤ k} (A P : SubEl) : Type (suc lzero ⊔ e ⊔ o) where

    field
      A=>B : A =>' (j , B)
      A=>B' : A =>' (j , B')
      edge : UNC A=>B ∨ UNC A=>B' ≤ k
      B'=>P : (j , B') =>' P
      Ker=>P : Ker q =>' P --right' (back A=>B) ■ uB {UNC A=>B} {UNC A=>B'}
open SupScheme
SupInd : {B B' : SubPtd (𝕏 j)} {q : j ≤ k} {A P : SubEl} → (S : SupScheme B B' A P) → A =>'[ UNC (A=>B S) ∨ (UNC (B'=>P S) ∨
                                                                                                           UNC (Ker=>P S)) ] P
SupInd {q = q} record { A=>B = A=>B ; A=>B' = A=>B' ; B'=>P = B'=>P ; edge = ed' ; Ker=>P = Ker=>P } =
  NOTHING (supInd' (back A=>B) (back A=>B') (back B'=>P) (back (  IncUncert' (intro⊂ (kerf⊂kergf   ed' q) ∷ Ker=>P)  (UNCTrans (intro⊂ (kerf⊂kergf   ed' q)) Ker=>P ■  left' (back Ker=>P)  ∨R )  )))   where

    supInd' : {A P : SubEl}   {B B' : SubPtd (𝕏 j)} → (ρ : A => (j , B)) → (ρ' : A => (j , B')) → (ψ : (j , B') => P) → (ζ : Ker (  right' ρ ■ uB {uncert ρ} {uncert ρ'}   ) => P) →  A => P
    supInd' {j = j} {A = A} {P = P} {B = B} {B' = B'} ρ ρ' ψ ζ = uncert ρ ∨ (uncert ψ ∨ uncert ζ) , AR λ a →
      (b , p) ← (provider ρ) a ,
      (b' , p') ← (provider ρ') a , 
      (ep , pf) ← ind' {B = B} {B' = B'} ψ ζ  b (b' , ≡ToFib {A = B} {B = B'} b (right' ρ ■ uB) ( trans≡ (symm p) p') ) ,
      return (ep , trans≡ p pf) 
    --   ind' {!ψ!} {!!} {!!} {!!} 
  -- THE UNC of result is A=>B ∨ (B'=>'P ∨ Ker => P)
supindhelper : {B B' : SubPtd (𝕏 j)} {q : j ≤ k} {A P : SubEl} →
     (A=>B : A =>' (j , B))
    → (A=>B' : A =>' (j , B'))
    → (ED : UNC A=>B ∨ UNC A=>B' ≤ k)
    → (B'=>P : (j , B') =>' P)
    → (K=>P : Ker q =>' P)
    → A ==> P --UNC (A=>B) ∨ (UNC (B'=>P) ∨ UNC (K=>P))
supindhelper a=>b a=>b' edge b'=>p ker=>p = SupInd (record
                                                      { A=>B = a=>b ; A=>B' = a=>b' ; edge = edge ; B'=>P = b'=>p ; Ker=>P = ker=>p })
                                                      
syntax supindhelper a=>b a=>b' edge b'=>p ker=>p =
  ROUNDTRIP a=>b JUMPBACK a=>b' ∶  b'=>p MOVECHILDREN edge , ker=>p
