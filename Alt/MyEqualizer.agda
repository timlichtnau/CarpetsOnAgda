{-# OPTIONS --cubical --without-K #-}
open import CarpetCubical3 
open import PointedTypesCubical
open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
open import Data.Product
open import PropositionReasoning
open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)
-- open import Relation.Binary.Core
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures using (IsPartialOrder)
open import Equalizer
open import SemiLattices
open import cubical-prelude hiding (_∨_ ; _∧_)
open import cubicalEqualityReasoning
open import HomoAlgStd
open import PropositionReasoning
import Relation.Binary.Reasoning.Preorder

module _ (C : Carpet {o} {ℓ} {e}) where
  open Carpet C 
  open SemiLattice J
  open Funs J
  open CarpetHelper C
  open _≡[_]_ 
  private variable
    i j k l : Carrier
  module _ (f : l ≤ k) {x y : ElUnder l} where
        myeqToPush≡ :  elem x ≡[ k ] elem y → push x ≡[ k ] push y
        myeqToPush≡ (x=y) = record { left = f ; right = f ; eq =
          push x § f
            ≡⟨ actrans (inScope x) f ⟩
          elem x § (inScope x ■ f)
            ≡⟨  eq' x=y  ⟩
          elem y § (inScope y ■ f)
            ≡˘⟨ actrans (inScope y) f ⟩ 
          push y § f ∎ } where open Reasoning
        Push≡ToMyEq : push x ≡[ k ] push y → elem x ≡[ k ] elem y
        Push≡ToMyEq  moin = (record { left = inScope x ■ left moin ; right = inScope y ■  right moin ; eq =
                elem x § (inScope x ■ left moin) ≡˘⟨ actrans (inScope x) (left moin) ⟩ elem x § inScope x § left moin ≡⟨ eq moin ⟩ elem y § inScope y § right moin ≡⟨ actrans (inScope y) (right moin) ⟩ elem y § (inScope y ■ right moin)   ∎ }) where open Reasoning

        data MyEqualizer {l k : Carrier} (f : l ≤ k) (x y : ElUnder l) : Set (o ⊔ e) where
          jo : (elem x) ≡[ k ] (elem y)  → MyEqualizer f x y
        MyEqualIsProp : {l k : Carrier} (f : l ≤ k) (x y : ElUnder l) → isProp (MyEqualizer f x y)
        MyEqualIsProp f x y (jo p) (jo q) = cong jo (≡[_]IsProp _ _ _ p q)
  myEq≅Push≡ : {f : l ≤ k} {x y : ElUnder l} → (elem x ≡[ k ] elem y) ≅ (push x ≡[ k ] push y)
  myEq≅Push≡ {f = f} {x = x} {y = y} =  myeqToPush≡ f  , Push≡ToMyEq f , ((λ _ → ≡[_]IsProp _ _ _ _ _) , λ _ → ≡[_]IsProp  _ _ _ _ _  ) -- (record { equiv-proof = λ z → (( z) , ) , λ y₁ → {!!} })

