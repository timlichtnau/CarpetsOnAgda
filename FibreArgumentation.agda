{-# OPTIONS --cubical --without-K #-}
open import CarpetCubical3 
open import CubicalBasics.PointedTypesCubical
open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
open import Data.Product
open import CubicalBasics.PropositionReasoning
open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)
-- open import Relation.Binary.Core
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures using (IsPartialOrder)
open import Equalizer
open import SemiLattices
open import CubicalBasics.cubical-prelude hiding (_∨_ ; _∧_)
open import CubicalBasics.cubicalEqualityReasoning
open import CubicalBasics.IsomorphismCubical
open import HomoAlgStd

import Relation.Binary.Reasoning.Preorder


module _ {o e} (C : Carpet {o} {ℓ} {e}) where

  module _ (j : SemiLattice.Carrier (Carpet.J C)) where
    

      C' : Carpet {o ⊔ e} {ℓ} {e}
      C' =  record { J = record
                          { Carrier = Car<j
                          ; CarIsSet = eltsIsSet (Carrier , CarIsSet) λ x → x ≤ j , isProp→isSet ≤isProp
                          ; _≤_ = λ x x₁ → proj₁ x ≤ proj₁ x₁
                          ; ≤isProp = λ x y →  ≤isProp x y 
                          ; reflexivity = reflexivity
                          ; _■_ = _■_
                          ; _∨_ = λ x x₁ → (proj₁ x ∨ proj₁ x₁) , (sup (proj₂ x) (proj₂ x₁))
                          ; comm = λ {i = k} {j = k'} i → comm {i = proj₁ k} {j = proj₁ k'} i , isProp→PathP (λ k → ≤isProp {x = comm k} {y = j}) (sup (proj₂ k) (proj₂ k')) ( (sup (proj₂ k') (proj₂ k))) i
                          ; uB = uB
                          ; sup = sup
                          } ; X = λ x → X (proj₁ x) ; XisSet = λ i → XisSet (proj₁ i) ; pts = λ i → pts (proj₁ i)  ; myCarp = record { ϕ = ϕ ; reflex = reflex ; transit = transit} }   where
            open CarpetHelper C
            Car<j : Type (o ⊔ e)
            Car<j = Σ[ k ∈ Carrier ] (k ≤ j)

   
    
--    data _≲_ (x : Elts) (p : Car<j) : Set e where
  --    intro : elem x < proj₁ p → x ≲ p



  module _ where
    
   
    module _ where
      open CarpetHelper C
      private variable
        i j k l : Carrier

      fmapElUnder : k ≤ j → ElUnder k → ElUnder j
      fmapElUnder p x = elem x , (inScope x ■ p)

    module _ (j : SemiLattice.Carrier (Carpet.J C)) where
      open CarpetHelper (C' j)
      open CarpetOn myCarp

      𝔼 : Ptd {o ⊔ e}
      𝔼 = ptd (Elts , EltsIsSet) (((j , SemiLattice.reflexivity (Carpet.J C))) , pt ( CarpetHelper.𝕏 C j))
{--
      π : 𝔼 ⊙→ 𝕏 j
      π = (λ (x , p) →  ⟦ ϕ (proj₂ x) ⟧ p  ) , (reflex _)

      postulate tpFib : {k : Car<j } → (x : Elts) → (q : x ≲ k) → x ≣[ π ] (x §§ q)


--}
