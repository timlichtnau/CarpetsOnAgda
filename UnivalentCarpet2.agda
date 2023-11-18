{-# OPTIONS --cubical --without-K #-}
open import CarpetCubical3
open import CubicalBasics.PointedTypesCubical
open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
open import Data.Product
open import Agda.Builtin.Unit
open import CubicalBasics.PropositionReasoning
open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)

open import Function.Base using (_∘_)
open import Relation.Binary.Definitions 
open import Relation.Binary.Structures using (IsPartialOrder ; IsPreorder)
open import Equalizer3
open import SemiLattices
open import CubicalBasics.cubical-prelude hiding (_∨_ ; _∧_)
open import CubicalBasics.cubicalEqualityReasoning
open import HomoAlgStd

import Relation.Binary.Reasoning.Base.Single
import HomoAlgOnCarpets
import SmartImplication
open import Relation.Binary renaming (_⇒_ to _==>_)
open import DoublePreorderReasoning
open import FibreArgumentation
import FiberInduction
import SupporterInduction
import NaiveImplication
module UnivalentCarpet2 {o e} (carpet : Carpet {o} {ℓ} {e} ) where
open HomoAlgOnCarpets carpet public
open CarpetHelper carpet  public
open SmartImplication carpet public
open NaiveImplication carpet public
open SupporterInduction carpet public
open FiberInduction carpet public
import Chains2
open Chains2 J public
--private variable
--  j k l : Carrier

open Monad (truncMonad)

-- module _ {start end : Carrier}  where
-- a Filler at a point x₁ : X i₁ under a chain i₁ / l₁ \ i₂ / l₂ \ ... \ iₙ consists of points xⱼ in Xᵢ_ⱼ such that xⱼ ≡[ lⱼ ] x_{suc j} 
Tot : ∀ {ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ') → Set (ℓ ⊔ ℓ')
Tot B = Σ _ B
FillerBundleAt : {i j : Carrier} → Chain i j → X i → X j → Set (o ⊔ e)
FillerBundleAt {i = i} (emptyChain i) x y = (i , x) ≡[ i ] (i , y)

FillerBundleAt (x :: (k , l)) xj y = (Σ[ Y ∈ Tot (FillerBundleAt x xj) ] ((k , y) ≡[ l ] (_ , proj₁ Y)))

FillerAt : {i j : Carrier} → Chain i j → X i → Set (o ⊔ e)
FillerAt C x = Tot (FillerBundleAt C x)


end : {i j : Carrier} {C : Chain i j} {xi : X i} → (FillerAt C xi) → X j
end = fst
Filler : {i j : Carrier} → Chain i j → Set (o ⊔ e)
Filler {i = i} C = (x : X i) → (FillerAt C x)
{--
{C = emptyChain _} {xi = xi}  F = xi
end {C = C :: hehe}  = fst
--}


{--
data _=>'2[_]_
    data _⇒[_]_ : (A : SubPtd (𝕏 start)) → (C : Chain start end) → (B : SubPtd (𝕏 end)) → Set {!!} where
      singleIntro : (l : Above (start ∨ end)) → ∀ {A B} → (start , A) =>'[ proj₁ l ] (end , B) → A ⇒[ single start end l ] B
      
--}      
module ARG where
  -- open Relation.Binary.Reasoning.Base.Single (_=>'_) refl=>' trans=>' public -- (λ p q → trans=>' q p) public
  -- ¶ : Preorder (suc zero ⊔ o) (suc zero ⊔ o) (suc zero ⊔ o ⊔ e) -- PreOrderOn SubEl (suc zero ⊔ o ⊔ e)
  -- ¶ = PreOrderOnToPreOrder (_=>'_ , (refl=>' , trans=>'))
  open Relation.Binary.Reasoning.Base.Single _=>'_ refl=>' trans=>' hiding (_IsRelatedTo_) public

 -- syntax step-∼˘ z y∼z x∼y = x∼y ~⟨ y∼z ⟩ z
  infixl 2 step-∼˘ transsyntax
  infixl 1 lets_
  infixl 3 start_ beginBackwards_
  beginBackwards_ : ∀ x → x =>' x
  beginBackwards x = refl=>'
  transsyntax : ∀ {x y} z → x =>' y → y =>' z →  x =>' z
  transsyntax _ p q = trans=>' p q
 ---discouraged:
  syntax transsyntax z p q = p ~⟨ q ⟩ z

  data _IsRelatedTo_ (x y : SubEl) : Set (suc zero ⊔ o ⊔ e) where
    relTo : (x∼y : x =>' y) → x IsRelatedTo y
  start_ : ∀ x → x IsRelatedTo x
  start_ x = relTo refl=>'    
  lets_ : ∀ {x y} → x IsRelatedTo y → x =>' y
  lets (relTo p) = p
  step-∼˘ : ∀ {x y} z → y =>' z → x IsRelatedTo y → x IsRelatedTo z
  step-∼˘ z (y∼z) (relTo x∼y) = relTo (trans=>' x∼y y∼z)

  


 
