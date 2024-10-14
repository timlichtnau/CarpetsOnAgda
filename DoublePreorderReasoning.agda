{-# OPTIONS --without-K --cubical #-}
open import CubicalBasics.cubical-prelude hiding (_∨_ ; _∧_)
--import Relation.Binary.Reasoning.Preorder
-- open import Relation.Binary
-- open import Data.Product
-- open import Level
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Preorder
--open import Relation.Binary.PropositionalEquality
module DoublePreorderReasoning where
private variable
  o e : Level
record PreOrderOn {o} (A : Set o) (ℓ : Level) : Set (o ⊔ suc ℓ) where
  constructor _,_
  field   
    _~_ : Cubical.Relation.Binary.Base.Rel A A ℓ
    iPO : BinaryRelation.isRefl _~_ ×  BinaryRelation.isTrans _~_

-- isPreOrder :  IsPreorder _≡_ _~_
-- is
PreOrderOnToPreOrder : {A : Set o} → PreOrderOn A ℓ → Preorder o ℓ
PreOrderOnToPreOrder P = ? where -- record { Carrier = _ ; _≈_ = _≡_ ; _∼_ =  _~_ ; isPreorder = record { isEquivalence = isEquivRelation ; reflexive = re ; trans = proj₂ iPO } } where
  open PreOrderOn P
  re : ∀ {x y} → x ≡ y → x ~ y
  re refl = {! proj₁ iPO !}
module DoubleReasoning {o ℓ} (A : Set o) ((_≤_ , P ) : PreOrderOn A ℓ) ((_~_ , Q) : PreOrderOn A e) (imp : ∀ {x y z} → (x ≤ y) → y ~ z → x ~ z)  where
  
  open Cubical.Relation.Binary.Order.Preorder.PreorderReasoning (PreOrderOnToPreOrder (_~_ , Q)) public --.
  --open 


  infixr 2 _≤⟨_⟩_ -- _≤⟨⟩_

 -- _≤⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ~ y
 -- x ≤⟨⟩ x≡y = imp (subst (x ≤_) x≡y ((IsPreorder.reflexive P) refl))

  _≤⟨_⟩_ : {y z : A} → (x : A) → (x ≤ y) → (y ≲ z) → (x PreorderStr.≲ z)
  --x ≤⟨ x≤y ⟩ {! (nonstrict y~z) !} =  nonstrict (imp x≤y y~z)  -- {! x ∼⟨ (imp x≤y) ⟩ y~z !}
  --x ≤⟨ x≤y ⟩ (equals as) = nonstrict (imp (subst (x ≤_) as x≤y) (proj₁ Q))
