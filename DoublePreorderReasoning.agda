{-# OPTIONS --without-K #-}
-- open import cubical-prelude hiding (_∨_ ; _∧_)
import Relation.Binary.Reasoning.Preorder
open import Relation.Binary
open import Data.Product
open import Level
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality
module DoublePreorderReasoning where
private variable
  o ℓ e : Level
record PreOrderOn {o} (A : Set o) (ℓ : Level) : Set (o ⊔ suc ℓ) where
  constructor _,_
  field   
    _~_ : Rel A ℓ
    iPO : Reflexive _~_ × Transitive _~_

-- isPreOrder :  IsPreorder _≡_ _~_
-- is
PreOrderOnToPreOrder : {A : Set o} → PreOrderOn A ℓ → Preorder o o ℓ
PreOrderOnToPreOrder P = record { Carrier = _ ; _≈_ = _≡_ ; _∼_ =  _~_ ; isPreorder = record { isEquivalence = isEquivalence ; reflexive = re ; trans = proj₂ iPO } } where
  open PreOrderOn P
  re : ∀ {x y} → x ≡ y → x ~ y
  re refl = proj₁ iPO
module DoubleReasoning {o ℓ} (A : Set o) ((_≤_ , P ) : PreOrderOn A ℓ) ((_~_ , Q) : PreOrderOn A e) (imp : ∀ {x y z} → (x ≤ y) → y ~ z → x ~ z)  where
  
  open Relation.Binary.Reasoning.Preorder (PreOrderOnToPreOrder (_~_ , Q)) public
  


  infixr 2 _≤⟨_⟩_ -- _≤⟨⟩_

 -- _≤⟨⟩_ : ∀ (x : A) {y : A} → x ≡ y → x ~ y
 -- x ≤⟨⟩ x≡y = imp (subst (x ≤_) x≡y ((IsPreorder.reflexive P) refl))

  _≤⟨_⟩_ : {y z : A} → (x : A) → (x ≤ y) → (y IsRelatedTo z) → (x IsRelatedTo z)
  x ≤⟨ x≤y ⟩ (nonstrict y~z) =  nonstrict (imp x≤y y~z)  -- {! x ∼⟨ (imp x≤y) ⟩ y~z !}
  x ≤⟨ x≤y ⟩ (equals as) = nonstrict (imp (subst (x ≤_) as x≤y) (proj₁ Q))
