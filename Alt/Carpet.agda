open import PointedTypes2 
open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
open import Data.Product

open import Level
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Relation.Binary.Core
open import Function.Base
open import Relation.Binary.Definitions
open import Basics hiding (_~_)
open Ptd
open _⊙→_
variable
  o l e : Level
record Carpet {o l e : Level} : Set (suc l ⊔ suc e ⊔ suc o) where
  constructor _,_
  field
    -- record {Carrier = I ; _≈_ =  _≈_ ; _≤_ = _≤_ ; isPartialOrder = isPartialOrder }  : Poset o l e
    I : Poset o l e
    X : (Poset.Carrier) I → Ptd
    ϕ : {i j : Poset.Carrier I} → (Poset._≤_ I) i j → X i ⊙→ X j
    reflex : {i : Poset.Carrier I} → ϕ ((Poset.refl I) {i}) ~ ⊙id (X i)
    transit : {i j k : Poset.Carrier I} → (p : (Poset._≤_ I) i j) → (q : (Poset._≤_ I) j k) → (r : (Poset._≤_ I) i k) → ϕ q ⊙∘ ϕ p ~ ϕ r
  
module _ (C : Carpet {o} {l} {e}) where
  open Carpet C
  open Poset I renaming (refl to reflexivity)
  transit' : {i j k : Poset.Carrier I} → (p : (Poset._≤_ I) i j) → (q : (Poset._≤_ I) j k) → ϕ q ⊙∘ ϕ p ~ ϕ (trans p q)
  transit' p q = transit p q (trans p q)
--  open Poset.PreOrder I hiding (Carrier)
  Elts : Set o
  Elts = Σ (Carrier) (U⊙ ∘ X)
  _≣_  : Rel Elts e
  (i , x) ≣ (j , y) = Σ[ p ∈ i ≤ j ] ⟦ ϕ p ⟧ x ≡ y
  refl≣ : Reflexive _≣_
  refl≣ {(_ , x)} = reflexivity , reflex x
  
  trans≣ : Transitive _≣_
  trans≣ {(i , x)} {(j , y)} {(k , z)} (p , ρ) (q , θ) =  trans p q , (sym (transit' p q x) ■ (ap ⟦ ϕ q ⟧ ρ ■ θ))
--  ≣-isPreorder : isPreOrder _≣_
  com≣ : (x y z : Elts) → fst y ≤ fst z → x ≣ y → x ≣ z → y ≣ z -- {i j k : Carrier} {x : U⊙ (X i)} → (p : i ≤ j) → (q : j ≤ k) → (
  com≣ x y z q (p , π) (r , ρ) = q , (sym (ap ⟦ ϕ q ⟧ π) ■ (transit p q r (snd x) ■ ρ) )
  
