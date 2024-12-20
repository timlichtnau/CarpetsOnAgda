{-# OPTIONS --cubical #-}
open import CubicalBasics.cubical-prelude hiding (_∨_)
open import SemiLattices

module _ {e} (J : SemiLattice ℓ ℓ' e) where
  open SemiLattice J
  Above : Carrier → Set (ℓ ⊔ e)
  Above j = Σ[ l ∈ Carrier ] (j ≤ l) 
  data Chain : (i j : Carrier) → Set (ℓ ⊔ e) where
    single : (i j : Carrier) → Carrier → Chain i j
    _::_ : ∀ {i j} → Chain i j → ((k , j) : Σ[ k ∈ Carrier ] (Above (k ∨ j))) → Chain i k
  data _⊂_ : ∀ {i j k} → Chain i j → Chain i k → Set (e ⊔ ℓ) where
    all : ∀ {i j} → (C : Chain i j) → C ⊂ C
    red : ∀ {i j sth} → (C : Chain i j) → C ⊂ (C :: sth)
    transi : ∀ {i j k l} → (C : Chain i l) →  (C' : Chain i k) → (C'' : Chain i j)
      →  C' ⊂ C → C'' ⊂ C' → C'' ⊂ C
      
--  data Filler : ∀ {i j} → Chain i j → Set ? where
