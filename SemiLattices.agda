{-# OPTIONS --cubical #-}
open import Level
open import CubicalBasics.cubical-prelude hiding (_∨_)
open import Data.Product
open import CubicalBasics.PointedTypesCubical
open import CubicalBasics.PropositionReasoning using (isSetIsProp)
-- open import CubicalBasics.CubicalFun

private variable
  o l e : Level
  
record SemiLattice (o l e : Level) : Type (suc o ⊔ suc e ⊔ suc l) where
  field
    Carrier : Set o
    CarIsSet : isSet (Carrier)
    _≤_ : Carrier → Carrier → Type e
  infixl 5 _≤_
  field
    ≤isProp : {x y : Carrier} → isProp (x ≤ y)
    reflexivity : {i : Carrier} → i ≤ i
    _■_ : {i j k : Carrier} → i ≤ j → j ≤ k → i ≤ k  
    _∨_ : Carrier → Carrier → Carrier
  infixl 20 _∨_
  infixl 20 _■_
  re = reflexivity
  field
    comm : ∀ {i} {j} → i ∨ j ≡ j ∨ i
    uB : ∀ {i} {j} → i ≤ (i ∨ j) 
    sup : ∀ {i} {j} {k} → i ≤ k → j ≤ k → (i ∨ j) ≤ k

module Funs (J : SemiLattice o ℓ e) where
  open SemiLattice J
  subst≤ : ∀ {e'} → {x y : Carrier} {p q : x ≤ y} → (A : x ≤ y → Set e' ) → A p → A q
  subst≤ A = subst A (≤isProp _ _)
  PathTo≤ : {x y : SemiLattice.Carrier J} → x ≡ y → SemiLattice._≤_ J x y
  PathTo≤ {x = x} {y = y} p = (subst (λ a → SemiLattice._≤_ J x a ) p (SemiLattice.reflexivity J))
  convertEq : {j k  : Carrier} → j ≡ k → j ≤ k × k ≤ j
  convertEq =  λ p → PathTo≤ p , PathTo≤ (sym p) 
  uB' :  ∀ {i j} → j ≤ (i ∨ j)
  uB' {k} {j'} = uB {j'} {k} ■ PathTo≤ comm

  left-Eat : ∀ {i j} → i ≤ j → i ∨ j ≤ j
  left-Eat p = sup  p reflexivity
  infix 21 _∨R
  _∨R = left-Eat
  right-Eat : ∀ {i j} → i ≤ j → j ∨ i ≤ j
  right-Eat p = sup reflexivity p
  resp : ∀ {i j k l} → i ≤ k → j ≤ l → i ∨ j ≤ k ∨ l
  resp p q = sup (p ■ uB) uB' ■ sup uB (q ■ uB')
  R∨_ = right-Eat
  infix 22 R∨_
  right-map : ∀ {i j k} → j ≤ k → i ∨ j ≤ i ∨ k 
  right-map p = sup uB (p ■ uB')
  left-map :  ∀ {i j k} → j ≤ k → j ∨ i ≤ k ∨ i
  left-map p = sup (p ■ uB) uB'
