{-# OPTIONS --cubical #-}
open import SemiLattices
open import CubicalBasics.CubicalFun
open import Level
open import CubicalBasics.cubical-prelude hiding (_∨_)
open import Data.Product
open import CubicalBasics.PointedTypesCubical
open import CubicalBasics.PropositionReasoning using (isSetIsProp)
module _ where
  open SemiLattice
  EqualityOfSemiLattices : (J J' : SemiLattice o l e) → ((f , _) : Carrier J ≃ Carrier J') → (∀ x y → _≤_ J x y ≃ _≤_ J' (f x) (f y)) → J ≡ J'
  EqualityOfSemiLattices J J' ϕ ≤pf i = record
                                      { Carrier = ua ϕ i
                                      ; CarIsSet = isProp→PathP (λ j →  isSetIsProp) (CarIsSet J) (CarIsSet J') i
                                      ; _≤_ = {!wow!}
                                      ; ≤isProp = {!!}
                                      ; reflexivity = {!!}
                                      ; _■_ = {!!}
                                      ; _∨_ = {!!}
                                      ; comm = {!!}
                                      ; uB = {!!}
                                      ; sup = {!!}
                                      }
