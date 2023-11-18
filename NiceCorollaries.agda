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

open import SemiLattices
open import CubicalBasics.cubical-prelude hiding (_∨_ ; _∧_)
open import CubicalBasics.cubicalEqualityReasoning
open import HomoAlgStd

open import Grids hiding (_≤_)
open import Data.Nat.Base hiding (_! ; _≤_ ; _⊔_)
import UnivalentCarpet2
-- open import CarpetAufsatzExamples2
import SmartImplication
module NiceCorollaries {o e} (C : Carpet {o} {ℓ} {e})  where

  open UnivalentCarpet2 C
  open Monad truncMonad
  twoFactorizationLemma : {i j k : Carrier} → (f : i ≤ j) → (g : j ≤ k) → (A : SubPtd (𝕏 i)) →  f ↓* A ⊂ g ↑* pushforward ((ϕ g) ⊙∘ (ϕ f)) A
  twoFactorizationLemma {i = i} {j = j} {k = k} f g A = ezFactor {𝔸 = 𝕏 i} {𝔹 = 𝕏 j} {ℂ = 𝕏 k} A
  module Adj {i j : Carrier} (g : i ≤ j) (A : SubPtd (𝕏 i))  where
    open ARG
    unit : (i , A) ==> (i ,  g ↑* g ↓* A )
    unit =  IncUncert'' (
      ROUNDTRIP
      FWD' g ∷
      PB g (functPush (ϕ g) {A = A} Sth⊂Full) ∶
      refl=>'
      MOVECHILDREN
      re
      < intro⊂ ( funcPull  (ϕ g) {A = g ↓* A} 0⊂Sth) >)
      (R∨ re)
      {--
 ∷  ∶  refl=>'
--}
    adjunction : (B : SubPtd (𝕏 j)) → g ↓* A ⊂ B → A ⊂ g ↑* B
    adjunction B info  =  trans⊂ (to⊂' unit) (funcPull (ϕ g) info) 
  twoFactorizationLemma' : {i j k : Carrier} → (f : i ≤ j) → (g : j ≤ k) → (A : SubPtd (𝕏 i)) →  f ↓* A ⊂ g ↑* (f ■ g) ↓* A
  twoFactorizationLemma' f g A = subst (λ y → f ↓* A ⊂ g ↑* y) (leftFunc {A = A} f g) (to⊂' (Adj.unit g _))
