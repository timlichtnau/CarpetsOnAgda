{-# OPTIONS --cubical --without-K #-}
open import CubicalBasics.cubical-prelude
module CubicalBasics.cubicalEqualityReasoning where
-- Equality reasoning
module Reasoning where
  infix  3 _∎
  infixr 2 _≡⟨_⟩_ _≡⟨⟩_ _≡˘⟨_⟩_

  _≡⟨_⟩_ : {A : Type ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = x≡y ∙ y≡z
  _≡˘⟨_⟩_ : {A : Type ℓ} (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
  _ ≡˘⟨ y≡x ⟩ y≡z = (λ i → y≡x (~ i)) ∙ y≡z
  ≡⟨⟩-syntax : {A : Type ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  ≡⟨⟩-syntax = _≡⟨_⟩_

  infixr 2 ≡⟨⟩-syntax
  syntax ≡⟨⟩-syntax x (λ i → B) y = x ≡[ i ]⟨ B ⟩ y

  _≡⟨⟩_ : {A : Type ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _∎ : {A : Type ℓ} (x : A) → x ≡ x
  x ∎ = λ _ → x
