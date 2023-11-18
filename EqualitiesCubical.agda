{-# OPTIONS --cubical #-}
open import CubicalBasics.cubical-prelude
open import CubicalBasics.IsomorphismCubical
module _ where
  private variable
    A : Set ℓ
    a b : A
  Builtin≡ToCubical≡ : a ≡' b → a ≡ b
  Builtin≡ToCubical≡ refl' = refl
  Cubical≡ToBuiltin≡ : a ≡ b →  a ≡' b
  Cubical≡ToBuiltin≡ {a = a} p = Jrule (λ y _ → a ≡' y) refl' p

  Cub-Builtin : (p : a ≡ b) → Builtin≡ToCubical≡ (Cubical≡ToBuiltin≡ p) ≡ p 
  Cub-Builtin {a = a} p = Jrule
    (λ y q → Builtin≡ToCubical≡ (Cubical≡ToBuiltin≡ q) ≡ q )
    (cong Builtin≡ToCubical≡ ((JRefl ((λ y _ → a ≡' y)) _)))
    p
  Builtin-Cub : (p : a ≡' b) →  Cubical≡ToBuiltin≡ (Builtin≡ToCubical≡ p) ≡ p
  Builtin-Cub {a = a} refl' = JRefl ((λ y _ → a ≡' y)) _
  EqEquiv : (a ≡' b) ≃ (a ≡ b)
  EqEquiv = Builtin≡ToCubical≡ , isoToIsEquiv (iso Builtin≡ToCubical≡  Cubical≡ToBuiltin≡ Cub-Builtin Builtin-Cub)
