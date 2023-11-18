{-# OPTIONS --cubical #-}
{-# OPTIONS --cubical --without-K #-}
open import CubicalBasics.cubical-prelude
open import CubicalBasics.IsomorphismCubical
open import Data.Empty
module CubicalBasics.Integrals where
-- Natural numbers. We use the built in ones to be able to use
-- numerals.

open import Data.Nat.Base  using (ℕ; zero; suc; _+_)  renaming (_*_ to _·_ ; _≤_ to _≤ℕ_)

_-_ : ℕ → ℕ → ℕ
n     - zero = n
zero  - suc m = zero
suc n - suc m = n - m

-- {-# BUILTIN NATMINUS _-_ #-}


-- Integers (slightly different from how Dan did them in order to have
-- one less constructor to pattern match on)
data ℤ : Type where
  pos    : (n : ℕ) → ℤ
  negsuc : (n : ℕ) → ℤ

sucℤ : ℤ → ℤ
sucℤ (pos n)          = pos (suc n)
sucℤ (negsuc zero)    = pos zero
sucℤ (negsuc (suc n)) = negsuc n

predℤ : ℤ → ℤ
predℤ (pos zero)    = negsuc zero
predℤ (pos (suc n)) = pos n
predℤ (negsuc n)    = negsuc (suc n)

sucPred : ∀ i → sucℤ (predℤ i) ≡ i
sucPred (pos zero)    = λ i → pos zero
sucPred (pos (suc n)) = λ i → pos (suc n)
sucPred (negsuc n)    = λ i → negsuc n

predSuc : ∀ i → predℤ (sucℤ i) ≡ i
predSuc (pos n)          = λ i → pos n
predSuc (negsuc zero)    = λ i → negsuc zero
predSuc (negsuc (suc n)) = λ i → negsuc (suc n)

sucPath : ℤ ≡ ℤ
sucPath = ua (sucℤ , isoToIsEquiv (iso sucℤ predℤ sucPred predSuc))

_+ℤ_ : ℤ → ℤ → ℤ
m +ℤ pos n = m +pos n
  where
  _+pos_ : ℤ → ℕ  → ℤ
  z +pos 0 = z
  z +pos (suc n) = sucℤ (z +pos n)
m +ℤ negsuc n = m +negsuc n
  where
  _+negsuc_ : ℤ → ℕ → ℤ
  z +negsuc 0 = predℤ z
  z +negsuc (suc n) = predℤ (z +negsuc n)



+-suc : ∀ m n → suc (m + n) ≡ m + suc n
+-suc zero n i = suc n
+-suc (suc m) n i = suc (+-suc m n i)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero zero i = 0
+-comm zero (suc n) i = suc (+-comm zero n i)
+-comm (suc m) zero i = suc (+-comm m zero i)
+-comm (suc m) (suc n) i =
  suc (((λ i →  (+-suc m n) (~ i))
  ∙ (λ j → suc (+-comm m n j))
  ∙ +-suc n m) i)

+-zero : ∀ m → m + 0 ≡ m
+-zero zero i = zero
+-zero (suc m) i = suc (+-zero m i)

+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc zero n o i    = n + o
+-assoc (suc m) n o i = suc (+-assoc m n o i)

addPath : ℕ → ℤ ≡ ℤ
addPath zero = refl
addPath (suc n) = addPath n ∙ sucPath

predPath : ℤ ≡ ℤ
predPath = ua (predℤ , isoToIsEquiv (iso predℤ sucℤ predSuc sucPred))

subPath : ℕ → ℤ ≡ ℤ
subPath zero = refl
subPath (suc n) = subPath n ∙ predPath

_+ℤ'_ : ℤ → ℤ → ℤ
m +ℤ' pos n    = transport (addPath n) m
m +ℤ' negsuc n = transport (subPath (suc n)) m

-- This agrees with regular addition defined by pattern-matching
+ℤ'≡+ℤ : _+ℤ'_ ≡ _+ℤ_
+ℤ'≡+ℤ i m (pos zero) = m
+ℤ'≡+ℤ i m (pos (suc n)) = sucℤ (+ℤ'≡+ℤ i m (pos n))
+ℤ'≡+ℤ i m (negsuc zero) = predℤ m
+ℤ'≡+ℤ i m (negsuc (suc n)) = predℤ (+ℤ'≡+ℤ i m (negsuc n))


-- So +ℤ' with a fixed element is an equivalence
isEquivAddℤ' : (m : ℤ) → isEquiv (λ n → n +ℤ' m)
isEquivAddℤ' (pos n)    = isEquivTransport (addPath n)
isEquivAddℤ' (negsuc n) = isEquivTransport (subPath (suc n))

isEquivAddℤ : (m : ℤ) → isEquiv (λ n → n +ℤ m)
isEquivAddℤ = subst (λ add → (m : ℤ) → isEquiv (λ n → add n m)) +ℤ'≡+ℤ isEquivAddℤ'

_≤_ : ℤ → ℤ → Type
pos n ≤ pos n₁ = n ≤ℕ n₁ 
pos n ≤ negsuc n₁ = 𝟏
negsuc n ≤ pos n₁ = ⊥
negsuc n ≤ negsuc n₁ = n₁ ≤ℕ n
