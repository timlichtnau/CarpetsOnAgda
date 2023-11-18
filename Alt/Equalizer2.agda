{-# OPTIONS --cubical --without-K #-}
open import PointedTypesCubical
-- open import Relation.Binary.PropositionalEquality
open import cubical-prelude
module Equalizer2 where
--data  _≡
open Ptd
open import Level

open import Data.Product
open import Relation.Binary
open import CarpetCubical3
import Relation.Binary.Reasoning.Preorder 
open _⊙→_
open SubPtd
private variable
  o l e : Level

module _  {𝔸 : Ptd {o}} {𝔹 : Ptd {l}} where
 A = U⊙ 𝔸
 B = U⊙ 𝔹
 module _(f : 𝔸 ⊙→ 𝔹) where
   data fib  :  U⊙ 𝔸 → U⊙ 𝔸 → Set (o ⊔ l) where
     kern : {y : U⊙ 𝔸} →  pt 𝔹 ≡ ⟦ f ⟧ y → fib (pt 𝔸) y
     inh : {y : U⊙ 𝔸} → fib y y

 --  syntax fib x y = x ≣ y
   syntax fib f x y = x ≣[ f ] y
   toFib : {x y : A} → fib x y → ⟦ f ⟧ x ≡ ⟦ f ⟧ y
   toFib (kern p) = psv f ∙ p
   toFib (inh) = refl
   inh' : {x y : A} → x ≡ y → fib x y
   inh' p = subst (λ a → fib _ a) p inh
 module _ {f : 𝔸 ⊙→ 𝔹} where
  _̇_ : {x y z : A} → fib f x y → fib f y z → fib f x z
  kern x ̇ kern y = kern y
  kern x ̇ inh = kern x
  inh ̇ q = q

 ℙ : (f : 𝔸 ⊙→ 𝔹) → Preorder o o (o ⊔ l)
 ℙ f = record { Carrier = A ; _≈_ = _≡_ ; _∼_ = fib f ; isPreorder = record { isEquivalence = record { refl = refl ; sym = sym ; trans = _∙_ } ; reflexive =  inh' f ; trans =  _̇_ } }
-- test : {𝔸 𝔹 : Ptd} {x y : U⊙ 𝔸} (f : 𝔸 ⊙→ 𝔹) → x ≡[ f ] y 
  --postulate PathsFrom0IndEmb : {y : A} → isEquiv (cong {x = pt 𝔸} {y = y} ⟦ f ⟧ )


module _ {𝔸 𝔸' 𝔹 : Ptd {o}} (g : 𝔸' ⊙→ 𝔸) (f : 𝔸 ⊙→ 𝔹) where
    f' = f ⊙∘ g
    FibTransport : {x y : U⊙ 𝔸'} → x ≣[ f' ] y → ⟦ g ⟧ x ≣[ f ] ⟦ g ⟧ y
    FibTransport (kern p) = begin
      ⟦ g ⟧ (pt 𝔸')
        ∼⟨ inh' f (psv g) ⟩
      pt 𝔸
        ∼⟨ kern p ⟩
      ⟦ g ⟧ _ ∎  where open Relation.Binary.Reasoning.Preorder (ℙ f)
    FibTransport inh = inh
{--  module _ {ℂ : Ptd} (g : 𝔹 ⊙→ ℂ) where
    h : 𝔸 ⊙→ ℂ
    h = g ⊙∘ f --}
--    EpiInd : {im g 
-- toFib' :  {𝔸 𝔹 : Ptd} (f : 𝔸 ⊙→ 𝔹) {x y : U⊙ 𝔸} → x ≣[ f ] y → ⟦ f ⟧ x ≡ ⟦ f ⟧ y
-- toFib' = toFib 
