{-# OPTIONS --cubical --without-K #-}
open import CubicalBasics.PointedTypesCubical
-- open import Relation.Binary.PropositionalEquality
open import CubicalBasics.cubical-prelude
module Equalizer3 where
--data  _≡
open Ptd
-- open import Level

-- open import Data.Product
--open import Relation.Binary.Order.Pr
open import HomoAlgStd hiding (fib)
open import Cubical.Relation.Binary.Order.Preorder 
open _⊙→_
open SubPtd
private variable
  o l e : Level

module _  {𝔸 : Ptd {o}} {𝔹 : Ptd {o}} where
 A = U⊙ 𝔸
 B = U⊙ 𝔹
 module _(f : 𝔸 ⊙→ 𝔹) where
   data fib  :  U⊙ 𝔸 → U⊙ 𝔸 → Set (o) where
     kern : {x y : U⊙ 𝔸} → (pf : pt 𝔹 ≡ ⟦ f ⟧ x) →  pt 𝔹 ≡ ⟦ f ⟧ y → fib x y
     inh : {y : U⊙ 𝔸} → fib y y


 --  syntax fib x y = x ≣ y
   syntax fib f x y = x ≣[ f ] y
   toFib : {x y : A} → fib x y → ⟦ f ⟧ x ≡ ⟦ f ⟧ y
   toFib (kern pf p) =  sym pf ∙ p 
   toFib (inh) = refl
   inh' : {x y : A} → x ≡ y → fib x y
   inh' p = subst (λ a → fib _ a) p inh
   postulate FibAxiom : ∀ {x y} →  isEquiv (toFib {x} {y} )
   fibInverse : ∀ {x y} → ⟦ f ⟧ x ≡ ⟦ f ⟧ y → fib x y
   fibInverse =  invEquiv FibAxiom
   isPropValued : ∀ (a b : A) →  isProp (fib a b)
   isPropValued a b = subst isProp (sym (ua ( (_ , FibAxiom))) ) (UisSet 𝔹 _ _)

 module _ {f : 𝔸 ⊙→ 𝔹} where
     _̇_ : {x y z : A} → fib f x y → fib f y z → fib f x z
     kern p x ̇ kern q y = kern p y
     kern p x ̇ inh =  kern p x 
     inh ̇ q = q


 ℙ : (f : 𝔸 ⊙→ 𝔹) → Preorder o o -- (ℓ-max o l) -- (o ⊔ l)
 ℙ f = A , (preorderstr (fib f) (ispreorder ( UisSet 𝔸  ) (λ a b → isPropValued f a b) (λ _ → inh' f (refl)) (λ _ _ _ → _̇_))) -- record { Carrier = A ; _≈_ = _≡_ ; _∼_ = fib f ; isPreorder = record { isEquivalence = ≡isEq ; reflexive =  inh' f ; trans =  _̇_ } }

   -- test : {𝔸 𝔹 : Ptd} {x y : U⊙ 𝔸} (f : 𝔸 ⊙→ 𝔹) → x ≡[ f ] y 
     --postulate PathsFrom0IndEmb : {y : A} → isEquiv (cong {x = pt 𝔸} {y = y} ⟦ f ⟧ )


module _  {𝔸 𝔸' 𝔹 : Ptd {o}} (g : 𝔸' ⊙→ 𝔸) (f : 𝔸 ⊙→ 𝔹) where
       f' = f ⊙∘ g
       FibTransport : {x y : U⊙ 𝔸'} → x ≣[ f' ] y → ⟦ g ⟧ x ≣[ f ] ⟦ g ⟧ y
       FibTransport (kern 0=f'x 0=f'y ) = kern 0=f'x 0=f'y  -- where open Relation.Binary.Reasoning.Preorder (ℙ f)
       FibTransport inh = inh
       module _ {ℂ : Ptd} (g : 𝔹 ⊙→ ℂ) where
         h : 𝔸 ⊙→ ℂ
         h = g ⊙∘ f 
     --    EpiInd : {im g 
     -- toFib' :  {𝔸 𝔹 : Ptd} (f : 𝔸 ⊙→ 𝔹) {x y : U⊙ 𝔸} → x ≣[ f ] y → ⟦ f ⟧ x ≡ ⟦ f ⟧ y
     -- toFib' = toFib 


