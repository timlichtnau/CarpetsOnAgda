{-# OPTIONS --cubical --without-K #-}
open import CubicalBasics.PointedTypesCubical
-- open import Relation.Binary.PropositionalEquality
open import CubicalBasics.cubical-prelude
open import Equalizer3
open import Data.Fin
open _⊙→_
open SubPtd
open import Data.Nat
private variable
  o l e : Level

pFin : ℕ → Ptd {lzero}
pFin n = record { U⊙ = Fin (suc n) ; UisSet = {!!} ; pt = zero }

bf : Fin 3 → Fin 2
bf zero = zero
bf (suc zero) = suc zero
bf (suc (suc x)) = suc zero
f : pFin 2 ⊙→ pFin 1
f = bf , refl

kerbf : {x : Fin 3} →  zero ≡ bf x → x ≡ zero
kerbf {zero} p = refl
kerbf {suc zero} p = {!!}
kerbf {suc (suc zero)} p = {!!}
a : U⊙ (pFin 2)
a = suc zero
b : U⊙ (pFin 2)
b = suc (suc zero)
p :  ⟦ f ⟧ a ≡ ⟦ f ⟧ b 
p = refl

h' : a ≣[ f ] b 
h' = fibInverse f p

stuff : {x y : Fin 3} → x ≣[ f ] y → x ≡ y
stuff {zero} {zero} (kern pf z) = refl
stuff {zero} {suc zero} (kern pf z) = sym (kerbf z) --absurd
stuff {zero} {suc (suc y)} (kern pf z) = sym (kerbf z) --absurd
stuff {suc x} {zero} (kern pf z) = kerbf pf  
stuff {suc x} {suc y} (kern pf z) = kerbf pf ∙ sym (kerbf z)
stuff inh = refl

contradiction : a ≡ b
contradiction = stuff h'
