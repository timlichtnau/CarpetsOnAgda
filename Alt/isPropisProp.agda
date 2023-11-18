{-# OPTIONS --cubical #-}

{---

Das Skript ist in Cubical agda geschrieben, d.h. ein Pfad p : x ≡ y in A ist zu verstehen als eine Map p : I → A mit p (i0) = x und p (i1) = y, wobei die Gleichheiten 'judgementally / definitionally' gelten.
--}
open import Level
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical public
  renaming ( 
            primHComp      to hcomp
  )

private variable
  ℓ : Level
isProp : Set ℓ → Set ℓ
isProp A = (x y : A) → x ≡ y

isSet : Set ℓ → Set ℓ
isSet A = (x y : A) → isProp (x ≡ y) 
isProp→isSet : ∀ {o} → {A : Set o} → isProp A → isSet A
isProp→isSet h a b p q j i =
    hcomp (λ k → λ { (i = i0) → h a a k
                   ; (i = i1) → h a b k
                   ; (j = i0) → h a (p i) k
                   ; (j = i1) → h a (q i) k }) a

--    hcomp ist homogenous composition und entspricht dem Füllen von Hörnern in Kancomplexen, bloß halt mit Würfeln statt simplices (VL 9?)

isPropisProp : ∀ {ℓ'} {A : Set  ℓ' } → isProp (isProp A)
isPropisProp {A = A} x y i a b = isProp→isSet x a b (x a b) (y a b) i  
isSetIsProp : ∀ {ℓ'} {A :  Set ℓ' } → isProp (isSet A)
isSetIsProp {A = A} p q i x y = isPropisProp (p x y) (q x y) i
