{-# OPTIONS --cubical --without-K --safe #-}
open import CubicalBasics.cubical-prelude hiding (ΣPathP ; PathPΣ)
-- open import Cubical.Data.Prod 
module CubicalBasics.IsomorphismCubical where
module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  section : (f : A → B) → (g : B → A) → Type ℓ'
  section f g = ∀ b → f (g b) ≡ b

  -- NB: `g` is the retraction!
  retract : (f : A → B) → (g : B → A) → Type ℓ
  retract f g = ∀ a → g (f a) ≡ a
  

  record Iso : Type (ℓ ⊔ ℓ') where
    no-eta-equality
    constructor iso
    field
      fun : A → B
      inv : B → A
      rightInv : section fun inv
      leftInv  : retract fun inv
  
  module _ (i : Iso) where
    open Iso i renaming ( fun to f
                        ; inv to g
                        ; rightInv to s
                        ; leftInv to t)

    private
      module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
        fill0 : I → I → A
        fill0 i = hfill (λ k → λ { (i = i1) → t x0 k
                                 ; (i = i0) → g y })
                        (inS (g (p0 (~ i))))

        fill1 : I → I → A
        fill1 i = hfill (λ k → λ { (i = i1) → t x1 k
                                 ; (i = i0) → g y })
                        (inS (g (p1 (~ i))))

        fill2 : I → I → A
        fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
                                 ; (i = i0) → fill0 k i1 })
                        (inS (g y))

        p : x0 ≡ x1
        p i = fill2 i i1

        sq : I → I → A
        sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                                ; (i = i0) → fill0 j (~ k)
                                ; (j = i1) → t (fill2 i i1) (~ k)
                                ; (j = i0) → g y })
                       (fill2 i j)

        sq1 : I → I → B
        sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 (~ j)) k
                                 ; (i = i0) → s (p0 (~ j)) k
                                 ; (j = i1) → s (f (p i)) k
                                 ; (j = i0) → s y k })
                        (f (sq i j))

        lemIso : (x0 , p0) ≡ (x1 , p1)
        lemIso i = (p i , λ j → sq1 i (~ j)) 

    isoToIsEquiv : isEquiv f
    isoToIsEquiv = record { equiv-proof = λ y → ((g y) , (s y)) , (λ z → lemIso y (g y) (proj₁ z) (s y) (proj₂ z)) }

module _ {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ A B} where
  pr₁ = proj₁
  pr₂ = proj₂
  ΣPathP : Σ (pr₁ x ≡ pr₁ y) (λ p → PathP (λ i → B (p i)) (pr₂ x) (pr₂ y))
         → x ≡ y
  ΣPathP (p , q) i = (p i) , (q i)

  PathPΣ : x ≡ y
         → Σ (pr₁ x ≡ pr₁ y) (λ p → PathP (λ i → B (p i)) (pr₂ x) (pr₂ y))
  PathPΣ q = (cong pr₁ q) , apf pr₂ q

  ΣPathP-PathPΣ : ∀ p → PathPΣ (ΣPathP p) ≡ p
  ΣPathP-PathPΣ (p , q) = refl

  PathPΣ-ΣPathP : ∀ p → ΣPathP (PathPΣ p) ≡ p
  PathPΣ-ΣPathP q = refl
  myEq : (Σ (pr₁ x ≡ pr₁ y) (λ p → PathP (λ i → B (p i)) (pr₂ x) (pr₂ y))) ≃ (x ≡ y)
  myEq = ΣPathP , isoToIsEquiv (iso ΣPathP PathPΣ PathPΣ-ΣPathP ΣPathP-PathPΣ) -- , (record { equiv-proof =  , λ y₂ → {!ΣPathP ? !} })


module _ {o} {ℓ} ((Carrier , CarIsSet) : Sets ℓ ) (X' : Carrier → Sets o) where

  private variable
     k j : Carrier
  private
    X : Carrier → Set o
    X k = proj₁ (X' k)
    helper : (k : Carrier) → isSet (X k)
    helper k = proj₂ (X' k)
    Elts = Σ Carrier X
  PathPAreProp : (p : k ≡ j) → (x : X k) → (y : (X j)) → isProp (PathP (λ i → (X (p i))) x y)
  PathPAreProp p x y ϕ ψ i i' =  isProp→PathP {A = λ i' →   ϕ i' ≡ ψ i'  } (λ i' → helper (p i') (ϕ i') (ψ i')) refl refl  i' i

  eltsIsSet : isSet (Elts)
  eltsIsSet (k , x) (j , y) p q =  ((sym (PathPΣ-ΣPathP p)) ∙ cong (ΣPathP) (ΣPathP (hmtpy , isProp→PathP (λ i →  PathPAreProp (hmtpy i) x y ) (proj₂ p') (proj₂ q')))) ∙ (PathPΣ-ΣPathP q )  where

    p' :  Σ (k ≡ j)
           (λ p₁ → PathP (λ i → (X (p₁ i))) x y)
    p' = PathPΣ p -- (  i i') , {!proj₂ (X' ?)!}
    q' :  Σ (k ≡ j)
           (λ p₁ → PathP (λ i → (X (p₁ i))) x y)
    q' = PathPΣ q
    hmtpy : proj₁ p' ≡ proj₁ q'
    hmtpy = (CarIsSet _ _ (proj₁ p') (proj₁ q'))
Σset : {A : Set ℓ} {B : A → Set ℓ'} → isSet A →  ((a : A) → isSet (B a)) → isSet (Σ A B)
Σset {B = B} isSetA f = eltsIsSet (_ , isSetA) λ a → B a , f a
