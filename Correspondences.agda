{-# OPTIONS --cubical #-}
open import HomoAlgStd
open import CubicalBasics.cubical-prelude
open import CubicalBasics.IsomorphismCubical
open import CubicalBasics.PointedTypesCubical
open import CubicalBasics.PropositionReasoning
module Correspondences where
module _ (A B : Ptd {ℓ}) where
  record _⟩_  : Set (lsuc ℓ) where
    field
      Tot : Ptd {ℓ}
      bwd : Tot ⊙→ A
      fwd : Tot ⊙→ B
      su : surj bwd
open _⟩_

fibreProduct : {A B C : Ptd {ℓ}} → A ⊙→ B → C ⊙→ B → Ptd {ℓ}
fibreProduct {A = A} {B = B} {C = C} f g = record { U⊙ = Σ[ b ∈ U⊙ B ] ((fib (⟦ f ⟧) b) × fib (⟦ g ⟧) b)  ; UisSet = Σset (UisSet B) λ b → Σset (fibIsSet (UisSet A) (UisSet B) _ _) λ _ → fibIsSet (UisSet C) (UisSet B) _ _  ; pt = (pt B) , (((pt A) , (psv f)) , (pt C , psv g)) }

π₁ : {A B C : Ptd {ℓ}} {f : A ⊙→ B} {g : C ⊙→ B} → fibreProduct f g ⊙→ A
π₁ = (λ x → proj₁ (proj₁ (proj₂ x))) , refl
surjStableUnderBC : {A B C : Ptd {ℓ}} {f : A ⊙→ B} {g : C ⊙→ B} → surj g → surj (π₁ {f = f} {g = g})
surjStableUnderBC {f = f} {g = g} sug = ⊂: λ (x , _) →
   let b = ⟦ f ⟧ x in
   z ← (sug) & ((b , *)) ,
   return ((b , (x , refl) , z) , refl)
  where   open Monad truncMonad
π₂ : {A B C : Ptd {ℓ}} {f : A ⊙→ B} {g : C ⊙→ B} → fibreProduct f g ⊙→ C
π₂ = (λ x → proj₁ (proj₂ (proj₂ x))) , refl
_⟨∘⟩_ : {A B C : Ptd {ℓ}} → B ⟩ C → A ⟩ B → A ⟩ C
f ⟨∘⟩ g = record {
  Tot = fibreProduct (fwd g) (bwd f) ;
  bwd = bwd g ⊙∘ π₁  {f = fwd g} {g = bwd f} ;
  fwd = fwd f ⊙∘ π₂ {f = fwd g} {g = bwd f} ;
  su = surjComp
    {f = π₁ {f = fwd g} {g = bwd f}}
    {g = bwd g} (su g) (surjStableUnderBC {g = bwd f} (su f)) }  
