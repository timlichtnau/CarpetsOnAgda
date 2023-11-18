{-# OPTIONS --without-K --safe --cubical #-}
open import Level


open import Data.Sum

open import Function.Base using (id; _∘_)

open import Relation.Binary.Definitions
open import Data.Product
--open import Data.Function
open import CubicalBasics.PropositionReasoning
open import CubicalBasics.cubical-prelude
open import CubicalBasics.IsomorphismCubical
module CubicalBasics.PointedTypesCubical where
  private variable
   l l' : Level

  
  record Ptd {l} : Set (suc l) where
    field
      U⊙ : Set l
      UisSet : isSet U⊙ 
      pt : U⊙
    U⊙' : Sets l
    U⊙' = U⊙ , UisSet

  open Ptd public

 
  ptd : (A : Sets l) -> proj₁ A -> Ptd {l}
  ptd (A , B) x = record { U⊙ = A ; UisSet = B ; pt = x }


  infix 10 _⊙→_
 
  record _⊙→_ (X : Ptd {l} ) (Y : Ptd {l'}) : Set (l ⊔ l') where
    constructor _,_
    field
      ⟦_⟧ : U⊙ X → U⊙ Y
      psv : ⟦_⟧ (pt X) ≡ pt Y
  open _⊙→_ public
  -- (A , x) ⊙→ (B , y) = Σ (A → B) (λ f → f x ≡ y)
  
  ⊙id : (X : Ptd {l}) → X ⊙→ X
  (⊙id X) = (λ x → x) , refl 

  
  infix 2 _⊙∘_
  _⊙∘_ : {X Y Z : Ptd {l}} → Y ⊙→ Z → X ⊙→ Y → X ⊙→ Z
  (g , q) ⊙∘ (f , p) = (g ∘ f , (cong g p) ∙ q)
  record SubPtd (X : Ptd {l}) : Set (suc l) where
    constructor _,_
    field
      ⟨_⟩ :  U⊙ X → Proposition {l}
      pt∈ : asType (⟨_⟩ (pt X))
    T⟨_⟩ : U⊙ X → Type l
    T⟨ x ⟩ = asType ⟨ x ⟩ 
  open SubPtd public
  _∈∈_ : {X : Ptd {l}} {B : U⊙ X → Type l} → Σ (U⊙ X) B → (f  : SubPtd X) → Proposition
  x ∈∈ f = ⟨ f ⟩ (proj₁ x)
  infix 1 _~_
  _~_ : {X Y : Ptd {l}} → (f g : X ⊙→ Y) → Type l
  f ~ g = ∀ x → ⟦ f ⟧ x ≡ ⟦ g ⟧ x
--  syntax base S = ⟨ S ⟩

 




  【_】 : {Y : Ptd {l}} → (X : SubPtd Y) → Set l
  【_】{Y = Y} X = Σ (U⊙ Y) (λ y → asType (⟨ X ⟩ y))
  ext : {Y : Ptd {l}} → (X : SubPtd Y) → Sets l
  ext {Y = Y} X = 【 X 】  , eltsIsSet (U⊙' Y) λ x → Prop→Set (⟨ X ⟩ x )

   
  ⟪_⟫ : {Y : Ptd {l}} → (X : SubPtd Y) → Ptd {l}
  ⟪_⟫ {Y = Y} X = ptd (ext X)  (pt Y , pt∈ X) 
  record _⊂_ {X : Ptd {l}} (A B : SubPtd X) : Set l where
    constructor ⊂:
    field      
      _&_ : ( x : 【 A 】) → asType ( x ∈∈  B ) -- (fst x ∈ B)
  open _⊂_ public

  _⊂'_ : {X : Ptd} (A B : SubPtd X) → Set
  A ⊂' B = 【 A 】 → 【 B 】 -- Σ[ i ∈( 【 A 】 → 
  _≳_ : {X : Ptd} {A B : SubPtd X} → A ⊂ B → A ⊂' B
  f ≳ x = (proj₁ x , f & x)
  refl⊂ : {X : Ptd {l}} → (A : SubPtd X) → A ⊂ A
  refl⊂  A = ⊂: proj₂
  trans⊂ : {X : Ptd {l}} {A B C : SubPtd X} → A ⊂ B → B ⊂ C → A ⊂  C
  trans⊂ p q = ⊂: (λ x → q & ((proj₁ x) , p & x))

  0Sub : {X : Ptd {l}} → SubPtd X
  0Sub {X = X} = (λ a →  (a ≡% U⊙' X % pt X)  ) , refl  -- , (proj₂ (U⊙' X) _ _)

  full : {X : Ptd {l} } → SubPtd X
  full = (λ a → Propo 𝟏 (foo)) , * where
    foo : (x : 𝟏) → (y : 𝟏) → x ≡ y
    foo * * = refl
  ⊂full : {X : Ptd {l}} {A : SubPtd X} → A ⊂ full
  ⊂full  = ⊂: (λ x → *)

  _≈_ : {A : Ptd {ℓ}} {B : Ptd {ℓ'}} → (f g : A ⊙→ B) → Set (ℓ ⊔ ℓ')
  f ≈ g = (x : _) → ⟦ f ⟧ x ≡ ⟦ g ⟧ x  


  P𝟏 : Ptd
  P𝟏 = ptd (𝟏 , foo) * where
    foo : isSet {lzero} 𝟏
    foo * * p q i j = 1isProp (p j) (q j) i where
      1isProp : (x : 𝟏) → (y : 𝟏) → x ≡ y
      1isProp * * = refl
  c1 : {X : Ptd {ℓ}} → X ⊙→ P𝟏
  c1 = (λ _ → *) , refl
  1c : {X : Ptd {ℓ}} → P𝟏 ⊙→ X
  1c {X = X} = (λ _ → (pt X)) , refl

   

  
  _↔_ : {𝕏 : Ptd {lzero}} (A B : SubPtd 𝕏) → Set
  _↔_  A B  = A ⊂ B × B ⊂ A --  (x : U⊙ 𝕏) → (x ∈ A) ↔ (x ∈ B )
  ↔to≡ :   {𝕏 : Ptd {lzero}} {A B : SubPtd (𝕏)} → A ↔ B → A ≡ B
  ↔to≡  {𝕏 = 𝕏} {A = A} {B = B} (f , g) i  = (λ x → hello x i) , isProp→PathP (λ i → isP (hello (pt (𝕏)) i)) (pt∈ A) (pt∈ B) i where
    hello : (x : U⊙ 𝕏) → ⟨ A ⟩ x ≡ ⟨ B ⟩ x
    hello x = logicalEquivalentsAreEqual (λ y → f & (x , y) ) (λ y → g & (x , y))
  
