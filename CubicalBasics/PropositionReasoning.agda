{-# OPTIONS --cubical --safe --without-K #-}
module CubicalBasics.PropositionReasoning where
open import CubicalBasics.cubical-prelude hiding (_∧_)
-- open import Data.Product
-- open import Cubical.Foundations.Prelude -- using (id ; ∘)
open import Agda.Primitive using (Level ; Setω)
open import CubicalBasics.IsomorphismCubical

record Proposition {ℓ} : Type (lsuc ℓ) where
  constructor Propo
  field
    asType : Type ℓ
    isP : isProp asType

open Proposition public



data ∥_∥₋₁ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣₋₁ : A → ∥ A ∥₋₁
  squash₁ : (x y : ∥ A ∥₋₁) → x ≡ y

∥_∥ : {ℓ : Level} (A : Type ℓ) → Proposition {ℓ}
∥ A ∥ = Propo ∥ A ∥₋₁ squash₁
forallP : {A : Type ℓ} → (A → Proposition {ℓ'}) → Proposition {ℓ ⊔ ℓ'}
forallP {A = A} B = Propo ((a : A) → asType (B a)) λ x y i a → isP (B a) (x a) (y a) i
existP : {A : Type ℓ} → (A → Proposition {ℓ'}) → Proposition {ℓ ⊔ ℓ'}
existP {A = A} B = ∥ Σ[ a ∈ A ] (asType (B a)) ∥
_∧_ : Proposition {ℓ} → Proposition {ℓ'} → Proposition {ℓ ⊔ ℓ'}
A ∧ B = Propo (asType A × asType B) (λ (a , b) (a' , b') i → isP A a a' i , isP B b b' i)
data IMP (A : Type ℓ) (Q : Proposition {ℓ'}) : Type (ℓ ⊔ ℓ') where 
-- syntax ((a : A) → asType (Q a)) = A ⇒ Q
 intro : (A → asType Q) → IMP A Q
IMP' : (A : Type ℓ) → (Q : A → Proposition {ℓ'}) → Type (ℓ ⊔ ℓ') 
IMP' A Q = ((a : A) → asType (Q a))
syntax IMP' A (λ a → Q) = [ a ∶ A ]⇒ Q
syntax IMP A Q = A ≡> Q
private
  _⇒_ : (A : Type ℓ) (Q : Proposition {ℓ'}) → Type (ℓ ⊔ ℓ')
  A ⇒ Q = [ x ∶ A ]⇒ Q

outro : {A : Type ℓ} {Q : Proposition {ℓ'}} → IMP A Q → (A → asType Q)
outro (intro g) = g

truncInd : {A : Type ℓ'} {Q : Proposition {ℓ}} → ∥ A ∥₋₁ → (A ≡> Q)  → asType Q
truncInd ∣ x ∣₋₁ g = (outro g) x
truncInd {Q = Q} (squash₁ z z₁ i) g  =  (isP Q) (truncInd z g) (truncInd z₁ g) i
truncIndSyntax : {A : Type ℓ'} → (Q : Proposition {ℓ}) → ∥ A ∥₋₁ → (A → asType Q)  → asType Q
truncIndSyntax Q x g = truncInd {Q = Q} x (intro g)
syntax truncIndSyntax Q x (λ y → g) = take y ← x , g to prove Q
-- syntax  = take x ∶ A such that B to show C
introSyntax : (A : Type ℓ) {Q : Proposition {ℓ}} → (A ⇒ Q)  → A ≡> Q
introSyntax A f = intro f
syntax introSyntax A (λ x → f) = take x ∶ A for f


infixl 25 _then_
_then_ : {A B : Type ℓ} {Q : Proposition {ℓ}} →  (A → B) → B ≡> Q → A ≡> Q
f then (intro bq) = intro λ x → bq (f x)

thenSyntax : {A B : Type ℓ}  {Q : Proposition {ℓ}} → ∥ A ∥₋₁ → (A → B) → (B ≡> Q)  → asType Q --{C : A → Type}
thenSyntax x f g = truncInd x (f then g)

-- syntax truncSyntax x (λ x' → f) g = x' ∶ x >> f ° g
syntax thenSyntax x (λ x' → f) g = take x' ∶ x to use f for g


isProp→isSet : ∀ {o} → {A : Type o} → isProp A → isSet A
isProp→isSet h a b p q j i =
    hcomp (λ k → λ { (i = i0) → h a a k
                   ; (i = i1) → h a b k
                   ; (j = i0) → h a (p i) k
                   ; (j = i1) → h a (q i) k }) a
Prop→Set : {l : Level} → Proposition {l} → Sets l
Prop→Set (Propo A isP) = A , isProp→isSet isP
isPropisProp : ∀ {ℓ'} {A : Type  ℓ' } → isProp (isProp A)
isPropisProp {A = A} x y i a b = isProp→isSet x _ _ (x a b) (y a b) i  -- isProp→PathP (λ j → {!x (x a b j) (y a b j)!}) {!!} {!!} i

Set≡  : (S : Sets ℓ) (x y : proj₁ S) → Proposition
Set≡ S x y = Propo (x ≡ y) (proj₂ S x y)
syntax Set≡ S x y = x ≡% S % y

private variable
 o l e : Level
 
record Monad : Setω where
  field
    M : {o : Level} → Type o → Type o
    fmap : {o l : Level} → ∀ {A : Type o} {B : Type l} → (A → B) → M A → M B
    η : {o : Level} → ∀ {A} → A → M A
    μ : {o : Level} → ∀ {A : Type o} → M (M A) → M A
  --  ident : ∀ {A} → (μ ∘ fmap (η {A = A} )) ∼ id
  --  assoc : ∀ {A} → (μ ∘ fmap (μ {M A})) ∼ (fmap μ ∘ μ)

  bind : ∀ {o} {l} → {a : Type o} {b : Type l} → M a → (a → M b) → M b
  bind x f = μ ( fmap f x )
  return : {o : Level} → {a : Type o} → a → M a 
  return {o} = η {o}
  syntax bind x (λ y → f) = y ← x , f
truncMonad : Monad 
truncMonad = record { M = ∥_∥₋₁ ; fmap = λ f a' → take a ← a' , ∣ f a ∣₋₁ to prove ∥ _ ∥ ; η = ∣_∣₋₁ ; μ = λ x → truncIndSyntax ∥ _ ∥ x id } -- ; ident = λ x i → {!!} ; assoc = {!!} }

fmap' : {o l : Level} → ∀ {A : Type o} (B : Proposition {l}) → ((a : A) → ∥ asType B ∥₋₁) → ∥ A ∥₋₁ → asType B
fmap' B p ma =  take a ← ma , take b ← p a , b to prove B to prove B
fmap'' : {o l : Level} → ∀ {A : Type o} (B : Proposition {l}) → ((a : A) → asType B) → ∥ A ∥₋₁ → asType B
fmap'' B p ma = take a ← ma , p a to prove B
syntax fmap'' B (λ a → p) = take a , p to prove B
syntax fmap' B (λ a → p) = take a , desquash p to prove B
-- chopOf : {Q : Proposition {ℓ}} → ∥ asType Q ∥₋₁ → asType Q
-- chopOf {Q = Q} = take ax , ax to prove Q
isSetIsProp : ∀ {ℓ'} {A : Type  ℓ' } → isProp (isSet A)
isSetIsProp {A = A} p q i x y = isPropisProp (p x y) (q x y) i
logicalEquivalentsAreEqual : {A B : Proposition {ℓ}} → (asType A → asType B) → (asType B → asType A) → A ≡ B
logicalEquivalentsAreEqual {ℓ = ℓ} {A = Propo  A Ap} {B = Propo B  Bp} f g i = Propo (ua  A≃B i) ((isProp→PathP (λ j → isPropisProp {A = ua A≃B j}) Ap Bp i)) where
 A≃B : A ≃ B
 A≃B = f , isoToIsEquiv (iso f g (λ b → Bp _ _) λ _ → Ap _ _)
