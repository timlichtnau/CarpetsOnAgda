{-# OPTIONS --cubical --without-K #-}
open import CarpetCubical3
open import CubicalBasics.PointedTypesCubical
-- open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
--open import Data.Product
open import Agda.Builtin.Unit
open import CubicalBasics.PropositionReasoning
--open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)

-- open import Function.Base using (_∘_)
open import Cubical.Relation.Binary.Order.Preorder using (IsPreorder)
-- open import Relation.Binary.Structures using (IsPartialOrder ; IsPreorder)
open import Equalizer3
open import SemiLattices
open import CubicalBasics.cubical-prelude hiding (_∨_ ; _∧_)
open import CubicalBasics.cubicalEqualityReasoning
open import HomoAlgStd

-- import Relation.Binary.Reasoning.Base.Single
import HomoAlgOnCarpets
open import Cubical.Relation.Binary.Base -- using (BinaryRelation.isTrans)
--open import Cubical.Relation.Binary.Base renaming (_⇒_ to _==>_)
--open import DoublePreorderReasoning
open import FibreArgumentation

module NaiveImplication {o e} (carpet : Carpet {o} {ℓ} {e} ) where
open CarpetHelper carpet
open HomoAlgOnCarpets carpet
open Monad truncMonad
private variable
  j k l : Carrier
_~_~_~>_ : (A : SubEl) → (x : 【 sub A 】) → Carrier → SubEl → Type (o ⊔ e)
A ~ x ~ uncert ~> B = ∥ (Σ[ y ∈ 【 sub B 】 ] ((daIn A , proj₁ x) ≡[ uncert ] (daIn B , proj₁ y) )) ∥₋₁
--- A ~~ l ~> B  TELLS YOU, that the map A ×ₗ B → A is surjective.
record _~~_~>_ (A : SubEl) (uncert : Carrier) (B : SubEl) : Type (o ⊔ e) where
  constructor AR
  field
   me : (x : 【 sub A 】) →  A ~ x ~ uncert ~> B
record _=>_ (A B : SubEl) : Type (o ⊔ e) where
  constructor _,_
  field
    uncert : Carrier
    provider' : A ~~ uncert ~> B
  provider : (x : 【 sub A 】) →  A ~ x ~ uncert ~> B
  open _~~_~>_
  provider = me provider'
  atLeast : daIn A ∨ daIn B ≤ uncert
  atLeast = (take (a , b) ← (provider (pt ⟪ sub A ⟫ )) , sup (left b) (right b) to prove Propo _ ≤isProp )
  left' : daIn A ≤ uncert
  left' = uB ■ atLeast
  right' : daIn B ≤ uncert
  right' = uB' ■ atLeast
open _=>_ public
postulate =>isProp : ∀ x y → isProp (x => y) 
refl=> : {A : SubEl} → A => A
refl=> {A = (i , A)} = i ,   AR (λ x →  ∣ x , refl≡  ∣₋₁)
trans=> : {A B C : SubEl} → A => B → B => C → A => C --  BinaryRelation.isTrans _=>_ -- 
trans=> (l , AR p) ( l' , AR q)= (l ∨ l') ,   AR λ x → --(resp (uB ■ h) (uB' ■ h') 
  (y , α) ← p x ,
  (z , β) ← q y ,
  return (z , trans≡ α β)  
IncUncert : {A B : SubEl} → ((j , p) : A => B) → j ≤ k  → A => B
IncUncert {k = k}  (j , AR p) q = k , AR λ x → z ← p x , return ((proj₁ z , deeper  q (proj₂ z)))

-- _⊂'_ : {A B : SubPtd} 
-- substAlongReflex : {B : SubPtd (𝕏 j)}  → 【 B 】 → 

=>To⊂ : {A B : SubEl} → (p : A => B) → uncert p ≤ daIn B → A ⊆ B
=>To⊂ {A = A} {B = B} p q = ((left' p) ■ q) , λ x →
  take
    (b , c) ← provider p x ,
    subst T⟨ sub B ⟩ (sym (foo x b c)) (proj₂ b )
  to prove (⟨ sub B ⟩ (⟦ ϕ ((left' p) ■ q) ⟧ (proj₁ x)))  where
  foo : (x : 【 sub A 】)  →
    (y :  【 sub B 】) →
    (daIn A , proj₁ x) ≡[ uncert p ] (daIn B , proj₁ y)
    →  ⟦ ϕ ((left' p) ■ q) ⟧ (proj₁ x) ≡ proj₁ (y)
  foo x y pf = isEmb helper where
    helper : (daIn B , ⟦ ϕ (left' p ■ q) ⟧ (proj₁ x)) ≡ (daIn B , proj₁ y)
    helper =
         
      (daIn A , proj₁ x) § (left' p ■ q)
        ≡˘⟨ actrans _ _ ⟩
      (daIn A , proj₁ x) § left' p § q
        ≡⟨ eq' pf ∣ ⟩
      (uncert p , snd ((daIn B , proj₁ y) § right' p)) § q
        ≡⟨ actrans _ _ ⟩
      (daIn B , proj₁ y) § (right' p ■ q)
        ≡⟨ refl ∣ ⟩
      (daIn B , proj₁ y) § reflexivity
        ≡⟨ §refl=id ⟩ 
      (daIn B , proj₁ y) ∎  where open Reasoning

=>Rel : Cubical.Relation.Binary.Order.Preorder.IsPreorder  _=>_ -- (o ⊔ e)
=>Rel =  Cubical.Relation.Binary.Order.Preorder.ispreorder SubEl_isSet (λ x y → =>isProp x y) (λ x → refl=>) (λ _ _ _ → trans=>) -- _=>_ , ( refl=> , trans=>  )
imp : ∀ {x y} →  (x ⊆ y) →  (x => y)
imp  {x = A} {y = B} (p , α) = (daIn B) , AR λ x →
  return ((⟦ ϕ p ⟧ (proj₁ x) , α x) , fwdEasy p)
trans≤=> : ∀ {x y z} → (x ⊆ y) → y => z → x => z
trans≤=> = (λ x≤y y~z → IncUncert (trans=> (imp x≤y) y~z) (sup (left' y~z) reflexivity))
