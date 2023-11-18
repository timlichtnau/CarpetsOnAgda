{-# OPTIONS --cubical --without-K #-}
open import CarpetCubical3
open import CubicalBasics.PointedTypesCubical
open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
open import Data.Product
open import Agda.Builtin.Unit
open import CubicalBasics.PropositionReasoning
open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)

open import Function.Base using (_∘_)
open import Relation.Binary.Definitions 
open import Relation.Binary.Structures using (IsPartialOrder ; IsPreorder)
open import Equalizer3
open import SemiLattices
open import CubicalBasics.cubical-prelude hiding (_∨_ ; _∧_)
open import CubicalBasics.cubicalEqualityReasoning
open import HomoAlgStd
open import CubicalBasics.PropositionReasoning
import Relation.Binary.Reasoning.Base.Single

module HomoAlgOnCarpets {o e} (carpet : Carpet {o} {ℓ} {e} ) where
open CarpetHelper carpet
open Monad truncMonad
private variable
  l k j : Carrier
{--
_↔_ : {j : Carrier} → (A B : SubPtd (𝕏 j)) → Set
_↔_  A B  = A ⊂ B × B ⊂ A --  (x : U⊙ 𝕏) → (x ∈ A) ↔ (x ∈ B )
↔to≡ : {j : Carrier} → (A B : SubPtd (𝕏 j)) → A ↔ B → A ≡ B
↔to≡ {j = j} A B (f , g) i  = (λ x → hello x i) , isProp→PathP (λ i → isP (hello (pt (𝕏 j)) i)) (pt∈ A) (pt∈ B) i where
  hello : (x : X j) → ⟨ A ⟩ x ≡ ⟨ B ⟩ x
  hello x = logicalEquivalentsAreEqual (λ y → f & (x , y) ) (λ y → g & (x , y))
--}  
record SubEl : Type (suc zero ⊔ o) where
  constructor _,_
  field
    daIn : Carrier 
    sub : (SubPtd (𝕏 daIn))
open SubEl public


Im : (p : k ≤ j) → SubEl
Im {j = j} p = j , im (ϕ p)
Ker : (p : k ≤ j) → SubEl
Ker {k = k} p = k , ker (ϕ p)
Full : Carrier → SubEl
Full j = (j , full)
Mono : j ≤ k → Set
Mono p = mono (ϕ p)

Epi : j ≤ k → Set
Epi p = surj (ϕ p)
𝟎 : Carrier → SubEl
𝟎 j = (j , 0Sub )
record _⊆_ (A B : SubEl) : Type e where
  constructor _,_
  field
    myEdge : daIn A ≤ daIn B
    myArg : (x : 【 sub A 】) → asType (⟨ sub B ⟩ (⟦ ϕ myEdge ⟧ (proj₁ x)))
ker_⊂0 : (p : k ≤ j) → Ker p ⊆ 𝟎 j
ker p ⊂0 = p , λ x → proj₂ x
0⊂Sth : {A : SubPtd (𝕏 j)} → 0Sub ⊂ A
0⊂Sth  {A = A} = ⊂:  λ x →  subst T⟨ A ⟩ (sym (proj₂ x)) (pt∈ A)

Sth⊂Full : {j : Carrier} → {A : SubPtd (𝕏 j)} → A ⊂ full
Sth⊂Full =  ⊂: λ x → *

Mono' : {p : j ≤ k} → Mono p → ker (ϕ p) ↔ 0Sub
Mono' m = m , 0⊂Sth
Epi' : {p : j ≤ k} → Epi p → im (ϕ p) ↔ full
Epi' s = Sth⊂Full , s


imf⊆imgf : (ed : j ≤ k) (ed' : k ≤ l) → Im ed ⊆ Im (ed ■ ed')
imf⊆imgf ed ed' = ed' , λ x → y ← proj₂ x , return (proj₁ y , sym (transit' ed ed' (proj₁ (proj₁ y))) ∙ cong (⟦ ϕ ed' ⟧) (proj₂ y))
kerf⊂kergf :  {ed : j ≤ k} (ed' : k ≤ l)  (ed'' : j ≤ l)  → ker (ϕ ed) ⊂ ker (ϕ (ed''))
kerf⊂kergf  {ed = ed} ed' ed'' = (⊂: (λ x →
       ⟦ ϕ ed'' ⟧ (proj₁ x)
       ≡⟨ doesntMatter  _ ⟩
       ⟦ ϕ (ed ■ ed') ⟧ (proj₁ x)
       ≡⟨ sym ((transit' _ _) _) ⟩
       ⟦ ϕ ed' ⟧ (⟦ ϕ ed ⟧ (proj₁ x))
       ≡⟨ cong (⟦ ϕ ed' ⟧) (proj₂ x) ⟩
       ⟦ ϕ ed' ⟧ (pts _)
       ≡⟨ psv (ϕ ed') ⟩
       pt (𝕏 _) ∎ )) where open Reasoning
outro⊂ : {A B : SubPtd (𝕏 j)} → (j , A) ⊆ (j , B) → A ⊂ B
outro⊂ {B = B} (p , q) = ⊂: (λ x → subst T⟨ B ⟩ (doesntMatter _ ∙ reflex _) (q x))      
F : SubEl → SubEl
F A = Full (daIn A)
isZeroObj : Carrier → Set e
isZeroObj j = Full j ⊆ 𝟎 j
