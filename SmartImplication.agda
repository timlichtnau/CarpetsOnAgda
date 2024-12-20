{-# OPTIONS --cubical -WnoUnsupportedIndexedMatch #-}
open import CarpetCubical3
open import CubicalBasics.PointedTypesCubical
-- open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
-- open import Data.Product
open import Agda.Builtin.Unit
open import CubicalBasics.PropositionReasoning
-- open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)

-- open import Function.Base using (_∘_)
-- open import Relation.Binary.Definitions 
--open import Relation.Binary.Structures using (IsPartialOrder ; IsPreorder)
open import Equalizer3
open import SemiLattices
open import CubicalBasics.cubical-prelude hiding (_∨_ ; _∧_)
open import CubicalBasics.cubicalEqualityReasoning
open import HomoAlgStd

-- import Relation.Binary.Reasoning.Base.Single
import HomoAlgOnCarpets

-- open import Relation.Binary renaming (_⇒_ to _==>_)
-- open import DoublePreorderReasoning
open import FibreArgumentation
import NaiveImplication
module SmartImplication {o e}(carpet : Carpet {o} {ℓ} {e} ) where
open HomoAlgOnCarpets carpet
open CarpetHelper carpet 

open NaiveImplication carpet 
private variable
  j k l : Carrier
infixr 21 _↓*_
_↓*_ : {i j : Carrier} → i ≤ j → (A : SubPtd (𝕏 i))  → SubPtd (𝕏 j)
p ↓* A = pushforward (ϕ p) A
infixr 21 _↑*_
_↑*_ : {i j : Carrier} → i ≤ j → (A : SubPtd (𝕏 j))  → SubPtd (𝕏 i)
p ↑* A = pullback (ϕ p) A

open Monad (truncMonad)
leftFunc : {i j k : Carrier} {A : SubPtd (𝕏 i)} → (f : i ≤ j) → (g : j ≤ k) →  g ↓* f ↓* A ≡(f ■ g) ↓* A
leftFunc {A = A} f g = ↔to≡ ((⊂: λ x →
  y ← proj₂ x ,
  z ← proj₂ (proj₁ y) ,
  return ((proj₁ z) , (sym (transit' f g (proj₁ (proj₁ z))) ∙ cong ⟦ ϕ g ⟧ (proj₂ z) ∙ proj₂ y))) , ⊂: λ x → y ← proj₂ x , return ((pushIntoPshFWD  (ϕ f) {A =  A } (proj₁ y)) , (transit' f g _ ∙ proj₂ y)))
--- A =>'[ l ]  B  TELLS YOU, that the map A ×ₗ B → A is surjective.
data _=>'[_]_ : SubEl → Carrier → SubEl → Type (suc lzero ⊔ o ⊔ e) where
  START : ∀ {A B } → (p : A ~~ daIn A ~> B)  → A =>'[ daIn A ] B
  END : ∀ {A B } → (p :  A ~~ daIn B ~> B)  → A =>'[ daIn B ] B
  EQUAL : ∀ {j} {A B : SubPtd (𝕏 j) } → (p : (j , A) ~~ j ~> (j , B)) → (j , A) =>'[ j ] (j , B)
  NOTHING : ∀ {A B } →  (p : A => B) → A =>'[ uncert p   ] B
  
_=>'_ : SubEl → SubEl → Type (suc lzero ⊔ o ⊔ e) 
A =>' B = Σ[ j ∈ Carrier ] (A =>'[ j ] B)
postulate =>'isPropValued : ∀ A B →  isProp (A =>' B)
back' : ∀ { A B } → A =>'[ j ] B → A ~~ j ~> B
back' {j = j} (START p ) = p
back' {j = j}  (END p ) =  p
back' {j = j} (NOTHING p ) = provider' p
back' {j = j} (EQUAL x ) = x
back :  ∀ { A B } → A =>' B → A => B
back (j , x) = j ,  back' x

UNC : ∀ {A B} → A =>' B → Carrier
UNC p =  proj₁ p -- uncert (back p)
infixl 2 %_
%_ : {A B : SubEl} → (p : A =>' B) → A =>'[ UNC p ] B
% p = proj₂ p
fstStart : {A B C : SubEl} →  (p : A => B) → uncert p ≤ daIn A → B =>' C → A =>' C

fstStart  p x (j , START p₁ ) =  _ , START (provider' (((IncUncert (trans=> p (j , p₁)))  (sup x (right' p ■ x)))))
fstStart p x (j , END p₁) = _ , NOTHING (trans=> p (j , p₁) )
fstStart  p x (j , NOTHING p₁) = _ , NOTHING (trans=> p p₁)
fstStart p x (j , EQUAL p₁) = _ , START (provider' (IncUncert (trans=> p (j , p₁)) ( sup x (right' p ■ x)))  )


  -- endStart : {A B C : SubEl} →  A =>' B → (p : B => C) → uncert p ≤ daIn B → A =>' C
  -- endStart
-- end : {j : Carrier} → (p :   
refl=>' : {A : SubEl} → A =>' A
refl=>' {A} = _ , EQUAL (provider' refl=> )
{-# TERMINATING #-}
trans=>' : {A B C : SubEl} → A =>' B → B =>' C → A =>' C
trans=>' (j , START p ) q = fstStart (j , p) re q
trans=>' (j , END p) (k , END q) = _ , END (provider' (IncUncert (trans=> (j , p) (k , q)) (left' (k , q) ∨R) ))  --(IncUncert (trans=> (j , p) (k , q)) (sup (left' (k , q )) reflexivity))
trans=>' (j , END p ) (k , START q ) = _ , NOTHING (IncUncert (trans=> (j , p) (k , q)) (sup (left' ( k ,  q )) reflexivity))
trans=>' (j , END p ) (k , EQUAL q ) = _ , END (provider' (IncUncert (trans=> (j , p) (k , q)) (left' (k , q) ∨R) ))  -- trans=>' (j , END p) (k , END q)
trans=>' (j , END p ) (k , NOTHING q ) = _ , NOTHING (IncUncert (trans=> (j , p) q) (sup (left' q) reflexivity))
trans=>' (j , EQUAL p) (k , q) = trans=>' (j , END p) ( k , q)

trans=>' (j , NOTHING x) (k , START p ) = _ , NOTHING (IncUncert (trans=> x (k , p)) (sup reflexivity (right' x)))
trans=>' (j , NOTHING x) (k , END p ) = _ , NOTHING (trans=> x (k , p))
trans=>' (j , NOTHING x) (k , NOTHING x₁) = _ , NOTHING (trans=> x x₁)
trans=>' (j , NOTHING x) (k , EQUAL p ) = _ , NOTHING (IncUncert (trans=> x (k , p)) (sup reflexivity (right' x)))

infixl 3 _∷_
_∷_ = trans=>'

UNCTrans : {A B C : SubEl} → (f : A =>' B) → (g : B =>' C) → UNC (f ∷ g) ≤ UNC f ∨ UNC g
UNCTrans (j , START p) (k , START p₁) = left' (j , p) ■ uB
UNCTrans (j , START p ) (k , END p₁ ) = reflexivity
UNCTrans (j , START p ) (k , EQUAL p₁ ) = left' (j , p) ■ uB
UNCTrans (j , START p ) (k , NOTHING x₁) = reflexivity
UNCTrans (j , END p) (k , START g) = uB'
UNCTrans (j , END p) (k , END g) = uB'
UNCTrans (j , END p) (k , EQUAL g) = uB'
UNCTrans (j , END p) (k , NOTHING g) = uB'
UNCTrans (j , EQUAL p) (k , START g) = uB'
UNCTrans (j , EQUAL p) (k , END g) = uB'
UNCTrans (j , EQUAL p) (k , EQUAL g) = uB'
UNCTrans (j , EQUAL p) (k , NOTHING g) = uB'
UNCTrans (j , NOTHING x) (k , START p) = uB
UNCTrans (j , NOTHING x) (k , END p) = reflexivity
UNCTrans (j , NOTHING x) (k , EQUAL p) = uB
UNCTrans (j , NOTHING x) (k , NOTHING x₁) = reflexivity

module _ {j : Carrier} where
  IncUncert'' : {A B : SubEl} → (f : A =>'[ j ] B) → j ≤ k → A =>'[ k ] B
  IncUncert'' (START f) p = NOTHING (IncUncert (j , f) p)
  IncUncert'' (END f) p = NOTHING (IncUncert (j , f) p)
  IncUncert'' (EQUAL f) p = NOTHING (IncUncert (j , f) p)
  IncUncert'' (NOTHING f) p = NOTHING (IncUncert f p)
IncUncert' : {A B : SubEl} → (f : A =>' B) → UNC f ≤ k → A =>' B
IncUncert' (j , f) p = _ , IncUncert'' f p 
FWD' :  {A : SubEl} → (p : daIn A ≤ j) → A  =>' (j , p ↓* (sub A))
FWD' {j = j} {A = A}  p = _ , END (provider' (imp erg)) where
  erg : A ⊆ (j , pushforward (ϕ p) (sub A))
  erg = (p , λ x → proj₂ (pushIntoPshFWD {𝔸 = 𝕏 (daIn A)} {𝔹 = 𝕏 j}  (ϕ p) {A = sub A} x))
BWD' :  {A : SubPtd (𝕏 k)} (p : k ≤ j) → (j , p ↓* A) =>' (k , A)
BWD' {A = A} p =  _ , START (AR λ (x , q) →
  (a , b) ← q ,
  return (a , symm (bwd (toEl≡ b) refl≡)))
PB : {A : SubPtd (𝕏 j)} (p : k ≤ j) → (A ⊂ im (ϕ p)) → (j , A) =>' (k , p ↑* A)
PB {A = A} p pf = _ , START (AR λ a →
  (x , b) ← pf & a ,
  return ((proj₁ x , subst (T⟨ A ⟩) (sym b) (proj₂ a )) , symm (bwd refl (refl≡' (sym b)))))
BWD : (p : k ≤ j) → Im p =>' Full k
BWD = BWD' {A = sub (Full _)}

intro⊆ : {A B : SubEl } → A ⊆ B → A =>' B -- [ daIn B ] B
intro⊆ {A = A} {B = B} (ed , p) = _ ,  END (provider' (imp (ed , (λ x →  subst (T⟨ sub B ⟩ )  (refl) (p x)))))
-- I WOULD REALLY LIKE TO DO STH LIKE syntax sub A ⊂ sub B = A ⊂' B
intro⊂ : {A B : SubPtd (𝕏 j) } → A ⊂ B → (j , A) =>' (j , B)
intro⊂ {B = B} (⊂: p) = _ ,  EQUAL ((provider' (imp (reflexivity , (λ x →  subst (T⟨ B ⟩ )  (sym (reflex _)) ((p x))))))) 



0=>'Sth : {A : SubEl} → 𝟎 (daIn A) =>' A
0=>'Sth = intro⊂ 0⊂Sth -- (0⊂Sth {A = ?})
0toF0 : (p : k ≤ j) → 𝟎 k =>' 𝟎 j
0toF0 {j = j} p = 0=>'Sth ∷ intro⊆ (ker p ⊂0) -- intro⊆ (p , λ x → subst T⟨ sub (𝟎 j) ⟩ (sym (psv (ϕ p)) ∙ (cong (⟦ ϕ p ⟧) (sym (proj₂ x)))) refl)

Sth=>'Full : {j : Carrier} → {A : SubPtd (𝕏 j)} → (j , A) =>' Full j
Sth=>'Full =  intro⊂ (Sth⊂Full)
FWD : {A : SubEl} → (p : daIn A ≤ j) → A  =>' Im p
FWD p = Sth=>'Full ∷ FWD' p

_==>_ : {j : Carrier} (A B : SubEl) → Set (suc lzero ⊔ o ⊔ e)
_==>_ {j = j} A B =  A =>'[ j ] B

to⊂' : {A B : SubPtd (𝕏 j)} → (p : (j , A) =>'[ j ] (j , B)) → A ⊂ B
to⊂' p = outro⊂ (=>To⊂ (back (_ , p)) re)

to⊂ : {A B : SubPtd (𝕏 j)} → (p : (j , A) =>'[ k ] (j , B)) → k ≤ j  → A ⊂ B
to⊂ p q = to⊂' (IncUncert'' p q)

_=>[_]_ : SubEl → Carrier → SubEl → Set (ℓ-max (ℓ-max (ℓ-suc ℓ-zero) o) e)
A =>[ l ] B = Σ[ ρ ∈ A =>' B ] UNC ρ ≤ l





