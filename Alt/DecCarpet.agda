{-# OPTIONS --cubical #-}
open import PointedTypesCubical
open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
open import Data.Product

open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)
open import Relation.Binary.Core
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures using (IsPartialOrder)

open import cubical-prelude hiding (_∨_)
open Ptd
open _⊙→_
variable
  o l e : Level
record SemiLattice (o l e : Level) : Type (suc o ⊔ suc e ⊔ suc l) where
  field
    Carrier : Set o
    CarIsSet : isSet (Carrier)
    _≤_ : Carrier → Carrier → Type e
    ≤isProp : {x y : Carrier} → isProp (x ≤ y)
    reflexivity : {i : Carrier} → i ≤ i
    _■_ : {i j k : Carrier} → i ≤ j → j ≤ k → i ≤ k
    _∨_ : Carrier → Carrier → Carrier
    comm : ∀ {i} {j} → i ∨ j  ≡ j ∨ i
    upperBound : ∀ i j → i ≤ (i ∨ j) 
    sup : ∀ {i} {j} {k} → i ≤ k → j ≤ k → (i ∨ j) ≤ k
module _ (J : SemiLattice o l e) where
  open SemiLattice J
  PathTo≤ : {x y : SemiLattice.Carrier J} → x ≡ y → SemiLattice._≤_ J x y
  PathTo≤ {x = x} {y = y} p = (subst (λ a → SemiLattice._≤_ J x a ) p (SemiLattice.reflexivity J))
  upperBound' :  ∀ i j → j ≤ (i ∨ j)
  upperBound' k j' = upperBound j' k ■ PathTo≤ comm

record Carpet {o l e : Level} : Set (suc l ⊔ suc e ⊔ suc o) where
  constructor _,_
  field
    -- record {Carrier = I ; _≈_ =  _≈_ ; _≤_ = _≤_ ; isPartialOrder = isPartialOrder }  : Poset o l e
    J : SemiLattice o l e
  open SemiLattice J
  field
    X : Carrier → Ptd
    ϕ : {i j : Carrier } → i ≤ j → X i ⊙→ X j
    reflex : {i : Carrier } → ϕ (reflexivity) ~ ⊙id (X i)
    transit : {i j k : Carrier } → (p : (_≤_ i j)) → (q : (_≤_ j k)) → (r : (_≤_ i k)) → ϕ q ⊙∘ ϕ p ~ ϕ r

module _ (C : Carpet {o} {l} {e}) where
  Lat = Carpet.J C
  open Carpet C 
  open SemiLattice Lat

  transit' : {i j k : Carrier} → (p : i ≤ j) → (q : j ≤ k) → ϕ q ⊙∘ ϕ p ~ ϕ (p ■ q)
  transit' p q = transit p q (p ■ q)

  Elts : Set o
  Elts = Σ (Carrier) (U⊙ ∘ X)
  _<_ : Elts → Carrier → Set e
  (i , x) < j = i ≤ j
  ElUnder : Carrier → Set (o ⊔ e)
  ElUnder j = Σ Elts (λ e → e < j)
  ≡ElUnder : {j : Carrier} → (x y : ElUnder j ) → proj₁ x ≡ proj₁ y → x ≡ y
  ≡ElUnder  x y p i = (p i) ,
    isProp→PathP {A = λ k → (proj₁ (p k)) ≤ _} (λ k → ≤isProp) (proj₂ x) (proj₂ y) i 
  infixl 5 _§_
  _§_ : ∀ {j} e → e < j → Elts
  _§_ {j} (i , x)  p = j ,  ⟦ ϕ p ⟧ x
  _§refl=id : ∀ e → e § reflexivity ≡ e
  e §refl=id = λ i → (proj₁ e) , (reflex (proj₂ e) i)
  ac' : {j : Carrier} → ElUnder j → Elts
  ac' (e , p) = e § p
  actrans : ∀ {j k e} → (p : e < j) → (q : j ≤ k) → (e § p) § q ≡ (e § (p ■ q))
  actrans {e = e} p q i = _ , transit' p q (snd e) i
  _∣  : ∀ {j} {e e'} {p : e < j} {p' : e' < j} → (pf : e ≡ e') → e § p ≡ e' § p'
  _∣ {e = e} {e' = e'} {p} {p'} pf = cong ac' (≡ElUnder (e , p) (e' , p') pf)
  commSq : ∀ {j j'  k} e →
    (p : e < j) →
    (q : j ≤ k) → (p' : e < j') → (q' : j' ≤ k) → e § p § q ≡ e § p' § q'
  commSq {k = k} e p q p' q' =
    e § p § q
      ≡⟨ actrans p q ⟩
    e § (p ■ q)
      ≡⟨  (λ i → _§_ {j = k} e (≤isProp (p ■ q) (p' ■ q') i ) )  ⟩
    e § (p' ■ q')
      ≡˘⟨ actrans p' q' ⟩
    e § p' § q' ∎
  


  record _≡[_]_ (ix : Elts) (k : Carrier) ( jy : Elts) : Set (o ⊔ e) where
    field
      left : fst ix ≤ k
      right : fst jy ≤ k
      eq : ix  § left ≡  jy § right
  open _≡[_]_
  fwd : {j' k : Carrier} →
    (ix : Elts) →
    ((jy , p) : ElUnder j') →
    ix ≡[ k ] jy →
    ix ≡[ k ∨ j' ] (jy § p) --(p $ ix)
    
  fwd {j'} {k} ix (jy , p) z = record {
    left = (left z) ■ (upperBound k j') ;
    right = (upperBound j' k) ■  (PathTo≤ J comm) ;
    eq =    ix § (left z ■ upperBound k j')
              ≡˘⟨ actrans (left z) (upperBound k j') ⟩
            ix § left z § (upperBound k j')
              ≡⟨  eq z ∣  ⟩ 
            jy § right z § upperBound k j'
              ≡⟨ (commSq jy (right z) (upperBound k j') p (upperBound' J _ _)) ⟩
            jy § p § upperBound j' k ■ PathTo≤ J comm ∎ 


    }
  sym : {l : Carrier} → {x y : Elts} → x ≡[ l ] y → y ≡[ l ] x
  sym p = record { left = right p ; right = left p ; eq = λ i → (eq p) (~ i) }
  deeper : {l k : Carrier} {x y : Elts} → l ≤ k →  x ≡[ l ] y → x ≡[ k ] y
  deeper p r = record { left = left r ■ p ; right = right r ■ p ; eq =
     _ § (left r ■ p)
     ≡˘⟨ actrans (left r) p ⟩
    _ § left r § p
      ≡⟨ eq r ∣ ⟩
    _ § right r § p
      ≡⟨ actrans (right r) p ⟩
    _ § (right r ■ p)
      ∎   
    }
  trans≡ : {l k : Carrier} →  {x y z : Elts} →  x ≡[ k ] y → y ≡[ l ] z → x ≡[ l ∨ k ] z
  trans≡ {x = x} {y = y} {z = z} p q = record {
    left = left p ■ upperBound' J _ _ ;
    right = right q ■ upperBound  _ _ ;
    eq =
      x § (left p ■ upperBound' J _ _)
        ≡˘⟨ actrans (left p) (upperBound' J _ _ ) ⟩
      x § left p § upperBound' J _ _
        ≡⟨ eq p ∣  ⟩
      y § right p § upperBound' J _ _
        ≡⟨  commSq y (right p) (upperBound' J _ _) (left q) (upperBound (proj₁ (y § left q)) _)  ⟩
      y § left q § upperBound _ _ 
        ≡⟨ eq q ∣  ⟩
      z § right q § upperBound _ _
        ≡⟨ actrans (right q) (upperBound _ _) ⟩ 
      z § (right q ■ upperBound _ _) ∎ }
  bwd : {l : Carrier} →  {x y z : Elts} → x ≡[ proj₁ y ] y → y ≡[ l ] z → x ≡[ l ] z
  bwd {l = l} p q = deeper (sup reflexivity (left q)) (trans≡ p q)
