{-# OPTIONS --cubical #-}
open import PointedTypesCubical
open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
open import Data.Product

open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)
-- open import Relation.Binary.Core
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures using (IsPartialOrder)
open import Equalizer
open import SemiLattices
open import cubical-prelude hiding (_∨_)
open import HomoAlgStd
record Carpet {o l e : Level} : Set (suc l ⊔ suc e ⊔ suc o) where
  constructor _,_
  field
    -- record {Carrier = I ; _≈_ =  _≈_ ; _≤_ = _≤_ ; isPartialOrder = isPartialOrder }  : Poset o l e
    J : SemiLattice o l e
  open SemiLattice J

  field
    X' : Carrier → Σ Ptd (λ X → isSet (U⊙ X))
  X : Carrier → Ptd
  X i = proj₁ (X' i)
  field
    ϕ : {i j : Carrier } → i ≤ j → X i ⊙→ X j
    reflex : {i : Carrier } → ϕ (reflexivity) ~ ⊙id (X i)
    transit : {i j k : Carrier } → (p : (_≤_ i j)) → (q : (_≤_ j k)) → (r : (_≤_ i k)) → ϕ q ⊙∘ ϕ p ~ ϕ r



module _ (C : Carpet {o} {ℓ} {e}) where
  open Carpet C 
  open SemiLattice J

  private variable
    i j k l : Carrier
  transit' : {i j k : Carrier} → (p : i ≤ j) → (q : j ≤ k) → ϕ q ⊙∘ ϕ p ~ ϕ (p ■ q)
  transit' p q = transit p q (p ■ q)

  Elts : Set o
  Elts = Σ (Carrier) (U⊙ ∘ X)
  
  EltsIsSet : isSet (Elts)
  EltsIsSet = eltsIsSet (Carrier , CarIsSet) (λ k → (U⊙ (X k) , snd (X' k)))
 

    
  toEl≡ : {x y : U⊙ (X j)} → x ≡ y → _≡_ {A = Elts} (j , x) (j , y)
  toEl≡ {j = j} p i = (j , p i) 
  _<_ : Elts → Carrier → Set e
  (i , x) < j = i ≤ j
  record ElUnder (j : Carrier) : Set (o ⊔ e) where
    constructor _,_
    field
      elem : Elts
      inScope : proj₁ elem ≤ j
  open ElUnder

  ≡ElUnder : {j : Carrier} → (x y : ElUnder j ) → elem x ≡ elem y → x ≡ y
  ≡ElUnder  x y p i = (p i) ,
    isProp→PathP {A = λ k → (proj₁ (p k)) ≤ _} (λ k → ≤isProp) (inScope x) (inScope y) i 
  infixl 5 _§_
  _§_ : ∀ {j} e → e < j → Elts
  _§_ {j} (i , x)  p = j ,  ⟦ ϕ p ⟧ x
  push : ElUnder l → Elts
  push x = (elem x § inScope x)
  _§refl=id : ∀ e → e § reflexivity ≡ e
  e §refl=id = λ i → (proj₁ e) , (reflex (proj₂ e) i)
------------
  --PROPERTIES
----------------
  actrans : ∀ {j k e} → (p : e < j) → (q : j ≤ k) → (e § p) § q ≡ (e § (p ■ q))
  actrans {e = e} p q i = _ , transit' p q (snd e) i
  _∣  : ∀ {j} {e e'} {p : e < j} {p' : e' < j} → (pf : e ≡ e') → e § p ≡ e' § p'
  _∣ {e = e} {e' = e'} {p} {p'} pf = cong push (≡ElUnder (e , p) (e' , p') pf)
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
  

  -- Equality After Applying a function
  record _≡[_]_ (x : Elts) (k : Carrier) ( y : Elts) : Set (o ⊔ e) where
    field
      left : fst x ≤ k
      right : proj₁ y ≤ k
      eq : x  § left ≡  y § right


  open _≡[_]_

  eq' : {x y : Elts} {k : Carrier}  {l' : fst x ≤ k} {r' : fst y ≤ k} → x ≡[ k ] y →  x § l' ≡ y § r'
  eq' {x = x} {y = y} p = x § _ ≡⟨ refl ∣ ⟩ x § (left p) ≡⟨ eq p ⟩ y § right p ≡⟨ refl ∣ ⟩ y § _ ∎
  ≡[_]IsProp : (x y : Elts) (k : Carrier) → isProp (x ≡[ k ] y)
  ≡[_]IsProp x y k = λ p q i → record {
    left = ≤isProp (left p) (left q) i ;
    right = ≤isProp (right p) (right q) i ;
    eq = isProp→PathP {A = λ x₁ → x § ≤isProp (left p) (left q) x₁ ≡ y § ≤isProp (right p) (right q) x₁ }
    (λ i₁ → EltsIsSet (x § ≤isProp (left p) (left q) i₁) (y § ≤isProp (right p) (right q) i₁)) (eq p) (eq q) i  }
  ----
---ACTIONS
  --
  fwd : {j' k : Carrier} →
    {x : Elts} →
    {y : ElUnder j'} →
    x ≡[ k ] (elem y) →
    x ≡[ k ∨ j' ] (push y) --(p $ ix)
    
  fwd {j'} {k} {ix} {(jy , p)} z = record {
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
  refl≡ : {x : Elts} → x ≡[ proj₁ x ] x
  refl≡ {x = x} = record { left = reflexivity ; right = reflexivity ; eq = refl }
  symm : {l : Carrier} → {x y : Elts} → x ≡[ l ] y → y ≡[ l ] x
  symm p = record { left = right p ; right = left p ; eq = λ i → (eq p) (~ i) }
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
  module _ (f : l ≤ k) {x y : ElUnder l} where
    myeqToPush≡ :  elem x ≡[ k ] elem y → push x ≡[ k ] push y
    myeqToPush≡ (x=y) = record { left = f ; right = f ; eq =
      push x § f
        ≡⟨ actrans (inScope x) f ⟩
      elem x § (inScope x ■ f)
        ≡⟨  eq' x=y  ⟩
      elem y § (inScope y ■ f)
        ≡˘⟨ actrans (inScope y) f ⟩ 
      push y § f ∎ }
    Push≡ToMyEq : push x ≡[ k ] push y → elem x ≡[ k ] elem y
    Push≡ToMyEq  moin = (record { left = inScope x ■ left moin ; right = inScope y ■  right moin ; eq =
      elem x § (inScope x ■ left moin) ≡˘⟨ actrans (inScope x) (left moin) ⟩ elem x § inScope x § left moin ≡⟨ eq moin ⟩ elem y § inScope y § right moin ≡⟨ actrans (inScope y) (right moin) ⟩ elem y § (inScope y ■ right moin)   ∎ })
  bwdHelper : {y : Elts} {x : ElUnder (proj₁ y)} → push x ≡ y → y ≡[ proj₁ y ] (elem x) 
  bwdHelper {x = (x , rr)} p = (record { left = reflexivity ; right = rr ; eq =  _ § reflexivity  ≡⟨ _ §refl=id ⟩ _ ≡˘⟨ p ⟩ (x § rr) ∎  }) 
  bwd : {l : Carrier} →  {y z : Elts} → {x : ElUnder (proj₁ y)} → push x ≡ y → z ≡[ l ] y → z ≡[ l ] elem x
  bwd {l = l} {x = (x , rr)} p q =  deeper (sup (right q) reflexivity ) (trans≡ q ((bwdHelper p))) 
--------
--HAVE FUN
----------
  fibre-map : {x y : ElUnder l} {f : l ≤ k} → (proj₂ (push x)) ≣[ ϕ f ] (proj₂ (push y)) →  elem x ≡[ k ] elem y  
  fibre-map {x = x} {y = y} {f = f} aha = record {
    left = inScope x ■ f ;
    right = inScope y ■ f ;
    eq =
      elem x § (inScope x ■ f)
        ≡˘⟨ actrans (inScope x) f ⟩
      push x § f
        ≡⟨ toEl≡ (toFib (ϕ f) aha) ⟩
      push y § f
        ≡⟨ actrans (inScope y) f ⟩
      elem y § (inScope y ■ f) ∎ }
  postulate FIBRE-IND :  {x y : ElUnder l} {f : l ≤ k} → isEquiv (fibre-map {x = x} {y = y} {f = f})
  fibre-inv : {x y : ElUnder l} {f : l ≤ k} → elem x ≡[ k ] elem y → (proj₂ (push x)) ≣[ ϕ f ] (proj₂ (push y))
  fibre-inv p = proj₁ (proj₁ (equiv-proof FIBRE-IND p))
  toIm : (f : k ≤ l) → [ x ∶ U⊙ (X k) ]⇒ ⟨ im (ϕ f) ⟩ (⟦ ϕ f ⟧ x)
  toIm f = intro λ y →  ∣  y , refl ∣₋₁ 
  push→Im' : (x : U⊙ (X k)) → (f : k ≤ l) → 【 im (ϕ f) 】
  push→Im' x f = (⟦ ϕ f ⟧ x) ,  toIm f x 
  push→Im : (x : ElUnder k) → (f : k ≤ l) → 【 im (ϕ f) 】
  push→Im x f = push→Im' (proj₂ (push x )) f 

  module _ {p : j ≤ k} {q : k ≤ l} where
    private
      f = ϕ p
      g = ϕ q
      h = ϕ (p ■ q)
    EpiIntro : ker g ⊂ im f → im g ⊂ im h → surj f
    EpiIntro info1 info2 = ⊂: (λ x → foo (proj₁ x)) where
      foo : [ x ∶ U⊙ (X k) ]⇒  ⟨ im f ⟩ x
      foo x =  takePreIm h (⟨ im f ⟩ x) (info2 & (push→Im' x q)) bar where
        la' : Σ (U⊙ (X k)) (λ y → asType (⟨ im f ⟩ y)  × y ≣[ g ] (x)) ⇒ ⟨ im f ⟩ x
        la' (.(pt (X k)) , (_ , kern zz)) = info1 & (_ ,  sym zz)
        la' (y , (p , inh)) = p

        la : Σ (U⊙ (X j)) (λ y → ⟦ f ⟧ y ≣[ g ] x) ⇒ ⟨ im f ⟩ x
        la (y , p') = la' ((⟦ f ⟧ y) , (toIm p y , p'))
        bar : Σ (U⊙ (X j)) (λ ur → ⟦ h ⟧ ur ≡ ⟦ g ⟧ x) ⇒ ⟨ im f ⟩ x
        bar (ur , ee) = la (ur , ((fibre-inv (symm ( bwd (toEl≡ ee) (deeper (left-Eat J q) (fwd refl≡) ) ))) ̇ inh' _ (reflex _))) 

     

  data MyEqualizer {l k : Carrier} (f : l ≤ k) (x y : ElUnder l) : Set (o ⊔ e) where
    jo : (elem x) ≡[ k ] (elem y)  → MyEqualizer f x y
  MyEqualIsProp : {l k : Carrier} (f : l ≤ k) (x y : ElUnder l) → isProp (MyEqualizer f x y)
  MyEqualIsProp f x y (jo p) (jo q) = cong jo (≡[_]IsProp _ _ _ p q)
  myEq≅Push≡ : {f : l ≤ k} {x y : ElUnder l} → (elem x ≡[ k ] elem y) ≅ (push x ≡[ k ] push y)
  myEq≅Push≡ {f = f} {x = x} {y = y} = myeqToPush≡ f , Push≡ToMyEq f , ((λ _ → ≡[_]IsProp _ _ _ _ _) , λ _ → ≡[_]IsProp  _ _ _ _ _  ) -- (record { equiv-proof = λ z → (( z) , ) , λ y₁ → {!!} })

