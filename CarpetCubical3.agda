{-# OPTIONS --cubical #-}
open import CubicalBasics.PointedTypesCubical
-- open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
-- open import Data.Product
open import CubicalBasics.PropositionReasoning
--open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)
-- open import Relation.Binary.Core
-- open import Function.Base using (_∘_)
-- open import Relation.Binary.Definitions
--open import Relation.Binary.Structures using (IsPartialOrder)
-- open import Equalizer
open import SemiLattices
open import CubicalBasics.cubical-prelude hiding (_∨_ ; _∧_)
open import CubicalBasics.cubicalEqualityReasoning
open import HomoAlgStd
open import CubicalBasics.PropositionReasoning
--import Relation.Binary.Reasoning.Preorder
open import CubicalBasics.IsomorphismCubical
module CarpetCubical3 where
private variable
  o e : Level


record CarpetOn {o l e : Level} (J : SemiLattice o l e) (𝕏 : SemiLattice.Carrier J → Ptd {lzero} ) : Type (o ⊔ l ⊔ e) where
    open SemiLattice J
    field
      ϕ : {i j : Carrier } → i ≤ j → 𝕏 i ⊙→ 𝕏 j
      reflex : {i : Carrier } → ϕ (reflexivity) ~ ⊙id (𝕏 i)
      transit : {i j k : Carrier } → (p : (_≤_ i j)) → (q : (_≤_ j k)) → (r : (_≤_ i k)) → ϕ q ⊙∘ ϕ p ~ ϕ r

record CarpetOnJ {o l e : Level} (J : SemiLattice o l e) : Type (lsuc o ⊔ l ⊔ e) where
  open SemiLattice J
  field
   𝕏 : Carrier → Ptd
   mycarp : CarpetOn J 𝕏

record Carpet {o l e : Level} : Set (suc l ⊔ suc e ⊔ suc o) where

  field
    -- record {Carrier = I ; _≈_ =  _≈_ ; _≤_ = _≤_ ; isPartialOrder = isPartialOrder }  : Poset o l e


    J : SemiLattice o l e
  open SemiLattice J
  field
    X : Carrier → Set
    XisSet : (i : Carrier) → isSet (X i)
    pts : (i : Carrier) →  X i
 
  field
    myCarp : CarpetOn J (λ i → ptd (X i , XisSet i)  (pts i)  )
  open CarpetOn myCarp public
  
CarpetOnJToCarpet : {J : SemiLattice o ℓ e} → CarpetOnJ J → Carpet {o} {ℓ} {e}
CarpetOnJToCarpet {J = J} myca = record { J = J ; X = λ j → U⊙ (𝕏 j) ; XisSet = λ j →  UisSet (𝕏 j) ; pts = λ j → pt (𝕏 j) ; myCarp = mycarp }    where open CarpetOnJ myca
module CarpetHelper (C : Carpet {o} {ℓ} {e}) where
  open Carpet C public

  open Funs J public
  open SemiLattice J public
  𝕏 : Carrier → Ptd
  𝕏 i =  ptd (X i , XisSet i)  (pts i)
  private variable
    i j k l : Carrier
  transit' : {i j k : Carrier} → (p : i ≤ j) → (q : j ≤ k) → ϕ q ⊙∘ ϕ p ~ ϕ (p ■ q)
  transit' p q = transit p q (p ■ q)

  Elts : Set o
  Elts = Σ (Carrier) X 
  
  EltsIsSet : isSet (Elts)
  EltsIsSet = eltsIsSet (Carrier , CarIsSet) (λ k → X k , XisSet k)
 
  doesntMatter : {p q : i ≤ j} → ϕ p ~ ϕ q 
  doesntMatter {p = p} {q = q} x = sym (reflex _) ∙ transit p reflexivity q x
    
  toEl≡ : {x y : X j} → x ≡ y → _≡_ {A = Elts} (j , x) (j , y)
  toEl≡ {j = j} p i = (j , p i)
  isEmb : {x y : X j} →  _≡_ {A = Elts} (j , x) (j , y) → x ≡ y
  isEmb  {j = j} {x = x} {y = y} p =   sym ( substRefl X x )   ∙ first  where -- hcomp (λ k → λ { (i = i0) → {!!} ; (i = i1) → {!!} }) {!proj₂ (p i)!}
    H : cong proj₁ p ≡ refl
    H = CarIsSet j j (cong proj₁ p) refl
    first : subst X refl x ≡ y
    first = subst (λ j=j →  subst X j=j x ≡ y ) H (fromPathP λ i → proj₂ (p i))
  data _≲_ (ix : Elts) (j : Carrier) : Set e where
    € : proj₁ ix ≤ j → ix ≲ j
  _<_ : (ix : Elts) → (j : Carrier) →  Set e
  ix < j = proj₁ ix ≤ j


  ElUnder : Carrier → Set (o ⊔ e)
  ElUnder j = Σ[ e ∈ Elts ] (proj₁ e ≤ j)

  elem : ElUnder j → Elts
  elem = proj₁
  inScope : (x : ElUnder j) → proj₁ (elem x) ≤ j
  inScope = proj₂
 
 {-- record ElUnder (j : Carrier) : Set (o ⊔ e) where
    constructor _,_
    field
      elem : Elts
      inScope : proj₁ elem ≤ j
  open ElUnder public
--}
  ≡ElUnder : {j : Carrier} → (x y : ElUnder j ) → elem x ≡ elem y → x ≡ y
  ≡ElUnder  x y p i = (p i) ,
    isProp→PathP {A = λ k → (proj₁ (p k)) ≤ _} (λ k → ≤isProp) (inScope x) (inScope y) i 
  infixl 5 _§_
  _§_ : ∀ {j} e → e < j → Elts
  _§_ {j} (i , x)  p = j ,  ⟦ ϕ p ⟧ x
  _§§_ : ∀ {j} e → e ≲ j → Elts
  _§§_ {j} (i , x)  (€ p) = j ,  ⟦ ϕ p ⟧ x 
  push : ElUnder l → Elts
  push x = (elem x § inScope x)
  §refl=id : ∀ {e} → e § reflexivity ≡ e
  §refl=id {e} = λ i → (proj₁ e) , (reflex (proj₂ e) i)

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
      ≡⟨  refl ∣ ⟩ 
    e § (p' ■ q')
      ≡˘⟨ actrans p' q' ⟩
    e § p' § q' ∎  where open Reasoning
  

  -- Equality After Applying a function
  record _≡[_]_ (x : Elts) (k : Carrier) ( y : Elts) : Set (o ⊔ e) where
    field
      left : fst x ≤ k
      right : proj₁ y ≤ k
      eq : x  § left ≡  y § right


  open _≡[_]_ public
  infix 4 _≡[_]_

  eq' : {x y : Elts} {k : Carrier}  {l' : fst x ≤ k} {r' : fst y ≤ k} → x ≡[ k ] y →  x § l' ≡ y § r'
  eq' {x = x} {y = y} p = x § _ ≡⟨ refl ∣ ⟩ x § (left p) ≡⟨ eq p ⟩ y § right p ≡⟨ refl ∣ ⟩ y § _ ∎ where open Reasoning
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
    left = (left z) ■ (uB ) ;
    right = (uB ) ■  (PathTo≤ comm) ;
    eq =    ix § (left z ■ uB )
              ≡˘⟨ actrans (left z) (uB) ⟩
            ix § left z § (uB)
              ≡⟨  eq z ∣  ⟩ 
            jy § right z § uB
              ≡⟨ (commSq jy (right z) (uB ) p (uB' )) ⟩
            jy § p § uB ■ PathTo≤ comm ∎
              


    } where open Reasoning
  refl≡' : {x y : X j} → x ≡ y → (j , x) ≡[ j ] (j , y)
  refl≡' p = record { left = reflexivity ; right = reflexivity ; eq = §refl=id ∙ toEl≡ p ∙ sym §refl=id  }
  refl≡ : {x : Elts} → x ≡[ proj₁ x ] x
  refl≡ {x = x} = refl≡' refl 
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
    } where open Reasoning
  syntax deeper p r = p ⅋ r
  trans≡ : {l k : Carrier} →  {x y z : Elts} →  x ≡[ k ] y → y ≡[ l ] z → x ≡[ k ∨ l ] z
  trans≡ {x = x} {y = y} {z = z} p q = record {
    left = left p ■ uB  ;
    right = right q ■ uB'   ;
    eq =
      x § (left p ■ uB)
        ≡˘⟨ actrans (left p) (uB) ⟩
      x § left p § uB 
        ≡⟨ eq p ∣  ⟩
      y § right p § uB 
        ≡⟨  commSq y (right p) (uB) (left q) (uB' )  ⟩ --{l = (proj₁ (y § left q))}
      y § left q § uB' 
        ≡⟨ eq q ∣  ⟩
      z § right q § uB' 
        ≡⟨ actrans (right q) (uB' ) ⟩ 
      z § (right q ■ uB') ∎ } where open Reasoning
        

  bwdHelper : {y : Elts} {x : ElUnder (proj₁ y)} → push x ≡ y →  (elem x) ≡[ proj₁ y ] y
  bwdHelper {x = (x , rr)} p = (record { left = rr ; right = reflexivity ; eq =   (x § rr)  ≡⟨ p ⟩ _ ≡˘⟨ §refl=id ⟩ _  § reflexivity ∎  })  where open Reasoning
  bwd : {l : Carrier} →  {y z : Elts} → {x : ElUnder (proj₁ y)} → push x ≡ y → z ≡[ l ] y → elem x ≡[ l ] z
  bwd {l = l} {x = (x , rr)} p q =  deeper (sup (right q) reflexivity) (trans≡ (bwdHelper  p) (symm q)) 
  fwdEasy : {x : X i} → (p : i ≤ j) → (i , x) ≡[ j ] ((i , x) § p)
  fwdEasy p = deeper (sup p reflexivity) (fwd refl≡ )

