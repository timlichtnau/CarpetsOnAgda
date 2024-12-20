{-# OPTIONS --cubical --without-K #-}
open import Cubical.Data.Int.Base renaming ( neg to negate)
open import Cubical.Data.Int.Properties renaming ( isSetℤ to ℤisSet)
open import Cubical.Data.Int.Order renaming ( _≤_ to _≤ℤ_ ; isRefl≤ to ≤-refl ; isTrans≤ to ≤-trans)
open import Cubical.Data.Nat.Base using (suc)
open import CubicalBasics.PointedTypesCubical
open import HomoAlgStd
open import CubicalBasics.PointedTypesCubical
import UnivalentCarpet2
--open import Data.Product
open import CubicalBasics.cubical-prelude
open import CarpetCubical3
open import Agda.Builtin.Equality renaming (_≡_ to _≡'_)
open import SemiLattices
open import Cubical.Data.Int hiding (neg) -- ; _+_)
open import EqualitiesCubical
--open import Level
--open import Algebra.Construct.NaturalChoice.Base
--open import Axiom.UniquenessOfIdentityProofs
--open import Relation.Binary.Definitions

data Dir : Set where
  H : Dir
  V : Dir
  D : Dir
record Pos : Set where
  constructor _!_!_
  field
    dir : Dir
    xarg : ℤ
    yarg : ℤ

open Pos
toxy : Pos → ℤ × ℤ
toxy (d ! x ! y ) = (x , y)
neg : Dir → Dir
neg H = V
neg V = H
neg D = D
_+x_ : Dir → ℤ → ℤ
H +x y = 1 + y
V +x y = y
D +x y = 1 + y
_+y_ : Dir → ℤ → ℤ
H +y y = y
V +y y  = 1 + y
D +y y = 1 + y
infix 21 _°
_° : Pos → Pos
p ° = (dir p) ! (dir p +x xarg p) ! (dir p +y yarg p)
invVec : Pos → Pos
invVec (d ! x ! y) = d ! (- x) ! (- y)
infix 21 _!
_! : Pos → Pos
(v ! x ! y) ! = neg v ! x ! y
infixl 15 _✯_ 
_✯_ : ℤ → Pos → Pos
(pos 0) ✯ j = j
(pos (suc p)) ✯ j = (pos p) ✯ j °
(negsuc 0) ✯ j = invVec j
(negsuc (suc p)) ✯ j = (negsuc p) ✯ (invVec j ° )

module _  where
  _≤_ : ℤ × ℤ → ℤ × ℤ → Set
  _≤_ = λ (a , b) (a' , b') → (a ≤ℤ a') × (b ≤ℤ b')
  -- We want a relative version of grids, i.e. a carpet on J should be the same as the transportet carpet along p on J + p, for this we have to replace the Carrier by ℤ × ℤ
  --comp to FibreArgumentation
  J : SemiLattice lzero lzero lzero
  J = record
        { Carrier = ℤ × ℤ
        ; CarIsSet = λ _ _  p q i j → ((ℤisSet _ _ (λ i → proj₁ (p i)) (λ i → proj₁ (q i))) i j) , (((ℤisSet _ _ (λ i → proj₂ (p i)) (λ i → proj₂ (q i))) i j)) 
        ; _≤_ = _≤_
        ; ≤isProp = λ (p , p') (q , q') → λ i → ≤isProp p q i , ≤isProp p' q' i
        ; reflexivity =   ≤-refl , ≤-refl 
        ; _■_ = λ (p , q) (p' , q') → ≤-trans p p' , ≤-trans q q'
        ; _∨_ = λ (a , b) (a' , b') → max a a' , max b b' 
        ; comm = λ {(a , b)} {(a' , b')} i →         (Cubical.Data.Int.maxComm a a') i , (Cubical.Data.Int.maxComm b b') i

        ; uB = λ {(a , b)} {(a' , b')} →   ≤max , ≤max --≤-max a a' , ≤-max b b'
        ; sup = λ {(a , b)} {(a' , b')} {( a'' , b'')} p q → ( max-lub  (proj₁ p) (proj₁ q) ) , (max-lub  (proj₂ p) (proj₂ q) )
        } where
        postulate max-lub : { a b c : ℤ} → a ≤ℤ c →  b ≤ℤ  c → max a b ≤ℤ c
--        max-lub p q = {!!}

        postulate ≤isProp : {a b : ℤ} → isProp (a ≤ℤ b)
       -- ≤isProp p q = {!!} -- (≤-irrelevant p q)

        
  grid : Set (lsuc lzero)
  grid = CarpetOnJ J 
-- ⊔-identityˡ
--  ; ⊓-identityʳ  to  ⊔-identityʳ
 -- gridInduction : ∀ {e} → (A : grid → Pos → Set e) → ((G : grid) → A G (H ! 0 ! 0)) → (G : grid) → (p : Pos) → A G p
 -- gridInduction A indStart G p = {!indStart!}
  module GridHelper (G : grid) where

    C = CarpetOnJToCarpet G
    
    open UnivalentCarpet2 C hiding (_≤_) public
    ≤-suc' : (x : ℤ) → x ≤ℤ 1 + x
    ≤-suc' x = ≤-pos+-trans ≤-refl
    private
      r : Dir
      r = H
    f' : (p : Pos) → (xarg p , yarg p) ≤ (xarg ( p °) , yarg (p ° ))
    f' (H ! x ! y) =  ( ≤-suc' x  , ≤-refl)
    f' (V ! x ! y) =  (≤-refl ,  ≤-suc' y)
    f' (D ! x ! y) =  (≤-suc' x , ≤-suc' y)
    f : (p : Pos) → 𝕏 (xarg p , yarg p) ⊙→ 𝕏 (xarg ( p °) , yarg (p ° ))
    f p = ϕ (f' p)
    module _ (p : Pos) where
      
      f⟩ : _ ≤ _ -- (r +x (r +x i)) (r +y (r +y j))
      f⟩ = f' (p °)
      f⇣ :  _ ≤ _ -- (r +x (r +x i)) (r +y (r +y j))
      f⇣  = f' (p ° !)
      f| : (c : ℤ) → _ ≤ _
      f| c = f' ((c ✯ p ! ) !)
    module _ (i k : ℤ) where
     private 
       p = r ! i ! k
       g = f⇣ p
       j = f p
       h = f (D ! i ! k)


    exactRow : Pos → Set 
    exactRow p = im (ϕ (f' p)) ↔ ker (ϕ (f⟩ p))
    Exact : (r : Dir) → (l : ℤ) → Set
    Exact H l = {cnter : ℤ} →  exactRow (H ! cnter ! l)
    Exact V l = {cnter : ℤ} → exactRow (V ! l ! cnter)
    Exact D l = {cnter : ℤ} → exactRow ((D ! cnter ! l)) -- WEIRD

{--
  triangle : {X Y Z : Ptd} → (f : X ⊙→ Y) → (g : Y ⊙→ Z) → (h : X ⊙→ Z) → (g ⊙∘ f) ≈ h → grid
  triangle {X} {Y} {Z} f g h gf~h = (record {
    𝕏 = 𝕏 ;
    mycarp = record { ϕ = {! !} ; reflex = {!!} ; transit = {!!} }
    }) where

    𝕏' : ℤ → ℤ → Ptd
    𝕏' zero zero = X
    𝕏' zero (suc zero) = Y
    𝕏' zero (suc (suc x)) = P𝟏
    𝕏' 1 0 = Y
    𝕏' 1 1 = Z
    𝕏' 1 (suc (suc x)) = P𝟏
    𝕏' (suc (suc x)) 0 = P𝟏
    𝕏' (suc (suc x)) (suc y) = P𝟏
    f'' : (p : Pos) → 𝕏' (xarg p) (yarg p) ⊙→ 𝕏' (xarg (p °)) (yarg (p °)) -- (r +x i) (r +y j)
    f'' (H ! zero ! zero) =  f
    f'' (V ! zero ! zero) = f
    f'' (D ! zero ! zero) = h
    f'' (H ! 0 ! 1) = g
    f'' (V ! 0 ! 1) =  c1

    f'' (V ! 1 ! 0) = g
    f'' (H ! zero ! suc (suc yarg₁)) = c1
    f'' (H ! suc xarg₁ ! zero) = c1
    f'' (H ! suc xarg₁ ! suc yarg₁) = c1
    f'' (V ! zero ! suc yarg₁) = c1
    f'' (V ! suc (suc xarg₁) ! zero) =  c1
    f'' (V ! suc zero ! suc yarg₁) = c1
    f'' (V ! suc (suc xarg₁) ! suc yarg₁) = c1
    f'' (D ! suc x ! zero) =  c1
    f'' (D ! zero ! suc yarg₁) = c1
    f'' (D ! suc x ! suc yarg₁) = c1
    𝕏 : ℤ × ℤ → Ptd
    𝕏 = λ (i , j) → 𝕏' i j --}
  --  ϕ : {i j : (ℤ × ℤ)} → i ≤ j → 𝕏 i ⊙→ 𝕏 j
  --  ϕ {i = .ℤ.zero , b} {j = a' , b'} (z≤n , snd) = {!!}
  --  ϕ {i = .(ℤ.suc _) , b} {j = .(ℤ.suc _) , b'} (s≤s fst , snd) = {!!}
  {--
    comp' : (i j : ℤ) → f' (H ! i ! (suc j)) ⊙∘ f' (V ! i ! j) ≈ f' (D ! i ! j)
    comp' zero zero = gf~h
    comp' zero (suc j) = λ x → refl 
    comp' (suc i) j = λ x → refl
  --}


