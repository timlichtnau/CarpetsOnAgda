{-# OPTIONS --cubical --without-K #-}
open import CarpetCubical3 
open import PointedTypesCubical
open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
open import Data.Product
open import PropositionReasoning
open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)
-- open import Relation.Binary.Core
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures using (IsPartialOrder)
open import Equalizer
open import SemiLattices
open import cubical-prelude hiding (_∨_ ; _∧_)
open import cubicalEqualityReasoning
open import HomoAlgStd
open import PropositionReasoning
import Relation.Binary.Reasoning.Preorder


module _ (C : Carpet {o} {ℓ} {e}) where
  open Carpet C 
  open SemiLattice J
  open Funs J
  open CarpetHelper C
  private variable
    i j k l : Carrier
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
      elem y § (inScope y ■ f) ∎ } where open Reasoning
  postulate FIBRE-IND :  {x y : ElUnder l} {f : l ≤ k} → isEquiv (fibre-map {x = x} {y = y} {f = f})
  fibre-inv : {x y : ElUnder l} {f : l ≤ k} → elem x ≡[ k ] elem y → (proj₂ (push x)) ≣[ ϕ f ] (proj₂ (push y))
  fibre-inv p = proj₁ (proj₁ (equiv-proof FIBRE-IND p))
  toIm : (f : k ≤ l) → [ x ∶ X k ]⇒ ⟨ im (ϕ f) ⟩ (⟦ ϕ f ⟧ x)
  toIm f y =  ∣  y , refl ∣₋₁ 
  push→Im' : (x : X k) → (f : k ≤ l) → 【 im (ϕ f) 】
  push→Im' x f = (⟦ ϕ f ⟧ x) ,  toIm f x 
  push→Im : (x : ElUnder k) → (f : k ≤ l) → 【 im (ϕ f) 】
  push→Im x f = push→Im' (proj₂ (push x )) f 

  module _ {p : j ≤ k} {q : k ≤ l} where
    private
      f = ϕ p
      g = ϕ q
      h = ϕ (p ■ q)
    EpiIntro : ker g ⊂ im f → im g ⊂ im h → surj f
    EpiIntro info1 info2 x =
      (a , aIsInPreImageofImX) ← info2 & imx ,
      la ( ⟦ f ⟧ a , (toIm p a , func1 a aIsInPreImageofImX)) 
       where --a aIsInPreImageofImX
        open Monad truncMonad
        imx = (push→Im' x q)
        func1 : (a : X j) → (⟦ h ⟧ a ≡ proj₁ imx ) → (⟦ f ⟧ a) ≣[ g ] x --
        func1 a ee =  begin
          ⟦ f ⟧ a
            ∼⟨ fibre-inv (bwd (toEl≡ ee) (deeper (left-Eat q) (fwd refl≡) ) ) ⟩
          snd (push ((k , x) , reflexivity))
            ∼⟨  inh' g (reflex x) ⟩
          x ∎  where open Relation.Binary.Reasoning.Preorder (ℙ g)
        la : Σ (X k) (λ y → asType (⟨ im f ⟩ y)  × y ≣[ g ] (x)) ⇒ ⟨ im f ⟩ x
        la (.(pt (𝕏 k)) , (_ , kern zz)) = info1 & (_ ,  sym zz)
        la (y , (p , inh)) = p
    surjComp : surj f → surj g → surj h
    surjComp info1 info2 x =
      (a , aP) ← info2 x ,
      (b , bP) ← info1 a ,
      return (b , (sym (transit' p q _) ∙ cong ⟦ g ⟧ bP ∙ aP)) where open Monad truncMonad
    surjComp' : surj f → surj h → surj g
    surjComp' info1 info2 x =
      (a , aP) ← info2 x ,
      return (⟦ f ⟧ a , transit' p q _ ∙ aP)   where open Monad truncMonad
   
--    surjComp2 : surj f → surj g → surj h
