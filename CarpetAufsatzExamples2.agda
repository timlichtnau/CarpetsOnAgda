{-# OPTIONS --cubical -WnoUnsupportedIndexedMatch #-}
open import CarpetCubical3 
open import CubicalBasics.PointedTypesCubical
-- open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
-- open import Data.Product
open import CubicalBasics.PropositionReasoning
-- open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)
-- open import Relation.Binary.Core
-- open import Function.Base using (_∘_)
-- open import Relation.Binary.Definitions
-- open import Relation.Binary.Structures using (IsPartialOrder)
open import Equalizer
open import SemiLattices
open import CubicalBasics.cubical-prelude hiding (_∨_ ; _∧_)
open import CubicalBasics.cubicalEqualityReasoning
open import HomoAlgStd hiding (surjComp)
import QuasiIsos
-- import Relation.Binary.Reasoning.Base.Single
import UnivalentCarpet2
module CarpetAufsatzExamples2 where
module Lemmata {o e} (C : Carpet {o} {ℓ} {e}) where
  open UnivalentCarpet2 C
  open ARG
  open QuasiIsos C
  private variable
    i j k l : Carrier

  module _ {p : j ≤ k} {q : k ≤ l} where
    private
      r = p ■ q



    surjComp : surj (ϕ p) → surj (ϕ q) → surj (ϕ r)
    surjComp surjf surjg = to⊂ (proj₂ foo') (R∨ (q ∨R)) where

      open ARG
      foo' : Full l =>' Im r
      foo' = begin
         Full _
           ∼⟨ intro⊂ surjg ⟩ 
         Im q
           ∼⟨ BWD q ⟩ 
         Full k
          ∼⟨ intro⊂ surjf ⟩
        Im p
          ∼⟨ BWD p ⟩ -- BWD p ⟩
        Full j
          ∼⟨ FWD (p ■ q) ⟩
         Im (p ■ q) ∎ 
         
    surjComp' : surj (ϕ p) → surj (ϕ r) → surj (ϕ q)
    surjComp' surjf surjh = to⊂ (proj₂ foo) (sup reflexivity reflexivity) where
      open ARG
      foo : Full l =>' Im q
      foo = begin
        Full l
          ∼⟨ intro⊂ surjh ⟩
        Im r
          ∼⟨ BWD r ⟩
        Full j
          ∼⟨ FWD p ⟩
        Im p
          ∼⟨ FWD q ⟩         
        Im q ∎ 
    injComp : Mono p → Mono q → Mono r
    injComp m m' = to⊂ me re where
      me : Ker (p ■ q) =>'[ UNC (intro⊂ m) ] 𝟎 j
      me =
        BACKWARDS
          proj₂ (intro⊆ (ker r ⊂0)) ∶
          0⇒ker q ✸
          (int↔ q (Mono' m')) ✸
          0↗ker p q  ∶
          intro⊂ m 
    EpiIntro : ker (ϕ q) ⊂ im (ϕ p) → im (ϕ q) ⊂ im (ϕ r) → surj (ϕ p)
    EpiIntro kerg⊂imf img⊂imh = to⊂ (
      ROUNDTRIP
        begin
          Full k
            ∼⟨ FWD q ⟩
          Im q
            ∼⟨ intro⊂ img⊂imh ⟩
          Im r
            ∼⟨ BWD r ⟩
          Full j
            ∼⟨ FWD p ⟩
          Im p ∎  ∶
        refl=>'
      MOVECHILDREN
         R∨ q 
        < intro⊂ kerg⊂imf > )
      (R∨ re)
    InjExt : ker (ϕ r) ⊂ ker (ϕ p) → ker (ϕ q) ⊂ im (ϕ p) → Mono q
    InjExt ker-r⊂ker-p kerq⊂imp = to⊂ (proj₂ (foo ∷ (intro⊆ (ker p ⊂0)))) (R∨ p ∨R ) where

      foo : Ker q =>' Ker p
      foo =  _ , ROUNDTRIP
                      begin
                       Ker q
                         ∼⟨ intro⊂ kerq⊂imp ⟩
                       Im p
                         ∼⟨ BWD p ⟩
                       Full j ∎
            JUMPBACK
              % (intro⊆ (ker q ⊂0)) ∶
              0⇒ker r ∶
              intro⊂ ker-r⊂ker-p , q
    kerBWDFac : Epi p → Ker q =>' Ker r
    kerBWDFac surjp = _ ,
      ROUNDTRIP
        intro⊂ (Sth⊂Full) ∷ intro⊂ (surjp) ∷ BWD p
      JUMPBACK
        % intro⊆ (ker q ⊂0) ∶ 0⇒ker r ∶ refl=>' , q
    kerFWDFacExp : Ker r =>'[ k ] Ker q
    kerFWDFacExp = END (back' (%  IncUncert' (
             _ , ROUNDTRIP
                FWD p
              JUMPBACK  %
              (intro⊆ (ker r ⊂0)) ∶
                0⇒ker q ∶ refl=>' , q) (re ∨R)))
    kerFWDFac : Ker r =>' Ker q
    kerFWDFac = _ , kerFWDFacExp
  --tp : {j : Carrier } {X Y : (SubPtd (𝕏 j))} (p : X ≡ Y)  → (j , X) =>'[ j ] (j , Y)
  --tp {j = j} {X} {Y} p = {!transit!} --  subst (λ i → (j , X) =>'[ j ] (j , (p i))) (% refl=>')
  kerFWDFac'Expl : {i j k : Carrier} (p : i ≤ j) (q : j ≤ k) (r : i ≤ k) →  Ker r =>'[ j ] Ker q
  kerFWDFac'Expl {i = i} {j = j} p q r = % trans=>' ( _ ,  EQUAL (subst≤ (λ q → Ker r ~~ i  ~> Ker q) (provider' refl=> ))) (kerFWDFac {p = p} {q = q})  -- Ker r ~~ daIn (Ker q) ~> Ker q
  kerFWDFac' : {i j k : Carrier} (p : i ≤ j) (q : j ≤ k) (r : i ≤ k) →  Ker r =>' Ker q
  kerFWDFac' {i = i} p q r = _ , kerFWDFac'Expl p q r
  
{-- OLD BUT WORKING CODE
    InjExtOld : mono (ϕ r) → ker (ϕ q) ⊂ im (ϕ p) → mono (ϕ q)
    InjExtOld monoh kerg⊂imf =  to⊂ (foo ∷ 0toF0 p) (R∨ sup p p ∨R)  where

      foo : Ker q =>' 𝟎 j
      foo = ROUNDTRIP
                     begin
                       Ker q
                         ∼⟨ intro⊂ kerg⊂imf ⟩
                       Im p
                         ∼⟨ BWD p ⟩
                       Full j ∎
           JUMPBACK
                     begin
                       Ker q
                         ∼⟨ intro⊆ (ker q ⊂0) ⟩
                       𝟎 l
                         ∼⟨ 0toB0 r ⟩
                       𝟎 j ∎ ∶ refl=>'
           MOVECHILDREN
                     q ∨R ,  intro⊂ monoh
    KernelFact : mono (ϕ q) → ker (ϕ (p ■ q)) ⊂ ker (ϕ p) -- general setting: last morphism is injective, 
    KernelFact monoq = to⊂ (
      ROUNDTRIP
        (ROUNDTRIP
                 FWD p
        JUMPBACK
          intro⊆ (ker (p ■ q) ⊂0) ∷ 0toB0 q ∶ refl=>'
        MOVECHILDREN
          q ∨R , (intro⊂ monoq)) ∷ 0toB0 p ∶ 0=>'Sth 
      MOVECHILDREN
        sup reflexivity (R∨ reflexivity) , refl=>')
      (R∨ reflexivity)



--}
