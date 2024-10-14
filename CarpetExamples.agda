{-# OPTIONS --cubical #-}
open import CarpetCubical3 
open import CubicalBasics.PointedTypesCubical
--open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
--open import Data.Product
open import CubicalBasics.PropositionReasoning
--open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)
-- open import Relation.Binary.Core
--open import Function.Base using (_∘_)
--open import Relation.Binary.Definitions
--open import Relation.Binary.Structures using (IsPartialOrder)
open import Cubical.Data.Nat.Base using (ℕ ) renaming (_+_ to _++_)
open import Cubical.Data.Int.Order renaming ( _≤_ to _≤ℤ_ ; isRefl≤ to ≤-refl ; isTrans≤ to ≤-trans)
open import SemiLattices
open import CubicalBasics.cubical-prelude hiding (_∨_ ; _∧_)
open import CubicalBasics.cubicalEqualityReasoning
open import HomoAlgStd hiding (surjComp)

open import Grids
open import Cubical.Data.Int.Base -- hiding (_≤_)
import UnivalentCarpet2
import QuasiIsos
open import CarpetAufsatzExamples2
--open import Data.Integer.Properties using (n≤1+n ; ≤-refl)
{--
We use → instead of =>'
There are different ways to argue in Carpets. Suppose we have two pointed subtypes B B' of the same object 𝕏 j. In the following we only allow paths into these B's that have uncertainty at most k (*). K is defined as the kernel of j ≤ k. 
The only thing which we have to assume is supporterInduction

         K
         |↘
         B  ↘  
       ↗     ↘   
    A -------> P
     [↘]    ↗ 
         B'  
The use of this principle is that the uncertaintanty of A → B' can be huge, as its not needed to calculate the uncertainty of A --> P         
done by
  ROUNDTRIP
    a→b
  JUMPBACK
    a→b' ∶
    b'→p
  MOVECHILDREN edge ,
    k→p
  
where edge : A→B ∨ A→B' ≤ k recognizes (*). The Uncertainty is A→B ∨ (B'→P ∨ K→P)

__________________________________

Now we have some abbreviations:
1. FiberInduction is used whenever A → B is reflexivity, then the pattern is
   ROUNDTRIP
     b→b' ∶ b' → p
   MOVECHILDREN (edge : b→b' ≤ k) 
     < k→p >

2.1
  SupporterInduction over the roof (cmp. QuasiIsos) is used to avoid providing a map k→p.
  In most cases, it can be constructed whenever the map A → B' "factors" as A → 0 k ⇒ B', where ⇒ is some slightly stronger form of → (cmp. QuasiIsos).
  I believe → maybe could be replaced by ⇒ in most of the settings. Be aware, that this relation is not transitive.
  ROUNDTRIP
    A→B
  JUMPBACK
    A→0k ∶
    0k⇒[k]B'' ∶
    B''→P , (edge : A→0k ∨ A→B ≤ k)
  It has uncertainty A→B ∨ B''→P (pretty good)
2.2
  If A→B is refl, then we call this
  BACKWARDS
    A→0k ∶
    0k ⇒[k] B'' ∶
    B''→P , (edge : A→0k ≤ k)
--}


module _ (G : grid) where
  open GridHelper G
  open QuasiIsos C
  open Lemmata C
  module _ where
    private
      p : Pos
      p = V ! (0) ! (0)
    ExToEpi : exactRow p → isZeroObj (toxy (p ° °)) → Epi (f' p)
    ExToEpi ex ze = to⊂' (BACKWARDS % (FWD (f⟩ p)) ∷ intro⊂ Sth⊂Full ∷ intro⊆ ze ∶ 0⇒ker (f⟩ p) ∶ intro⊂ (proj₂ ex))
  i = pos 0
  j = pos 0
  
  module _ (ex0 : Exact H j) (ex1 : Exact H (1 + j))  where
 
   p = V ! (0) ! (0) -- V ! i ! j
   g : (n : ℕ) → (pos n , pos 0) ≤ (pos n , pos 1)
   g n = ( ≤-refl , zero-≤pos )

   m : (d : ℕ) (c : ℕ)  → _ ≤ _
   m d c = f' ((pos c) ✯ (((pos d) ✯ p) !))
   h = m 0
   k = m 1
   l = m 2
   u : (n : ℕ) → (pos n , pos 1) ≤ (pos n , pos 2)
   u n = ≤-refl , (suc-≤-suc zero-≤pos ) 
            {--
   h
     g
   k
     u
   l
   --}
   
 
   module VIERER (g0surj : Epi (g 0)) (g3mono : Mono (g 3)) where
     0⇒Kerh2 : 𝟎 (pos 3 , pos 1) ⇒[ _ ] Ker (h 2)
     0⇒Kerh2 = 
              (0⇒ker (g 3))  ✸
             int↔ (g 3) (Mono' g3mono)  ✸
             0↗ker (h 2) (g 3)
     Kerk1=>Imh0 : Ker (k 1) =>' Im (h 0)
     Kerk1=>Imh0 = intro⊂ (proj₂ ex1) ∷ BWD (k 0) ∷
         intro⊂ g0surj ∷ BWD (g 0) ∷ FWD (h 0)
         
     module VIERER-INJ (g1mono : Mono (g 1)) where
       cl1 : Ker (g 2) ==> Im (h 1)
       cl1 = 
         BACKWARDS %
         intro⊆ (ker (g 2) ⊂0) ∷ 0toF0 (k 2)  ∶
           0⇒Kerh2 ∶
         intro⊂ (proj₂ ex0)
    
       cl2 : Ker (g 1 ■ k 1) ==> Ker (h 1) -- 𝟎 (1 , 0)
       cl2 = 
         % (begin
         Ker (g 1 ■ k 1)
           ∼⟨ kerFWDFac {p = g 1} {q = k 1} ⟩
         Ker ( k 1)
           ∼⟨ Kerk1=>Imh0 ⟩
         Im (h 0)
           ∼⟨ intro⊂ (proj₁ ex0) ⟩
         Ker (h 1) ∎) where open ARG
       vierer-inj : Mono (g 2)
       vierer-inj = InjExt (subst≤ (λ t → ker (ϕ t) ⊂ ker (ϕ (h 1))) (DecUnc g1mono cl2)) (to⊂' cl1)
       
     module VIERER-SURJ  (g2surj : Epi (g 2))  where
       open ARG
       helper : Ker (k 1) ==> Im (g 1)
       helper = % Kerk1=>Imh0 ∷ FWD (g 1)
       helper' : Im (k 1) ==> Im (h 1)
       helper' =
         ROUNDTRIP
           Sth=>'Full ∷ intro⊂ (g2surj) ∷  BWD (g 2 )
         JUMPBACK %
           intro⊂ (proj₁ ex1) ∷
           intro⊆ (ker (k 2) ⊂0 ) ∶
           0⇒Kerh2 ∶
           intro⊂ (proj₂ ex0) ,
         (k 2)
       myh : Im (k 1) ==> Im (h 1 ■ g 2) -- im (ϕ (k 1)) ⊂ im (ϕ (h 1 ■ g 2))
       myh = % (_ , helper') ∷ intro⊆ (imf⊆imgf (h 1) (g 2))
       vierer-surj : Epi (g 1)
       vierer-surj = EpiIntro (to⊂' helper) (subst≤ (λ t → im (ϕ (k 1)) ⊂ im (ϕ t)) (to⊂' myh) ) {-- let
   
   h
     g
   k
     u
   l
   --}
   
   module 3x3 (V : (i' : ℤ) → Exact V (i + i'))
              (VMonos : (i' : ℕ) → Mono (g i'))
              (VEpis : (i' : ℕ) → Epi (u i'))
              (HEpi : (d : ℕ) → Epi (m d 2))              
              (HMono : (d : ℕ) → Mono (m d 0))
              where
    module H0Missing (H1 : Exact H (pos 1 + j))
                     (H2 : Exact H (pos 2 + j)) where

   
      
      foo :  Ker (u 2 ■ l 2) =>' Full (pos 2 , pos 0)
      foo = _ , ROUNDTRIP
            kerFWDFac' ( u 2) (l 2) ( u 2 ■ l 2)  ∷ 
            intro⊂ (proj₂ H2) ∷ BWD (l 1)
             ∷ (intro⊂ (VEpis 1)) ∷ BWD (u 1)  ∷  FWD (k 1)  ∶
            intro⊂ (proj₁ H1) ∷ intro⊆ (ker (k 2) ⊂0) ∷ 0toB0 ( g 2 ■ k 2) ∷ 0=>'Sth 
          MOVECHILDREN re 
           < intro⊂ (proj₂ (V (pos 2))) ∷ BWD (g 2) >  
      HEpi0 : Epi (h 2)
      HEpi0 = EpiIntro
        (to⊂ (% intro⊂ (VMonos 3) ∷ intro⊂ 0⊂Sth) (R∨ re))
        (to⊂ (% (intro⊂ (proj₁ (V (pos 3))) ∷ kerBWDFac (HEpi 1)) ∷ foo  ∷ FWD (h 2 ■ g 3)) re) 

      Im⊂Ker : Im (h 0) ==> Ker (h 1)
      Im⊂Ker = BACKWARDS %      
          BWD (h 0) ∷
          FWD (g 0) ∷
          FWD (k 0) ∷
          intro⊂ (proj₁ ex1) ∷
          intro⊆ (ker (k 1) ⊂0) ∶
          0⇒ker (g 2) ✸
          int↔ (g 2) (Mono' (VMonos 2)) ✸
          (0↗ker (h 1) (g 2)) ∶
          refl=>' 
      Ker⊂Im : Ker (h 1) ==> Im (h 0)
      Ker⊂Im = % intro⊂ (kerf⊂kergf (g 2) (g 1 ■ k 1)) ∷
               _ , ROUNDTRIP
               kerFWDFac {p = g 1} ∷ intro⊂ (proj₂ H1) ∷ BWD (k 0)
               JUMPBACK
               % FWD (g 1) ∷ intro⊂ (proj₁ (V (pos 1))) ∷
               intro⊆ (ker (u 1) ⊂0) ∶
               0⇒ker (l 0) ✸ int↔ (l 0) (Mono' (HMono 2)) ✸ 0↗ker (u 0) (l 0) ∶
               intro⊂ (proj₂ (V (pos 0))) ∷ BWD (g 0) ∷ FWD (h 0) , u 1

      H0 : (exactRow (H ! j ! (pos 0)) ) 
      H0 = to⊂' Im⊂Ker , DecUnc (VMonos 1) (Ker⊂Im)  

{-- OLD, BUT WORKING CODE
   helper' : Im (k 1) =>' Im (h 1)
         helper' =
               (ROUNDTRIP
                    Sth⊂Full ∷ intro⊂ (g2surj) ∷  BWD (g 2 )              
               JUMPBACK
                  begin
                    Im (k 1)
                      ∼⟨ intro⊂ (proj₁ (ex1 _)) ⟩
                    Ker (k 2)
                      ∼⟨ intro⊆ (ker⊂0 (k 2)) ⟩
                    𝟎 _
                      ∼⟨  ( 0toB0 (h 2 ■ g 3) )  ⟩
                    𝟎 _ ∎ ∶ 0=>'Sth {A = Ker (h 2)}
               MOVECHILDREN
                  (k 2) ∨R , intro⊂ (KernelFact g3mono))  ∷ intro⊂ (proj₂ (ex0 _))
         vierer-surj : surj (ϕ (g 1) )
         vierer-surj = to⊂ (
           ROUNDTRIP
             FWD (k 1) ∷
               helper' 
               ∷ (BWD (h 1) ∷ FWD (g 1))
               ∶ refl=>' {A = Im (g 1)}
           MOVECHILDREN reflexivity ,
            intro⊂ helper)
          (R∨ reflexivity) --}




