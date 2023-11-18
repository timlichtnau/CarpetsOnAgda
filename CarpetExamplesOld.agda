{-# OPTIONS --cubical --without-K #-}
open import CarpetCubical3 
open import CubicalBasics.PointedTypesCubical
open import Relation.Binary.Bundles 
open import Agda.Builtin.Sigma
open import Data.Product
open import CubicalBasics.PropositionReasoning
open import Level
--open import Relation.Binary.PropositionalEquality hiding (trans)
-- open import Relation.Binary.Core
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures using (IsPartialOrder)
open import Data.Nat.Base using (ℕ ; z≤n ; s≤s)
open import SemiLattices
open import CubicalBasics.cubical-prelude hiding (_∨_ ; _∧_)
open import CubicalBasics.cubicalEqualityReasoning
open import HomoAlgStd hiding (surjComp)

open import Grids
open import Data.Integer.Base hiding (_≤_)
import UnivalentCarpet2
import QuasiIsos
open import CarpetAufsatzExamples2
open import Data.Integer.Properties using (n≤1+n ; ≤-refl)
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
  
where edge : A→>B ∨ A→B' ≤ k recognizes (*). The Uncertainty is A→B ∨ (B'→P ∨ K→P)

__________________________________

Now we have some abbreviations:
1. FiberInduction is used whenever A → B is reflexivity, then the pattern is
   ROUNDTRIP
     b→b' ∶
   MOVECHILDREN (edge : b→b' ≤ k) , 
     k→p

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
      p = V ! (+ 0) ! (+ 0)
    ExToEpi : exactRow p → isZeroObj (toxy (p ° °)) → Epi (f' p)
    ExToEpi ex ze = to⊂' (BACKWARDS % (FWD (f⟩ p)) ∷ intro⊂ Sth⊂Full ∷ intro⊆ ze ∶ 0⇒ker (f⟩ p) ∶ intro⊂ (proj₂ ex))
  i = + 0
  j = + 0
  module _ (ex0 : Exact H j) (ex1 : Exact H (+ 1 + j))  where
   
   p = V ! i ! j
   g : (n : ℕ) → (+ n , + 0) ≤ (+ n , + 1)
   g n = ( ≤-refl , +≤+ z≤n )
   h : (c : ℕ) → _ ≤ _
   h n = f' ((+ n) ✯ p !) -- z≤n , n≤1+n n --
   k : (c : ℕ) → _ ≤ _
   k n = f' ((+ n) ✯ (p ° !))
   l : (c : ℕ) → _ ≤ _
   l n = f' ((+ n) ✯ (p ° ° !))
   u : (n : ℕ) → (+ n , + 1) ≤ (+ n , + 2)
   u n = ≤-refl , +≤+ (s≤s z≤n) 
   module VIERER (g0surj : Epi (g 0)) (g3mono : Mono (g 3)) where
     0⇒Kerh2 : 𝟎 (+ 3 , + 1) ⇒[ _ ] Ker (h 2)
     0⇒Kerh2 = 
              (0⇒ker (g 3))  ✸
             int↔ (g 3) (Mono' g3mono)  ✸
             0⇔ker (h 2) (g 3)
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
         ROUNDTRIP
           FWD (g 1)
         JUMPBACK %
           intro⊆ (ker (g 1 ■ k 1) ⊂0)  ∶
           0⇒ker (k 1) ∶
          Kerk1=>Imh0 ∷
           (intro⊂ (proj₁ ex0)) , k 1
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
       vierer-surj : Epi (g 1)
       vierer-surj = EpiIntro (to⊂' helper) let
         h : Im (k 1) ==> Im (h 1 ■ g 2) -- im (ϕ (k 1)) ⊂ im (ϕ (h 1 ■ g 2))
         h = % (_ , helper') ∷ intro⊆ (imf⊆imgf (h 1) (g 2)) 
         in subst≤ (λ t → im (ϕ (k 1)) ⊂ im (ϕ t)) (to⊂' h)
         {--
   h
     g
   k
     u
   l
   --}

   module 3x3 (V : (i' : ℤ) → Exact V (i + i'))   (H1 : Exact H (+ 1 + j)) (H2 : Exact H (+ 2 + j)) where
--(HEpi1 : Epi (
    foo : Im (g 3) ==> Full _
    foo =
      ROUNDTRIP
        intro⊂ (Sth⊂Full) ∷ {!intro⊂ (VEpis 1)!}
      JUMPBACK
        {!!} ∶ {!!} ∶ {!!}
      , {!!}
    VMonos : (i' : ℕ) → Mono (g i')
    VMonos = {!!}
    VEpis : (i' : ℕ) → Epi (u i')
    VEpis i = {!ExToEpi ? ?!}
    HEpi0 : Epi (h 2)
    HEpi0 = EpiIntro (to⊂ (% intro⊂ (VMonos 3) ∷ intro⊂ 0⊂Sth) (R∨ re)) {!!}
    Im⊂Ker : Im (h 0) ==> Ker (h 1)
    Im⊂Ker = BACKWARDS %      
        BWD (h 0) ∷
        FWD (g 0) ∷
        FWD (k 0) ∷
        intro⊂ (proj₁ ex1) ∷
        intro⊆ (ker (k 1) ⊂0) ∶
        0⇒ker (g 2) ✸
        int↔ (g 2) (Mono' (VMonos 2)) ✸
        (0⇔ker (h 1) (g 2)) ∶
        refl=>' --  ∷ {!!}
    H0 : (exactRow (H ! j ! (+ 0)) ) 
    H0 = to⊂' Im⊂Ker , {!!} 
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
