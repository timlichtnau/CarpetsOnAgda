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
--open import Relation.Binary.Definitions
--open import Relation.Binary.Structures using (IsPartialOrder)

open import SemiLattices
open import CubicalBasics.cubical-prelude hiding (_∨_ ; _∧_)
open import CubicalBasics.cubicalEqualityReasoning
open import HomoAlgStd

open import Grids hiding (_≤_)
open import Cubical.Data.Nat.Base -- hiding (_! ; _≤_ ; _⊔_)
import UnivalentCarpet2
-- open import CarpetAufsatzExamples2
import SmartImplication
open import Cubical.Data.Nat.Properties -- using (n≤1+n ; ≤-refl)
{--
There are two notions in this chapter:
 0 . A ⇔ B is saying that B is equal to the pushforward of A along |A|of cocartesian morphism : 
 1. A ⇒ B are


--}

module QuasiIsos {o e} (C : Carpet {o} {ℓ} {e})  where

  open UnivalentCarpet2 C
  open Monad truncMonad
 
  private variable
    i j k : Carrier

  0toB0 : (p : k ≤ j) → 𝟎 j =>' 𝟎 k
  0toB0 {j = j} p = _ , START (AR (λ x → return (((pts _) , refl) , deeper (sup reflexivity reflexivity) (trans≡ (refl≡' (proj₂ x)) (symm (bwd (toEl≡ (psv (ϕ p))) refl≡))) )))
  private    
    0&0 : 𝟎 j =>' 𝟎 k --NEEDED?
    0&0 {j = j} {k = k} =  0toF0 uB ∷ 0toB0 uB' 
--  
{--
A ⇒[ l ] B tells you A =>' B and that one of the equivalent things holds
0. im (A ×ₗ FB → FB) ⊂ B.  
1. the embedding A ×ₗ B → A ×ₗ FB is surjective, i.e. an equivalence.
3. A => FB factors through A => B => FB





the map ρ is cocartesian (Sure?): Given a diagram

         B'
         
   __    ^
     |   | ∃! 
  //     |
 //  ρ
A   ⇒    B

_____________________
     l
i ------> j
Means that there exists a unique morphism B -> B over the identity of j (i.e. an inclusion). For the definition of the index category see overleaf.

--}
  _⇒_ : SubEl → SubEl → Set (ℓ-max (ℓ-max (ℓ-suc ℓ-zero) o) e)
  A ⇒ B = Σ[ ρ ∈ A =>' B ] (
    ∀ b → F B ~ b ~ UNC ρ ~> A 
   → asType (b ∈∈ sub B))

{--  _∣_>_ : {A B : SubEl} → (ρ : A ⇒ B) → ∀ b → Σ-syntax 【 sub A 】
                                                (λ y →
                                                   (daIn (F B) , proj₁ b) ≡[ UNC (proj₁ ρ) ] (daIn A , proj₁ y)) → asType (b ∈∈ sub B)--}
--  syntax ρ ∣ b > x = ρ b (return x) -- where open Monad truncMonad
  _⇒[_]_ : SubEl → Carrier → SubEl → Set (ℓ-max (ℓ-max (ℓ-suc ℓ-zero) o) e)

  A ⇒[ l ] B = Σ[ ρ ∈ A ⇒ B ] (l ≡ UNC (proj₁ ρ))

    
  int⊂ : {A B : SubPtd (𝕏 j)} → A ⊂ B → (j , A) ⇒ (j , B)
  int⊂ {B = B} p = intro⊂ p , λ b aq →
    take
     (a , q) ← aq ,
    subst T⟨ B ⟩ (  sym (reflex _) ∙ doesntMatter _ ∙  isEmb (eq (symm q)) ∙ doesntMatter _ ∙ (reflex _) ) (p & a)
    to prove ⟨ B ⟩ (proj₁ b) -- (a , q) → 
  0⇒ker : (p : k ≤ j) → 𝟎 j ⇒[ j ] Ker p
  0⇒ker {j = j} p =  foo , refl where -- left' (back (0toB0 p ∷ 0s))
    open Reasoning

    0s = (0=>'Sth {A = Ker p})
    ut = UNCTrans ( 0toB0 p ) 0s  ■ sup reflexivity p
    foo : 𝟎 j ⇒ Ker p
    foo = IncUncert' ( 0toB0 p ∷ 0=>'Sth) ut , λ (b , pff) →
     ( take (px , x) ,          
         (
        ( ⟦ ϕ p ⟧ b
            ≡⟨ doesntMatter _ ⟩ --sym (transit _ _ p b) 
          ⟦ ϕ (left x)  ⟧ b 
            ≡⟨ (isEmb ( (eq x))) ⟩
            (⟦ ϕ (right x) ⟧ (proj₁ px))
            ≡⟨ cong  ⟦ ϕ (right x)  ⟧ (proj₂ px)  ⟩
          ⟦ ϕ (right x) ⟧ (pt (𝕏 j) )
            ≡⟨ psv (ϕ _) ⟩
          pt (𝕏 j) ∎) )
                 to prove
         ( ( b , *) ∈∈ ker (ϕ p) ) )

  record _↗[_]_ (A : SubEl)  (j : Carrier) (B : SubEl) : Set (e ⊔ o ⊔ lsuc lzero) where
    constructor _§$_§$_
    field
      A⇒B : A ⇒ B
      B=>'A : daIn B ≤ daIn A -- F B =>[ UNC (proj₁ ( A⇒B)) ] F A
      lenProof : (UNC (proj₁ A⇒B)) ≤ j

  0↗ker : (p : k ≤ j) (ed : j ≤ i) → 𝟎 j ↗[ i ] Ker p
  0↗ker p ed = (proj₁ (0⇒ker p)) §$ p §$ ed --((intro⊆ (p , λ (x , _) → *)) , re)
  0↗ker' : (p : k ≤ j) → 𝟎 j ↗[ j ] Ker p
  0↗ker' p = 0↗ker p reflexivity

  -- There are two ways to concat ⇒-paths : the first is used whenever the first path has smaller uncertainty as the second, the application would be everything which was done by ∷ before.
  int↔ : {A B : SubPtd (𝕏 j)} → (ed : j ≤ k) →  A ↔ B → (j , A) ↗[ k ] (j , B)
  int↔ ed p = int⊂ (proj₁ p) §$  re §$ ed -- IncUncert' refl=>' reflexivity , reflexivity  §$ ed
  trans'⇒ : {A B C : SubEl} → ((A=>B , _) : A ⇒ B) → ((B=>C , _) : B ⇒ C) → UNC A=>B ≤ UNC B=>C → A ⇒ C
  trans'⇒  {C = C} (A=>B , a-b) (B=>C , b-c) pf = IncUncert' (A=>B ∷ B=>C) (UNCTrans A=>B B=>C ■  pf ∨R ) , (λ c →
    take (a , c=a) ,
    desquash (b , a=b) ← provider (back A=>B) a ,
    return (b-c c (return (b , (R∨ pf) ⅋ trans≡ c=a a=b)))
    to prove (c ∈∈ (sub C))) 
   -- Otherwise you use the second one, thE Uncertainty have to be as follows: B⇒A ≤ A⇒B ≤ A'⇒A
  infixl 5 _✸_
  _✸_ : {A' A B : SubEl} {l : Carrier} → (γ : A' ⇒[ l ] A) → A ↗[ l  ]  B → A' ⇒[ l ] B -- (B=>'A , BA≤AB)
  _✸_ {A' = A'} {A = A}  {B = B} {l = l }((A'=>'A , a'-a) , lenProof) ((A=>'B ,  a-b) §$ b≤a §$ AB≤A'A) = (IncUncert' (A'=>'A ∷ A=>'B) (((UNCTrans A'=>'A A=>'B ■ ( left-map (proj₂ lp) ■ R∨ AB≤A'A ))) )  , foo) , refl where
    lp = convertEq lenProof
    BA≤AB : daIn A ≤ UNC A=>'B
    BA≤AB = left' (back A=>'B)
    B=>'A : F B =>' F A
    B=>'A = FWD b≤a ∷ Sth=>'Full 
    foo : ∀ b → 
            F B ~ b ~ l ~> A' →
            T⟨ sub B ⟩ (proj₁ b)
    foo b = take
      (a' , b=a') , desquash
      (a , b=a) ← provider (back (B=>'A)) b ,
      return ( a-b b (return (((proj₁ a) , (a'-a (proj₁ a , *) (return (a' , ( (BA≤AB  ■ AB≤A'A) ∨R ■ proj₁ lp ) ⅋ trans≡ (symm b=a) b=a')))) , deeper BA≤AB b=a)) )
      to prove (b ∈∈ sub B)   

  DecUnc : {A B : SubPtd (𝕏 j)} {p : j ≤ k} → Mono p → (j , A) =>'[ k ] (j , B) →  A ⊂ B
  DecUnc {p = p} mo me = to⊂ ((
    ROUNDTRIP
      _ , me  ∶
      refl=>'
    MOVECHILDREN  re  
      < intro⊂ mo ∷ 0=>'Sth >))
    (R∨ re) 
      
  module _ {B'' : SubPtd (𝕏 j)}  ((0k⇒B'' , p') : 𝟎 k ⇒[ k ] (j , B'')) where
    private
      p = convertEq p'
      q : j ≤ k
      q = right' (back (proj₁ 0k⇒B'')) ■  proj₂ p
    supIndOverTheRoof : {A P : SubEl}  {B : SubPtd (𝕏 j)}  →
        (A=>B : A =>' (j , B))
      → (A=>0k : A =>'[ k ] 𝟎 k)  
      → UNC A=>B  ≤ k

      → (B''=>P : (j , B'') =>' P)
      → A =>'[ UNC A=>B ∨ UNC B''=>P ] P
    --supporter INDUCTION over the roof has uncertainty A=>B ∨ B''=>P.
    supIndOverTheRoof A=>B A=>0k edge  B''=>P = 
     IncUncert'' bar (right-map (atLeast (back B''=>P) ∨R)) where
      bar : _ =>'[ UNC A=>B ∨ (UNC (0&0) ∨ UNC ( B''=>P)) ] _ -- 
      bar = 
        ROUNDTRIP
          A=>B
        JUMPBACK
          _ , A=>0k ∷ 0toB0 q ∶ 0&0 ∷ 0=>'Sth 
        MOVECHILDREN sup (edge) ( (UNCTrans (k , A=>0k) (0toB0 q) ■ R∨ re ) ),
        (IncUncert' (intro⊂ foo ∷ B''=>P) (UNCTrans (intro⊂ foo) B''=>P ■ left' (back (B''=>P)) ∨R)) where

        foo : ker (ϕ q) ⊂ B''
        foo = ⊂: λ x → (proj₂ (0k⇒B'')) (proj₁ x , * ) (return
          (pt ⟪ 0Sub {X = 𝕏 k}  ⟫ , deeper (proj₁ p)
            (symm (deeper (reflexivity ∨R)
              (trans≡ (symm (bwd refl (refl≡' (sym (proj₂ x))) ))
                      (deeper q (refl≡' refl)))))) )
        
    syntax supIndOverTheRoof 0k⇒B'' A=>B A=>0k edge B''=>P =
      ROUNDTRIP
        A=>B
      JUMPBACK
        A=>0k ∶
        0k⇒B'' ∶
        B''=>P , edge
    
    gobackwards :  {P : SubEl} {A : SubPtd (𝕏 j)}      
      → (A=>0k : (j , A) =>'[ k ] 𝟎 k)
      → (B''=>P : (j , B'') =>' P)
      → (j , A) =>'[ UNC (B''=>P) ] P
    gobackwards {P = P} {A = A} (A=>0k) = bar where
      foo : (B''=>P : (j , B'') =>' P)  → (j , A) =>'[ UNC (B''=>P) ] P
      foo B''=>P = IncUncert'' (
        supIndOverTheRoof
          refl=>'      
          A=>0k 
          q
          B''=>P )
        (left' (back B''=>P) ∨R) -- UNC of backwards is B''=>P.
      bar : (B''=>P : (j , B'') =>' P)  → (j , A) =>'[ UNC (B''=>P) ] P
      bar (j , SmartImplication.START p₁ ) = NOTHING (back (_ , foo (j , START p₁ )))
      bar (j , SmartImplication.END p₁ ) = END (provider' (back (_ , foo (j , END p₁))) )
      bar (j , SmartImplication.EQUAL p₁ ) = EQUAL (provider' (back (_ , foo (j , EQUAL p₁))) )
      bar (j , SmartImplication.NOTHING x ) = NOTHING (back (_ , foo (j , NOTHING x)))
    syntax gobackwards 0k⇒B'' A=>0k B''=>P  =
      BACKWARDS
        A=>0k ∶
        0k⇒B'' ∶
        B''=>P 

   -- first : {A B : SubEl}  {j : Carrier} → A ↗[ j ] B → A ⇒ B
   -- first (x §$ y §$ z) = x



