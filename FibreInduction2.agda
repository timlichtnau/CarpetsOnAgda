{-# OPTIONS --with-K #-}
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import PointedTypes2


module FibreInduction2 where
open  Ptd
open _⊙→_
open import Basics
open ≡-Reasoning
open import Function
hasSection : {X Y : Set} → (f : X → Y) → Set
hasSection {X} {Y} f = Σ[ g ∈ (Y → X) ] ((y : Y) → f (g y) ≡ y)
fib : {X Y : Set} → (f : X → Y) → Y → Set
fib {X} {Y} f y = Σ[ x ∈ X ] (f x ≡ y)
$_$ : {X Y : Set} {f : X → Y} → (x : X) → fib f (f x)
$ x $ = (x , refl)

module _ {X : Set} (Y : X → Set) where
  section = (x : X) → Y x
  eva : (x' : X) → section → Y x'
  eva x' f = f x'
  ExtProp = (x : X) → hasSection (eva x)

ext : {X : Set} → {Y : X → Set}  {x' : X} → ExtProp Y → Y x' → section Y
ext {x' = x'} ep = proj₁ (ep x')
module FibInd {P : Set} {B : Set} {A : Set} (f : P → B) (g : B → A) where
  Y : {a : A} → fib g a → Set
  Y b = fib f (proj₁ b)

  localSectionThroughPoint : P → Set
  localSectionThroughPoint p = fib (eva Y $ f p $) $ p $ -- ExtProp' Y (λ p → $ f p $) 
  SEP : Set
  SEP = section localSectionThroughPoint -- section (λ a → ExtProp (Y {a}))

  postulate  FIBRE-IND : ExtProp localSectionThroughPoint


  
  getSepByPoint : {p : P} →  localSectionThroughPoint p → SEP
  getSepByPoint lsectionThroughp = ext FIBRE-IND lsectionThroughp
  someLocalSection : (b : B) → (s : section (Y {g b})) → localSectionThroughPoint (proj₁ (s $ b $))
  someLocalSection b s = (λ x → s (proj₁ x , proj₂ x ∙ ap g (proj₂ (s $ b $)))) , dpair-≡ (ap (proj₁ ∘ s) (dpair-≡ (proj₂ (s $ b $)) (tp-resp-ap g (proj₂ (s $ b $)))))
    ((test {proj₁ (s $ b $)} {proj₂ (s $ b $)}) ∙ ∙-inv-r ( proj₂ (s $ b $))) where
    _∙_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c    
    refl ∙ p = p
    ∙-unit-r : {A : Set} {a b : A} → (p : a ≡ b) → p ∙ refl ≡ p
    ∙-unit-r refl = refl
    ∙-inv-r : {A : Set} {a b : A} → (p : a ≡ b) → p ∙ (sym p) ≡ refl
    ∙-inv-r refl = refl
    tp-resp-ap  : {A B : Set} (g : A → B) {a x : A} → (p : x ≡ a) → tp (λ x → g x ≡ g a) p (ap g p) ≡ refl
    tp-resp-ap g refl = refl

    test : {sb1 : P}  {sb2 : f (sb1) ≡ b} → tp (λ x → f x ≡ f (sb1))
             (ap (λ x → proj₁ (s x))
              (dpair-≡ ( sb2) (tp-resp-ap g (sb2))))
             (proj₂
              (s
               (f (sb1) ,
                (ap g (sb2)))))
             ≡ (proj₂ (s $ b $) ∙ sym (sb2))
    test {sb2 = refl} = sym (∙-unit-r (proj₂ (s $ f _ $)))
  getSEP : (b : B) → (s : section (Y {g b})) → SEP
  getSEP b s = getSepByPoint (someLocalSection b s)

Ex2 : {𝔸 𝔹 : Ptd} {a : U⊙ 𝔸} → (g : 𝔹 ⊙→ 𝔸) → (f' : U⊙ 𝔹 → Set)
    → ((b : fib ⟦ g ⟧ (pt 𝔸)) → f' (proj₁ b))
    → Σ[ b ∈ fib ⟦ g ⟧ a ] (f' (proj₁ b))
    →  ((b : fib ⟦ g ⟧ a) → f' (proj₁ b))
  
Ex2 {𝔸 = 𝔸} {𝔹 = 𝔹} {a = a*} pg f' ker (b' , fb') b = foo where
  B = (U⊙ 𝔹)
  A = U⊙ 𝔸
  P = Σ B f'
  getPInfo : (p : P) → f' (proj₁ p)
  getPInfo = proj₂ 
  f : P → B
  f = proj₁
  g : B → A
  g = ⟦ pg ⟧
  open FibInd f g
  sep : SEP 
  sep = getSEP (pt 𝔹) λ x → $ (  proj₁ x ,  ker ((proj₁ x) , (proj₂ x ■ psv pg))) $
  bar : localSectionThroughPoint (proj₁ b' , fb')
  bar = sep (( proj₁ b') , fb') 
  myb = proj₁ bar (proj₁ b , proj₂ b ■ sym (proj₂ b'))
  foo : f' (proj₁ b)
  foo = tp f' (proj₂ myb) (proj₂ (proj₁ (myb)))
