{-# OPTIONS --cubical #-}
-- open import Level
open import CubicalBasics.cubical-prelude hiding (_∨_  )
-- open import Data.Product
open import CubicalBasics.PointedTypesCubical
open import CubicalBasics.PropositionReasoning
open import CubicalBasics.IsomorphismCubical
fib : {A : Set ℓ} {B : Set ℓ'} → (A → B) → B → Set ( ℓ ⊔ ℓ' )
fib f b = Σ _ (λ a → f a ≡ b)
fibIsSet : {A : Set ℓ} {B : Set ℓ'} → isSet A → isSet B →  (f : A → B) → (b : B) →  isSet (fib f b)
fibIsSet isSetA isSetB f b = Σset isSetA λ a → isProp→isSet (isSetB _ _)
open Monad truncMonad
module _ {l}  {𝔸 : Ptd {l}} {𝔹 : Ptd {l}} (f : 𝔸 ⊙→ 𝔹) where

  src = U⊙ 𝔸
  trg = U⊙ 𝔹
  pushforward : SubPtd 𝔸 → SubPtd 𝔹
  pushforward A = (λ x → ∥ Σ[ a ∈ 【 A 】 ] (⟦ f ⟧ (proj₁ a) ≡ x)∥) ,  ∣ ( (pt 𝔸 , pt∈ A) , psv f) ∣₋₁
  pullback : SubPtd 𝔹 → SubPtd 𝔸
  pullback (B , b) = (λ x → B ( ⟦ f ⟧ x)) , subst (λ b → asType (B b)) (sym (psv f)) b
  functPush : {A A' : SubPtd 𝔸} → A ⊂ A' → pushforward A ⊂ pushforward A'
  functPush A⊂A' = ⊂: λ x →
    (a , pf) ← proj₂ x ,
    return (((proj₁ a) , (A⊂A' & a)) , pf)

  funcPull :   {A A' : SubPtd 𝔹} → A' ⊂ A → pullback A' ⊂ pullback A
  funcPull A'⊂A = ⊂: λ (a , pf) → A'⊂A & ((⟦ f ⟧ a) , pf)
  im : SubPtd 𝔹
  im = pushforward full --  (λ b →  ∥ Σ[ a ∈ src ] (⟦ f ⟧ a ≡ b) ∥  ) , ∣ ( pt 𝔸 , psv f) ∣₋₁
  pushIntoPshFWD : {A : SubPtd 𝔸} → 【 A 】 → 【 pushforward A 】
  pushIntoPshFWD (x , y) = (⟦ f ⟧ x) , ∣  ((x , y)) , refl ∣₋₁
  pushIntoImg : U⊙ 𝔸 → 【 im 】 
  pushIntoImg x = pushIntoPshFWD {A = full} (x , *) -- 
  ker : SubPtd 𝔸
  ker = pullback (0Sub) -- (λ x → ⟦ f ⟧ x ≡%  U⊙' 𝔹 % pt 𝔹) , (psv f)

  -- takePreIm : {b : B} {Q : Proposition {ℓ}} →  asType (⟨ im ⟩ b)   → (( Σ[ a ∈ A ] (⟦ f ⟧ a ≡ b) ) ≡> Q) → asType Q
  -- takePreIm z g = (z >>> g) --{! (λ z → (g (fst z))) !}
  surj : Type l
  surj =  full ⊂ im  -- [ b ∶ trg ]⇒ ⟨ im ⟩ b ----

  surjP : Proposition
  surjP = forallP (⟨ im ⟩)
  mono : Type l
  mono = ker ⊂ 0Sub
  

module _ {l}  {𝔸 : Ptd {l}} {𝔹 : Ptd {l}} {ℂ : Ptd {l}} {f : 𝔸 ⊙→ 𝔹} {g : 𝔹 ⊙→ ℂ} where
  surjComp  :  surj g → surj f → surj (g ⊙∘ f)
  surjComp isSurjG isSurjF = ⊂: λ x →
    y ← isSurjG &  x ,
    z ← isSurjF & ((proj₁ (proj₁ y)) , *) ,
    return ((proj₁ z) , (cong ⟦ g ⟧ (proj₂ z)  ∙ proj₂ y) )
  ezFactor : (A : SubPtd 𝔸) → pushforward f A ⊂ pullback g (pushforward (g ⊙∘ f) A)
  ezFactor A = ⊂: (λ x →
    (a , pf) ← proj₂ x ,
    return (a , cong ⟦ g ⟧ pf)
    )


