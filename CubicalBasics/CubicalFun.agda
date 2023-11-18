{-# OPTIONS --cubical --without-K #-}
open import CubicalBasics.cubical-prelude
open import Data.Product
open import CubicalBasics.IsomorphismCubical
open import Function.Base
module CubicalBasics.CubicalFun where
{--
transportRelation : {A B : Type ℓ} {C : Type ℓ'}  → (P : A ≡ B) → (f1 : A → C) → (f2 : B → C) → transport (λ i → P i → C) f1 ≡ f2 → PathP (λ i → (P i → C)) f1 f2
transportRelation {ℓ = ℓ} { C = C} p f1 f2 pf i =  toPathP {A = λ i → (p i → C) }{x = f1} pf i where --try (λ j → (p (~ (i ∧ j)))) f2 --(λ j a → pf a j ) -- (λ a → f1 (transport (sym P) a))

  try : {A B : Type ℓ} {C : Type ℓ'} → A ≡ B → (A → C) → B  → C
  try {C = C} p f =  subst (λ X → (X → C)) p f
  --}
transportRelation : {A B : Type ℓ}  {C : Type ℓ'}  → (ψ : A ≃ B) → (f1 : A × A → C) → (f2 : B × B → C) → ((a a' : A) →
  f2 ( proj₁ ψ a , proj₁ ψ a') ≡ f1 (a , a')) → PathP (λ i → (ua ψ i × ua ψ i) → C) f1 f2
transportRelation {A = A} {B = B} ψ f1 f2 pipi = {!!} where
  P' : (A × A) ≡ (B × B)
  P' =  cong (λ A → A × A) (ua ψ)
 
  ψ' : (A × A) ≃ (B × B)
  ψ' = substEquiv≃ (λ A → A × A) ψ
  pipi' : f2 ∘ proj₁ ψ' ≡ f1
  pipi' i (a , b) = {!pipi a b i!}
--  ψ' = (λ (a , b) → (ψ a , ψ b) ) , record { equiv-proof = λ (b , b') → {!!} } --}

module _  {A B : Type ℓ} {C : Type ℓ'}  (ψ : A ≃ B)  where
  P : A ≡ B
  P = ua ψ 
  wow : PathP (λ i → P i → B) (transport P) id
  wow i = transp (λ j → P (i ∨ j)) i
  wcomp : ∀  {A : I → Type ℓ'} {f} {g} {h} →  PathP (λ v → A v) g h → f ≡ h → PathP (λ v → A v) {!!} h
  wcomp {g = g} wow we i = {! hcomp (λ j → λ { (i = i0) → ?  ; (i = i1) → g }) (wow i)!} --(we a j)
  wow' : (f : B → C) → PathP (λ v → P v → C) (f ∘ proj₁ ψ) f
  wow' f i = f ∘ {! wcomp wow {!(uaβ ψ)!} !}
 {-- wow : (f : A → C) → PathP (λ v →  P v → C) f (f ∘ ϕ)
  ϕ : B → A
  ϕ = transport (sym P)
  Th1 : (A → C) → (B → C)
  Th1 = (transport (λ i → P i → C))
  Th2 : (A → C) → (B → C)
  Th2 =  (_∘ ϕ)                        
  wow f = λ i → f ∘  transp (λ j → P (i ∧ (~ j))) (~ i) 
  BigThm : Th1 ≡ Th2
  BigThm i f = fromPathP (wow f)  i
--}
