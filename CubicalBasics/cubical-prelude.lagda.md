This file contains whatever is needed from the agda/cubical library to
get the lectures to typecheck. Warning: it is not very organized or
documented.

```agda
{-# OPTIONS --cubical --without-K --safe #-}

module CubicalBasics.cubical-prelude where
-- open import Relation.Binary.Structures public
open import Agda.Builtin.Cubical.Path public
open import Agda.Primitive renaming (lsuc to suc) public
open import Cubical.Relation.Binary
open import Agda.Builtin.Equality renaming (_≡_ to _≡'_ ; refl to refl') public
-- open import Cubical.Data.Prod using (proj₁ ; proj₂ )
open import Cubical.Data.Sigma public renaming (fst to proj₁ ; snd to proj₂)
open import Agda.Builtin.Cubical.Sub public
  renaming ( 
           primSubOut to outS
           )
open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )


open import Agda.Builtin.Cubical.Glue public
  using ( isEquiv       -- ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ ⊔ ℓ')

        ; equiv-proof   -- ∀ (y : B) → isContr (fiber f y)

        ; _≃_           -- ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ ⊔ ℓ')

        ; equivFun      -- ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → A → B

        ; equivProof    -- ∀ {ℓ ℓ'} (T : Type ℓ) (A : Type ℓ') (w : T ≃ A) (a : A) φ →
                        -- Partial φ (fiber (equivFun w) a) → fiber (equivFun w) a

        ; primGlue      -- ∀ {ℓ ℓ'} (A : Type ℓ) {φ : I} (T : Partial φ (Type ℓ'))
                        -- → (e : PartialP φ (λ o → T o ≃ A)) → Type ℓ'

        ; prim^unglue   -- ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I} {T : Partial φ (Type ℓ')}
                        -- → {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A

        -- The ∀ operation on I. This is commented out as it is not currently used for anything
        -- ; primFaceForall -- (I → I) → I
        )
  renaming ( prim^glue   to glue         -- ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I} {T : Partial φ (Type ℓ')}
                                         -- → {e : PartialP φ (λ o → T o ≃ A)}
                                         -- → PartialP φ T → A → primGlue A T e
           )

open import Agda.Primitive public
  using    ( Level
           ; SSet
           ; lzero
           ; lsuc
           ; _⊔_ )
  renaming ( Set to Type )

-- We parametrize everything by some universe levels
variable
  ℓ ℓ' ℓ'' : Level

-- Non dependent path types



-- PathP (λ i → A) x y gets printed as x ≡ y when A does not mention i.
--  _≡_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
--  _≡_ {A = A} = PathP (λ _ → A)

-- Path composition
_∙_ : {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_∙_ {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
                                   ; (i = i1) → q j })
                          (p i)
_::_::_ : {A : Type ℓ} {x y z w : A} → x ≡ y → y ≡ z → z ≡ w → x ≡ w
_::_::_ {x = x} p q r i =  hcomp (λ j → λ { (i = i0) → p (~ j)
                                   ; (i = i1) → r j })
                          (q i)

sym : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym p i = p (~ i)
infixr 30 _∙_


invEquiv : {A : Type ℓ} {B : Type ℓ'} {f : A → B} → (isEquiv f) → B → A
invEquiv p b = proj₁ (proj₁ ((equiv-proof p b))) 


--- Homogeneous filling

refl : {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} i = x
≡isEq : {A : Type ℓ} → BinaryRelation.isEquivRel {A = A} _≡_
≡isEq =  record { reflexive = λ a →  refl ; symmetric = λ _ _ p → sym p  ; transitive = λ a b c p q → p ∙  q  } --_∙_
cong : {A : Type ℓ} {B : Type ℓ'} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f p i = f (p i)
syntax cong f p   = f ←[ p ]
-- syntax cong f p = f ←[ p ]
apf : {A : Type ℓ} {B : A → Type ℓ'} {x y : A} (f : (a : A) → B a) → (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
apf f p = λ i → f (p i)
-- Use built in Σ types to avoid problems with the imported Cubical
-- Agda operations that use Σ types


isContr : Type ℓ → Type ℓ
isContr A = Σ A (λ x → ((y : A) → x ≡ y))

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)
Glue : (A : Type ℓ) {φ : I}
       → (Te : Partial φ (Σ (Type ℓ') (_≃ A)))
       → Type ℓ'
Glue A Te = primGlue A (λ x → Te x .proj₁) (λ x → Te x .proj₂)

funExt₂ : {A : Type ℓ} {B : A → Type} {C : (x : A) → B x → I → Type}
          {f : (x : A) → (y : B x) → C x y i0}
          {g : (x : A) → (y : B x) → C x y i1}
          → ((x : A) (y : B x) → PathP (C x y) (f x y) (g x y))
          → PathP (λ i → ∀ x y → C x y i) f g
funExt₂ p i x y = p x y i

--syntax thenSyntax x (λ y →  z → f y)) g = take y ∶ x such that z - Consider f to prove g
-- _≅_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
-- A ≅ B = Σ (A → B) \ f → Σ (B → A) \ g → ((z : B) → (f (g z) ≡ z)) × ( ∀ z → g (f z) ≡ z )
subst : {A : Type ℓ} (B : A → Type ℓ') {x y : A} → x ≡ y → B x → B y
subst B p = transp (λ i → B (p i)) i0
substRefl : {A : Type ℓ} (B : A → Type ℓ') {x : A} → (a : B x) → subst B refl a ≡ a
substRefl B {x = x} a i = transp (λ j → B x) i a
{--
substComposite : ∀ {ℓ ℓ'} {A : Type ℓ} → (B : A → Type ℓ')
                 → {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : B x)
                 → subst B (p ∙ q) u ≡ subst B q (subst B p u)

--}
-- subst-distrib-∙ : {A : Type ℓ} (B : A → Type ℓ') {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → (a : B x) → subst B (p ∙ q) a ≡ subst B q (subst B p a)
-- subst-distrib-∙ B p q a  = {!!}
transport : {A B : Type ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

transpFill : ∀ {ℓ} {A : Type ℓ}
             (φ : I)
             (A : (i : I) → Type ℓ [ φ ↦ (λ _ → A) ])
             (u0 : outS (A i0))
           → --------------------------------------
             PathP (λ i → outS (A i)) u0 (transp (λ i → outS (A i)) φ u0)
transpFill φ A u0 i = transp (λ j → outS (A (i ∧ j))) (~ i ∨ φ) u0
{--
transport-fillerExt : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
                    → PathP (λ i → A → p i) (λ x → x) (transport p)
transport-fillerExt p i x = transpFill i0 (λ i₁ → {!p i₁!}) x i -- transport-filler p x i
substComposite B {z = z} p q Bx i =
  transport (cong B (compPath-filler' i)) (transport-fillerExt (cong B p) i Bx) where 
            compPath-filler' : PathP (λ j → p j ≡ z) (p ∙ q) q
            compPath-filler' j = hfill {!(λ k → λ { (j = i0) → ? ; (j = i1) → ? })!} {!!} j
--}            
fromPathP : {A : I → Type ℓ} {x : A i0} {y : A i1} →
  PathP A x y → transport (λ i → A i) x ≡ y
fromPathP {A = A} p i = transp (λ j → A (i ∨ j)) i (p i)
toPathP : {A : I → Type ℓ} {x : A i0} {y : A i1} →
  transport (λ i → A i) x ≡ y → PathP A x y
toPathP {A = A} {x = x} p i =
  hcomp
    (λ {j (i = i0) → x ;
        j (i = i1) → p j })
   ( transp (λ k → A (i ∧ k)) (~ i) x)
isProp→PathP : {A : I → Type ℓ} (p : (i : I) → isProp (A i))
  (a₀ : A i0) (a₁ : A i1) → PathP A a₀ a₁
isProp→PathP {A = A} p a₀ a₁ = toPathP λ i → p i1 (transport (λ i → A i) a₀) a₁ i

Σmap : {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''} → ((a : A) → B a → C a) → Σ A B → Σ A C
Σmap f (a , b) = (a , f a b)

Sets : (o : Level) → Set (lsuc o)
Sets o = Σ (Set o) isSet

_∼_ : {A : Set ℓ} {B : Set ℓ'} → (f g : A → B) → Type (ℓ ⊔ ℓ')
f ∼ g = (x : _) → f x ≡ g x
module _ {A : Type ℓ} where

  singl : (a : A) → Type ℓ
  singl  a = Σ A (a ≡_)



  isContrSingl : (x : A) → isContr (singl x)
  isContrSingl x = ctr , prf
    where
    -- The center is just a pair with x and refl
    ctr : singl x
    ctr = x , refl

    -- We then need to prove that ctr is equal to any element s : singl x.
    -- This is an equality in a Σ-type, so the first component is a path
    -- and the second is a path over the path we pick as first argument,
    -- i.e. the second component is a square. In fact, we need a square
    -- relating refl and pax over a path between refl and pax, so we can
    -- use an _∧_ connection.
    prf : (s : singl x) → ctr ≡ s
    prf (y , pax) i = (pax i) , λ j → pax (i ∧ j)


  Jrule :  {x : A} {o : Level} 
      (P : (y : A) → x ≡ y → Type o)
      (d : P x refl)
      {y : A}
      (p : x ≡ y)
      →
      P y p


  Jrule  {x = x} P d p = subst (λ X → P (proj₁ X) (proj₂ X)) ((lem .proj₂ (_ , p)) ) d
    where
    lem : isContr (Σ A (x ≡_))
    lem = isContrSingl x
  JRefl : {x : A} (P : (z : A) → x ≡ z → Type ℓ'')
    (d : P x refl) → Jrule P d refl ≡ d
  JRefl {x = x} P d i = transp (λ _ → P x (λ _ → x)) i d
module _ {A : Type ℓ} where
  comp-filler : {x y z : A} (p : x ≡ y) (q : y ≡ z)
              → PathP (λ j → refl {x = x} j ≡ q j) p (p ∙ q)
  comp-filler {x = x} p q j i = hfill (λ k → λ { (i = i0) → x
                                                ; (i = i1) → q k })
                                      (inS (p i)) j
                                   
  comp∷filler : {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → PathP (λ i → p (~ i) ≡ r i) q (p :: q :: r)
  comp∷filler p q r j i =  hfill (λ j → λ { (i = i0) → p (~ j)
                                     ; (i = i1) → r j })
                            (inS (q i)) j

  lUnit : {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
  lUnit {x = x} {y = y} p i j =
    hcomp (λ k → λ {(i = i0) → comp-filler refl p k j
                   ; (i = i1) → p (k ∧ j)
                   ; (j = i0) → x
                   ; (j = i1) → p k})
          x



  rUnit : {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
  rUnit {x = x} {y = y} p i j =
    hcomp (λ k → λ {(i = i0) → comp-filler p refl k j
                   ; (i = i1) → p j
                   ; (j = i0) → x
                   ; (j = i1) → y})
          (p j)
  lInv : {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
  lInv {x = x} {y = y} p i j = hcomp (λ k → λ {
      (i = i0) → comp-filler p (sym p) k j
    ; (i = i1) → x
    ; (j = i0) → x
    ; (j = i1) → (sym p) (k ∨ i) } ) (p (j ∧ (~ i))) 

  comp-filler' : {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → PathP (λ j → sym p j ≡ r j) q (p ∙ (q ∙ r))
  comp-filler' {y = y} p q r i j = hcomp ((λ k → λ { (i = i0) → help j k ; (i = i1) → comp-filler p (q ∙ r) k j ; (j = i0) → p (k ∧ ~ i) ; (j = i1) → comp-filler q r i k })) (p j)  where
    help' : PathP (λ i' → sym p i' ≡ y) refl p
    help' j i' = p (i' ∨ ~ j)
    help : PathP (λ k → p k ≡ q k) p q
    help j k = hcomp ((λ l → λ { (k = i0) →  help' l j ; (k = i1) → q (j ∧ l) ; (j = i0) → help' l k ; (j = i1) → q (l ∧ k) })) y
assoc : {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
assoc {x = x} {y = y} p q r i j =
  hcomp (λ k → λ {(i = i0) → (p ∙ comp-filler q r k) j
                 ; (i = i1) → comp-filler (p ∙ q) r k j
                 ; (j = i0) → x
                 ; (j = i1) → r k})
        ((p ∙ q) j)

-- hCompIsUnique :  ∀ {ℓ} {A : Set ℓ} {φ : I} (u : ∀ i → Partial φ A) → (i : I) → (p q : Partial φ A) → (Partial (~ i) (p ≡ q)) → Partial i (p ≡ q)
-- hCompIsUnique u i p q x = {!!}
-- hfill : {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (u0 : A [ φ ↦ u i0 ]) (i : I) → A
congPres∷ : {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) {B : Type ℓ'} (f : A → B) → cong f (p :: q :: r) ≡ cong f p :: cong f q :: cong f r
congPres∷ {A = A} p q r f i j = hcomp (λ k → λ { (i = i0) → f (comp∷filler p q r k j) ; (i = i1) → comp∷filler (cf p) (cf q) (cf r) k j ; (j = i0) → cong f (sym p) k ; (j = i1) → cong f r k}) (cf q j) where
    cf : {a b : A} → a ≡ b → f a ≡ f b
    cf = cong f
-- hComp∙≡ : {A : I → Type ℓ} →  (p q base : (i : I) → A i) → (h : (i : I ) → p i ≡ q i) → (l : base i0 ≡ p i0) → (r : base i
module _ where
  idEquiv : ∀ {ℓ} (A : Type ℓ) → A ≃ A
  idEquiv A .proj₁ = λ x → x
  equiv-proof (idEquiv A .proj₂) = λ y → (y , (λ i → y)) , (λ h i → (h .proj₂ (~ i)) , λ j → h .proj₂ ((j ∨ ~ i)))

  private variable
    A B : Type ℓ

  isEquivTransport : {A B : Type ℓ} (p : A ≡ B) → isEquiv (transport p)
  isEquivTransport p =  transport (λ i → isEquiv (transp (λ j → p (i ∧ j)) (~ i))) (idEquiv _ .proj₂)
  transportRefl : (x : A) → transport refl x ≡ x
  transportRefl {A = A} x i = transp (λ _ → A) i x
  ua : {A B : Type ℓ}  → A ≃ B → A ≡ B
  ua {A = A} {B = B} e i = Glue B (λ { (i = i0) → (A , e)
                                   ; (i = i1) → (B , idEquiv B) })
  uaβ : (e : A ≃ B) (x : A) → transport (ua e) x ≡ proj₁ e x
  uaβ e x = transportRefl (equivFun e x)

  substEquiv : (S : Type ℓ → Type ℓ') (e : A ≃ B) → S A → S B
  substEquiv S e = subst S (ua e)
  substEquiv≃ : (S : Type ℓ → Type ℓ') (e : A ≃ B) → S A ≃ S B
  substEquiv≃ S e = (substEquiv S e) , (isEquivTransport (cong S (ua e)))
data 𝟏 {l : Level } : Set l where
      * : 𝟏
id  :  {A : Type ℓ} →  A → A
id x = x

_∘_ : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)
