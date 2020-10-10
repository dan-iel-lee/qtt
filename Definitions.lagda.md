
## Yay

```
{-# OPTIONS --allow-unsolved-metas #-}

open import QTT.POSemiring using (POSemiring)

module QTT.Definitions {R : Set} {{mod : POSemiring R}} where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym) renaming (subst to subs≡)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Relation.Nullary using (¬_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat
open import Data.Nat.Properties using (+-comm; +-assoc; +-identity; *-assoc; *-identity; *-zero; ≤-reflexive; ≤-antisym; ≤-trans)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax; _,_) 
open import Data.String using (String)
open import Data.List using (List; map; []; _∷_; zip; length) renaming (_++_ to _<>'_)
open import Function using (_∘_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Empty


_*'_ = POSemiring._*'_ mod
_+'_ = POSemiring._+'_ mod
zero' = POSemiring.zero' mod
one' = POSemiring.one' mod

infixl 30 _*'_
infixl 29 _+'_

*'-zero = POSemiring.*-zero' mod
*'-identity = POSemiring.*-identity' mod
+'-identity = POSemiring.+-identity' mod
+'-comm = POSemiring.+-comm' mod
+'-assoc = POSemiring.+-assoc' mod

```

## Basic definitions

### Types

```

data Type : Set₁ where
  Unit : Type
  _-⟨_⟩→_ : Type → R → Type → Type
  [_]_ : R → Type → Type
  _⊗_ : Type → Type → Type
  _⊕_ : Type → Type → Type

infix 19 [_]_
infix 18 _-⟨_⟩→_
infix 22 _⊗_
infix 21 _⊕_

```

### Typing Contexts
```

-- typing context indexed by a list of context elements
data Context : (List Type) → Set₁ where
  Ø : Context []
  _,:⟨_⟩_ : {Δ : List Type} →
                  Context Δ → R → ∀ (A : Type) → Context ( A ∷ Δ )
infixl 8 _,:⟨_⟩_

-- inductive definition of an empty context
data CEmpty : ∀ {Δ : List Type} → Context Δ → Set where
  Ø-empty : CEmpty Ø
  ,-empty : ∀ {Δ : List Type} {Γ₁ : Context Δ} {A : Type}
            → CEmpty Γ₁
            ---------
            → CEmpty (Γ₁ ,:⟨ zero' ⟩ A)


-- context scaling
_**_ : {Δ : List Type} → R → Context Δ → Context Δ
infix 10 _**_
_ ** Ø = Ø
a ** (Γ ,:⟨ q ⟩ A)  =  (a ** Γ) ,:⟨ a *' q ⟩ A

-- context addition
_++_ : {Δ : List Type} → (Γ₁ : Context Δ) → (Γ₂ : Context Δ) → Context Δ
infix 9 _++_
Ø ++ Ø = Ø
(Γ₁ ,:⟨ q1 ⟩ A)  ++ (Γ₂ ,:⟨ q2 ⟩ .A)  =  (Γ₁ ++ Γ₂) ,:⟨ q1 +' q2 ⟩ A

-- context concat
_<>_ : {Δ₁ Δ₂ : List Type} → (Γ₂ : Context Δ₂) → (Γ₁ : Context Δ₁) → Context (Δ₁ <>' Δ₂)
infixl 7 _<>_
b <> Ø = b
b <> (a ,:⟨ x ⟩ A) = (b <> a) ,:⟨ x ⟩ A


```

### Terms
```
-- LOOKUP - used for variable definition
data _∋_ : ∀ {Δ} → Context Δ → Type → Set₁ where

  Z : ∀ {Δ} {Γ : Context Δ} {A}
        → CEmpty Γ
          -------
        → (Γ ,:⟨ one' ⟩ A) ∋ A

  S_ : ∀ {Δ} {Γ : Context Δ} {A B}
      → Γ ∋ A
        -------- 
      → (Γ ,:⟨ zero' ⟩ B) ∋ A

infix 5 _∋_


-- inductive definition of terms with intrinsic typing
data _⊢_ : ∀ {Δ} (Γ : Context Δ) → Type → Set₁
infix 2 _⊢_

data _⊢_ where
  --
  `_ : ∀ {Δ} {Γ : Context Δ}  {A}
      → Γ ∋ A
        -----
      → Γ ⊢ A

  ƛ:⟨_⟩_⇒_ : ∀ {Δ} {Γ : Context Δ} {B}
            → (q : R)
            → (A : Type)
            → Γ ,:⟨ q ⟩ A ⊢ B
              -----------
            → Γ ⊢ A -⟨ q ⟩→ B

  appP : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A B θ q}
        → θ ≡ q ** Γ₂ ++ Γ₁
        → Γ₁ ⊢ A -⟨ q ⟩→ B
        → Γ₂ ⊢ A
        → θ ⊢ B

  unitP : ∀ {Δ} {Γ : Context Δ} -- changed to allow zeroed out context
          → CEmpty Γ
          → Γ ⊢ Unit

  unitElimP : ∀ {Δ} {A θ} {Γ₁ Γ₂ : Context Δ}
                  → θ ≡ Γ₁ ++ Γ₂
                  → Γ₁ ⊢ Unit
                  → Γ₂ ⊢ A
                  → θ ⊢ A

  boxP : ∀ {Δ} {Γ θ : Context Δ} {A} (q : R)
          → θ ≡ q ** Γ
          → Γ ⊢ A
          → θ ⊢ [ q ] A

  -- interesting case
  boxElimP : ∀ {Δ} {Γ₁ Γ₂ θ : Context Δ} {q A B}
                → θ ≡ Γ₁ ++ Γ₂
                → Γ₁ ⊢ [ q ] A
                → Γ₂ ,:⟨ q ⟩ A ⊢ B
                → θ ⊢ B

  pairP : ∀ {Δ} {Γ₁ Γ₂ θ : Context Δ} {A B}
        → θ ≡ Γ₁ ++ Γ₂
        → Γ₁ ⊢ A
        → Γ₂ ⊢ B
          ------
        → θ ⊢ A ⊗ B

  pairElimP : ∀ {Δ} {Γ₁ Γ₂ θ : Context Δ} {A₁ A₂ B}
            → θ ≡ Γ₁ ++ Γ₂
            → Γ₁ ⊢ A₁ ⊗ A₂
            → Γ₂ ,:⟨ one' ⟩ A₁ ,:⟨ one' ⟩ A₂ ⊢ B
              ------------
            → θ ⊢ B

  -- had to make non mixfix to allow specifying implicit argument
  inj₁ : ∀ {Δ} {Γ : Context Δ} {A B}
        → Γ ⊢ A
          -----
        → Γ ⊢ A ⊕ B

  inj₂ : ∀ {Δ} {Γ : Context Δ} {A B}
        → Γ ⊢ B
          ------
        → Γ ⊢ A ⊕ B

  sumElimP : ∀ {Δ} {Γ₁ Γ₂ θ : Context Δ} {A₁ A₂ B}
            → (q : R)
            → θ ≡ q ** Γ₁ ++ Γ₂
            → Γ₁ ⊢ A₁ ⊕ A₂
            → Γ₂ ⊢ A₁ -⟨ q ⟩→ B
            → Γ₂ ⊢ A₂ -⟨ q ⟩→ B
              ---------
            → θ ⊢ B

infix 25 `_

{-
  -- needed to refactor some terms to have proofs passed in (for subst)
  -- but step relation doesn't require these proofs
  _·_ : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A B q}
      → Γ₁ ⊢ A -⟨ q ⟩→ B
      → Γ₂ ⊢ A
        ------
      → q ** Γ₂ ++ Γ₁ ⊢ B
  a · b = appP refl a b

  unit : ∀ {Δ} {Γ : Context Δ}
       → (zero' ** Γ) ⊢ Unit
  unit {Γ = Γ} = unitP (zero' ** Γ) refl

  let-unit≔_in'_ : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A}
                 → Γ₁ ⊢ Unit
                 → Γ₂ ⊢ A
                   -------
                 → (Γ₁ ++ Γ₂) ⊢ A
  let-unit≔ u in' a = unitElimP refl u a
  
  box⟨_⟩_ : ∀ {Δ} {Γ : Context Δ} {A} (q : R)
          → Γ ⊢ A
          → (q ** Γ) ⊢ [ q ] A
  box⟨ q ⟩ a = boxP q refl a

  let-box≔_in'_ : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {q A B}
                → Γ₁ ⊢ [ q ] A
                → Γ₂ ,:⟨ q ⟩ A ⊢ B
                → Γ₁ ++ Γ₂ ⊢ B
  let-box≔ b in' a = boxElimP refl b a

  ⟨_,_⟩ : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A B}
        → Γ₁ ⊢ A
        → Γ₂ ⊢ B
          ------
        → Γ₁ ++ Γ₂ ⊢ A ⊗ B
  ⟨ a , b ⟩ = pairP refl a b

  let⟨,⟩≔_in'_ : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A₁ A₂ B}
               → Γ₁ ⊢ A₁ ⊗ A₂
               → Γ₂ ,:⟨ one' ⟩ A₁ ,:⟨ one' ⟩ A₂ ⊢ B
                 ------------
               → Γ₁ ++ Γ₂ ⊢ B
  let⟨,⟩≔ p in' b = pairElimP refl p b

  case⟨_⟩_of_||_ : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A₁ A₂ B}
                 → (q : R)
                 → Γ₁ ⊢ A₁ ⊕ A₂
                 → Γ₂ ⊢ A₁ -⟨ q ⟩→ B
                 → Γ₂ ⊢ A₂ -⟨ q ⟩→ B
                   ---------
                 → (q ** Γ₁ ++ Γ₂) ⊢ B
  case⟨ q ⟩ s of f || g = sumElimP q refl s f g

  infixl 21 _·_
  infix 23 box⟨_⟩_
  infix 22 let-unit≔_in'_
  infix 22 let-box≔_in'_
  infix 22 let⟨,⟩≔_in'_
  infix 22 case⟨_⟩_of_||_

-}

```

### Definition properties
```



-- context inductive relations
data _≈_**_++_ : ∀ {Δ : List Type} → Context Δ → R → Context Δ → Context Δ → Set where
  CArith-Emp : ∀ {Δ} {Γ Γ₁ : Context Δ} {q}
             → CEmpty Γ₁ ⊎ q ≡ zero'
             → Γ ≈ q ** Γ₁ ++ Γ

  CArith-, : ∀ {Δ} {Θ Γ₁ Γ₂ : Context Δ} {A q₁ q₂ q q'}
           → (Θ ≈ q ** Γ₁ ++ Γ₂)
           → (q' ≡ q *' q₁ +' q₂)
           → (Θ ,:⟨ q' ⟩ A) ≈ q ** (Γ₁ ,:⟨ q₁ ⟩ A) ++ (Γ₂ ,:⟨ q₂ ⟩ A)

-- data _≈_!+_ : ListType → List Type → Type → Set
--   LIns-Nil : 

data _≈_*_#_ : ∀ {Δ₁ Δ₂ : List Type} → Context Δ₂ → R → Context Δ₂ → Context Δ₁ → Set₁ where
  CSurr-Z : ∀ {Δ} {Γ Γ₁ : Context Δ} {q A}
          → CEmpty Γ₁ ⊎ q ≡ zero'
          → (Γ ,:⟨ q ⟩ A) ≈ q * Γ₁ ,:⟨ one' ⟩ A # Γ

  CSurr-S : ∀ {Δ₁ Δ₂} {q q' B} {Γ Γ₁ : Context Δ₁} {Γ₂ : Context Δ₂}
          → Γ ≈ q * Γ₁ # Γ₂
          → (Γ ,:⟨ q' ⟩ B) ≈ q * (Γ₁ ,:⟨ zero' ⟩ B) # (Γ₂ ,:⟨ q' ⟩ B)

zero-like : R → Set
zero-like x = ∀ {y : R} → x *' y ≡ zero'

one-like : R → Set
one-like x = ∀ {y : R} → x *' y ≡ y







postulate
  -- in the var case, want to be able to say either q is zero (meaning the vars don't match) or q is one (meaning the vars match)
  var-help : ∀ {Δ Δ₁} {Γ₁ Ω₁ : Context Δ₁} {Ω : Context Δ} {A B q} → (Γ₁ ∋ A) → (Ω₁ ≈ q * Γ₁ # Ω) → (Ω₁ ∋ B)
           → q ≡ zero' ⊎ (q ≡ one' × CEmpty Ω)
  **++-eq : ∀ {Δ} {Γ₂ Ω₂ Ω : Context Δ} {q} → (Ω₂ ≈ q ** Γ₂ ++ Ω) → (q ≡ one') → CEmpty Ω → Γ₂ ≡ Ω₂
  **#-eq : ∀ {Δ Δ₁} {Γ₂ Ω₂ : Context Δ} {Ω : Context Δ₁} {q} → (Ω₂ ≈ q * Γ₂ # Ω) → (q ≡ one') → CEmpty Ω → Γ₂ ≡ Ω₂
  cont-exc : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A} → Γ₁ ≡ Γ₂ → Γ₁ ⊢ A → Γ₂ ⊢ A -- is there a better way to say this? use subst?
  type-exc : ∀ {Δ} {Γ : Context Δ} {A B} → A ≡ B → Γ ⊢ A → Γ ⊢ B

  zero-ctx-eq : ∀ {Δ Δ₁} {Ω Ω₂ : Context Δ} {Ω₁ : Context Δ₁} {Γ₁ Γ₂ A} → Ω₂ ≈ zero' ** Γ₂ ++ Ω → Ω₁ ≈ zero' * Γ₁ # Ω → Ω₁ ∋ A → Ω₂ ∋ A

  
  cont-type-exc : ∀ {Δ} {Γ : Context Δ} {A B} → Γ ∋ A → Γ ∋ B → A ≡ B
  -- var-


var-split : ∀ {Δ Δ₁} {Γ₁ Ω₁ : Context Δ₁} {Ω : Context Δ} {A B q} → (Γ₁ ∋ A) → (Ω₁ ≈ q * Γ₁ # Ω) → (Ω₁ ∋ B)
          → zero-like q ⊎ (one-like q × CEmpty Ω)
var-split {_} {_} {.(_ ,:⟨ POSemiring.one' mod ⟩ _)} {.(_ ,:⟨ POSemiring.one' mod ⟩ _)} {Ω} (Z x) p (Z x₁) = {!!}
var-split {_} {_} {.(_ ,:⟨ POSemiring.one' mod ⟩ _)} {.(_ ,:⟨ POSemiring.zero' mod ⟩ _)} {Ω} (Z x) p (S y) = {!!}
var-split {_} {_} {.(_ ,:⟨ POSemiring.zero' mod ⟩ _)} {Ω₁} {Ω} (S x) p y = {!!}


subst : ∀ {Δ₁ Δ₂} {Γ₁ : Context Δ₁} {Γ₂ Ω : Context Δ₂} {Ω₁ Ω₂ q A}
      → (x : Γ₁ ∋ A)
      → (s : Γ₂ ⊢ A)
      → (Ω₁ ≈ q * Γ₁ # Ω)
      → (Ω₂ ≈ q ** Γ₂ ++ Ω)
      → (∀ {B} → Ω₁ ⊢ B → Ω₂ ⊢ B)
subst {_} {_} {Γ₁} {Γ₂} {Ω} {Ω₁} {Ω₂} x s p1 p2 {B} (` x₁) with var-help x p1 x₁
...                    | inj₁ qz = ` (zero-ctx-eq (subs≡ (λ g → Ω₂ ≈ g ** Γ₂ ++ Ω ) qz p2) (subs≡ (λ g → Ω₁ ≈ g * Γ₁ # Ω) qz p1) x₁)
...                    | inj₂ qo = cont-exc (**++-eq p2 (proj₁ qo) (proj₂ qo)) (type-exc (cont-type-exc x (subs≡ (λ g → g ∋ B) ((sym (**#-eq p1 (proj₁ qo) (proj₂ qo)))) x₁)) s)
subst x s p1 p2 (ƛ:⟨ q ⟩ A ⇒ b) = {!!}
subst x s p1 p2 (appP x₁ b b₁) = {!!}
subst x s p1 p2 (unitP x₁) = {!!}
subst x s p1 p2 (unitElimP x₁ b b₁) = {!!}
subst x s p1 p2 (boxP q x₁ b) = {!!}
subst x s p1 p2 (boxElimP x₁ b b₁) = {!!}
subst x s p1 p2 (pairP x₁ b b₁) = {!!}
subst x s p1 p2 (pairElimP x₁ b b₁) = {!!}
subst x s p1 p2 (inj₁ b) = {!!}
subst x s p1 p2 (inj₂ b) = {!!}
subst x s p1 p2 (sumElimP q x₁ b b₁ b₂) = {!!}

-- subst .(Z em) s {CSurr-Z em} (` Z x) = subst-var {!!} {!!} {!!}
-- subst .(Z em) s {CSurr-Z em} (` (S x₁)) = subst-var {!!} {!!} {!!}
-- subst .(S _) s {CSurr-S Ω₁} (` x₁) = subst-var {!!} {!!} {!!}


-- relation stuff
-- subst : ∀ {Δ₁ Δ₂} {Γ₁ : Context Δ₁} {Γ₂ Ω : Context Δ₂} {Ω₁ Ω₂ q}
--       → {Ω₁ ≈ q * Γ₁ # Ω}
--       → {Ω₂ ≈ q ** Γ₂ ++ Ω}
--       → (∀ {A} → Γ₁ ∋ A → Γ₂ ⊢ A)
--       → (∀ {B} → Ω₁ ⊢ B → Ω₂ ⊢ B)
-- subst f {B} (` x) = {!!} -- need omega empty, q = 1
-- subst f (ƛ:⟨ q ⟩ A ⇒ b) = {!!}
-- subst f (appP x b b₁) = {!!}
-- subst f (unitP x) = {!!}
-- subst f (unitElimP x b b₁) = {!!}
-- subst f (boxP q x b) = {!!}
-- subst f (boxElimP x b b₁) = {!!}
-- subst f (pairP x b b₁) = {!!}
-- subst f (pairElimP x b b₁) = {!!}
-- subst f (inj₁ b) = {!!}
-- subst f (inj₂ b) = {!!}
-- subst f (sumElimP q x b b₁ b₂) = {!!}
```
