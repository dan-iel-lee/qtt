
## Yay

```

open import QTT.POSemiring using (POSemiring)

module QTT.Definitions {R : Set} {{mod : POSemiring R}} where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Relation.Nullary using (¬_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat
open import Data.Nat.Properties using (+-comm; +-assoc; +-identity; *-assoc; *-identity; *-zero; ≤-reflexive; ≤-antisym; ≤-trans)
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

  Z_ : ∀ {Δ} {Γ : Context Δ} {A}
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

```
