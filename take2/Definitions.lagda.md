## Yay

```
{-# OPTIONS --allow-unsolved-metas #-}

open import QTT.POSemiring using (POSemiring)

module QTT.take2.Definitions {R : Set} {{mod : POSemiring R}} where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym) renaming (subst to subs≡)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Relation.Nullary using (¬_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat
open import Data.Nat.Properties using (+-comm; +-assoc; +-identity; *-assoc; *-identity; *-zero; ≤-reflexive; ≤-antisym; ≤-trans)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
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

data TContext : Set₁ where
  ∅ : TContext
  _,_ : TContext → Type → TContext

data QContext : Set where
  Ø : QContext
  _$_ : QContext → R → QContext

-- inductive definition of an empty context
data CEmpty : QContext → Set where
  Ø-empty : CEmpty Ø
  $-empty : ∀ {Δ A}
          → CEmpty Δ
            ---------
          → CEmpty (Δ $ A)

data CCompat : QContext → TContext → Set where
  Ø~∅ : CCompat Ø ∅
  $~, : ∀ {Γ Δ q A}
      → CCompat Γ Δ
      → CCompat (Γ $ q) (Δ , A)

-- context operations
data _≈_⨂_⨁_ : QContext → R → QContext → QContext → Set where

```

### Terms
```
-- LOOKUP - used for variable definition
data _∋_ : TContext → Type → Set where

  Z : ∀ {Δ A}
    ---------
    → Δ , A ∋ A

  S_ : ∀ {Δ A B}
    → Δ ∋ A
      ---------
    → Δ , B ∋ A

infix 5 _∋_


-- inductive definition of terms with intrinsic typing
data _⊢_ : TContext → Type → Set₁
infix 2 _⊢_

data _⊢_ where
  --
  `_ : ∀ {Δ A}
      → Δ ∋ A
        -----
      → Δ ⊢ A

  ƛ:⟨_⟩_⇒_ : ∀ {Δ B}
            → (q : R)
            → (A : Type)
            → Δ , A ⊢ B
              -----------
            → Δ ⊢ A -⟨ q ⟩→ B

  _·_ : ∀ {Δ} {A B q}
        → Δ ⊢ A -⟨ q ⟩→ B
        → Δ ⊢ A
        → Δ ⊢ B

infix 25 `_

-- well quantified
-- TODO: define what it means for a term to be well quantified
data _⊨_ : ∀ {Δ A} → QContext → Δ ⊢ A → Set₁
infix 1 _⊨_

data _⊨_ where

  VarZ : ∀ {Γ Δ A}
       → CCompat Γ Δ  -- ensure contexts are same length
       → CEmpty Γ     -- context must be  Ø $ 0 $ ... $ 0 $ 1
       → (Γ $ one') ⊨ (` (Z {Δ} {A}))

  -- variable weakening
  VarS : ∀ {Γ Δ A B x}
       → Γ ⊨ ` x
       → (Γ $ zero') ⊨ ` (S_ {Δ} {A} {B} x)

  Lambda : ∀ {Γ Δ q A B b}
         → _⊨_ {Δ , A} {B} (Γ $ q) b -- need b to be well quantified under context with q As
         → Γ ⊨ (ƛ:⟨ q ⟩ A ⇒ b)

  App : ∀ {Γ Γ₁ Γ₂ Δ A B q a b}
      → Γ ≈ q ⨂ Γ₂ ⨁ Γ₁
      → Γ₁ ⊨ a
      → Γ₂ ⊨ b
      → Γ ⊨ _·_ {Δ} {A} {B} {q} a b

```

## Computation

```

extr :  ∀ {Δ₁ Δ₂ B}
     → (∀ {A} → Δ₁ ∋ A → Δ₂ ∋ A)
     → (∀ {A} → Δ₁ , B ∋ A → Δ₂ , B ∋ A)
extr f Z = Z
extr f (S v) = S (f v)

rename : ∀ {Δ₁ Δ₂}
       → (∀ {A} → Δ₁ ∋ A → Δ₂ ∋ A)
       → (∀ {B} → Δ₁ ⊢ B → Δ₂ ⊢ B)
rename f (` x) = ` f x
rename f (ƛ:⟨ q ⟩ A ⇒ b) = ƛ:⟨ q ⟩ A ⇒ rename (extr f) b
rename f (b · b₁) = rename f b · rename f b₁

weaken : ∀ {Δ B}
       → (∀ {A} → Δ ⊢ A → Δ , B ⊢ A)
weaken = rename S_

exts : ∀ {Δ₁ Δ₂ B}
     → (∀ {A} → Δ₁ ∋ A → Δ₂ ⊢ A)
     → (∀ {A} → Δ₁ , B ∋ A → Δ₂ , B ⊢ A)
exts f Z = ` Z
exts f (S v) = weaken (f v)

subst : ∀ {Δ₁ Δ₂}
      → (∀ {A} → Δ₁ ∋ A → Δ₂ ⊢ A)
      → (∀ {B} → Δ₁ ⊢ B → Δ₂ ⊢ B)
subst f (` x) = f x
subst f (ƛ:⟨ q ⟩ A ⇒ b) = ƛ:⟨ q ⟩ A ⇒ subst (exts f) b
subst f (b · b₁) = subst f b · subst f b₁
```


