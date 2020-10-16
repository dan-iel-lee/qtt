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

data QContext : TContext → Set₁ where
  Ø : QContext ∅
  _,⟨_⟩_ : {Δ : TContext} →
          QContext Δ → R → ∀ (A : Type) → QContext ( Δ , A )
infixl 8 _,⟨_⟩_


-- TODO: make DECIDABLE
-- inductive definition of an empty context
data CEmpty : ∀ {Δ} → QContext Δ → Set where
  Ø-empty : CEmpty Ø
  $-empty : ∀ {Δ} {Γ : QContext Δ} {A}
          → CEmpty Γ
            ---------
          → CEmpty (Γ ,⟨ zero' ⟩ A)

_++_ : TContext → TContext → TContext
Δ ++ ∅ = Δ
Δ ++ (Δ₁ , A) = (Δ ++ Δ₁) , A

_<>_ : ∀ {Δ₁ Δ₂} (Γ₁ : QContext Δ₁) (Γ₂ : QContext Δ₂) → QContext (Δ₁ ++ Δ₂)
Γ <> Ø = Γ
Γ <> (Γ₁ ,⟨ q ⟩ A) = (Γ <> Γ₁) ,⟨ q ⟩ A

infixl 5 _++_
infixl 5 _<>_

-- context operations
data _≈_⨂_⨁_ : ∀ {Δ} → QContext Δ → R → QContext Δ → QContext Δ → Set where

  CArith-Emp : ∀ {Δ} {Γ Γ₁ : QContext Δ} {q}
             → CEmpty Γ₁
             → Γ ≈ q ⨂ Γ₁ ⨁ Γ

  CArith-Zero :  ∀ {Δ} {Γ Γ₁ : QContext Δ} {q}
              → q ≡ zero'
              → Γ ≈ q ⨂ Γ₁ ⨁ Γ

  CArith-, : ∀ {Δ} {Θ Γ₁ Γ₂ : QContext Δ} {A q₁ q₂ q q'}
           → (Θ ≈ q ⨂ Γ₁ ⨁ Γ₂)
           → (q' ≡ q *' q₁ +' q₂)
           → (Θ ,⟨ q' ⟩ A) ≈ q ⨂ (Γ₁ ,⟨ q₁ ⟩ A) ⨁ (Γ₂ ,⟨ q₂ ⟩ A)

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

infix 3 _∋_


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
data _⊨_ : ∀ {Δ A} → QContext Δ → Δ ⊢ A → Set₁
infix 1 _⊨_

data _⊨_ where

  VarZ : ∀ {Δ} {Γ : QContext Δ} {A}
       → CEmpty Γ     -- context must be  Ø $ 0 $ ... $ 0 $ 1
       → (Γ ,⟨ one' ⟩ A) ⊨ (` Z)

  -- variable weakening
  VarS : ∀ {Δ A B} {Γ : QContext Δ} {x : Δ ∋ A}
       → Γ ⊨ ` x
       → (Γ ,⟨ zero' ⟩ B) ⊨ ` (S x)

  Lambda : ∀ {Δ q A B} {Γ : QContext Δ} {b : Δ , A ⊢ B}
         → (Γ ,⟨ q ⟩ A) ⊨ b -- need b to be well quantified under context with q As
         → Γ ⊨ (ƛ:⟨ q ⟩ A ⇒ b)

  App : ∀ {Δ A B q} {Γ Γ₁ Γ₂ : QContext Δ} {a : Δ ⊢ A -⟨ q ⟩→ B} {b : Δ ⊢ A}
      → Γ ≈ q ⨂ Γ₂ ⨁ Γ₁
      → Γ₁ ⊨ a
      → Γ₂ ⊨ b
      → Γ ⊨ a · b

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


_[_] : ∀ {Δ A B}
     → Δ , B ⊢ A
     → Δ ⊢ B
     → Δ ⊢ A
_[_] {Δ} {A} {B} a b = subst {Δ , B} f a
  where
    f : ∀ {A} → Δ , B ∋ A → Δ ⊢ A
    f Z = b  -- how is this okay? since b is for a fixed type B
    f (S x) = ` x





-- -- alternative sub
-- subst' : ∀ {Δ₁ Δ₂ A B}
--        → Δ₁ , B ++ Δ₂ ⊢ A
--        → Δ₁ ⊢ B
--        → Δ₁ , B ++ Δ₂ ∋ A
--        → Δ₁ ++ Δ₂ ⊢ A
-- subst' (` x₁) b x = {!!}
-- subst' (ƛ:⟨ q ⟩ A ⇒ a) b x = {!!}
-- subst' (a · a₁) b x = {!!}

```

## Properties
```

postulate
  times-eq : ∀ {Δ} {Γ Γ₁ Γ₂ : QContext Δ} → Γ ≈ one' ⨂ Γ₂ ⨁ Γ₁ → CEmpty Γ₁ → Γ ≡ Γ₂


-- f-quant f = ∀ (a : Δ₁ , B ++ Δ₂ ∋ A₁) → 

substitution : ∀ {Δ A B} (Γ₁ Γ₂ Γ : QContext Δ) (a : Δ , B ⊢ A) (b : Δ ⊢ B)
               (q : R)
             → Γ₁ ,⟨ q ⟩ B ⊨ a
             → Γ₂ ⊨ b
             → Γ ≈ q ⨂ Γ₂ ⨁ Γ₁
             → Γ ⊨ a [ b ]
substitution Γ₁ Γ₂ Γ .(` Z) b .(one') (VarZ x) Qb eq = subs≡ (λ qc → qc ⊨ b) (sym (times-eq eq x)) Qb
substitution Γ₁ Γ₂ Γ .(` (S _)) b .(POSemiring.zero' mod) (VarS Qa) Qb eq = {!!}
substitution Γ₁ Γ₂ Γ .(ƛ:⟨ _ ⟩ _ ⇒ _) b q (Lambda Qa) Qb eq = {!!}
substitution Γ₁ Γ₂ Γ .(_ · _) b q (App x Qa Qa₁) Qb eq = {!!}

substitution' : ∀ {Δ₁ Δ₂ A B} {Γ₁ : QContext Δ₁} {Γ₂ : QContext Δ₂} {Γ Γ₃ : QContext (Δ₁ ++ Δ₂)}
                {f : ∀ {A₁} → Δ₁ , B ++ Δ₂ ∋ A₁ → Δ₁ ++ Δ₂ ⊢ A₁}
                (a : Δ₁ , B ++ Δ₂ ⊢ A)
                (q : R)
               → (∀ {x} → Γ₃ ⊨ (f {B} x))
              → Γ₁ ,⟨ q ⟩ B <> Γ₂ ⊨ a
              → Γ ≈ q ⨂ Γ₃ ⨁ Γ₁
              → Γ <> Γ₂ ⊨ (subst f a)
```
