## Yay

```
{-# OPTIONS --rewriting #-}

open import QTT.POSemiring using (POSemiring)

module QTT.Relations {R : Set} {{mod : POSemiring R}} where

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


open import QTT.Definitions {R} {{mod}}


postulate
  rename : ∀ {Δ₁ Δ₂} {Γ₁ : Context Δ₁} {Γ₂ : Context Δ₂}
         → (∀ {A} → Γ₁ ∋ A → Γ₂ ∋ A)
         → (∀ {A} → Γ₁ ⊢ A → Γ₂ ⊢ A)

-- how to weaken when the term has a free variable?
-- answer: have to rename free variables to one higher
-- want to encode weakening
weaken : ∀ {Δ} {Γ : Context Δ} {A B} → Γ ⊢ A → Γ ,:⟨ zero' ⟩ B ⊢ A
weaken (` x) = ` (S x)
weaken (ƛ:⟨ q ⟩ A ⇒ a) = {!!}
weaken (appP x a a₁) = {!!}
weaken (unitP x) = {!!}
weaken (unitElimP x a a₁) = {!!}
weaken (boxP q x a) = {!!}
weaken (boxElimP x a a₁) = {!!}
weaken (pairP x a a₁) = {!!}
weaken (pairElimP x a a₁) = {!!}
weaken (inj₁ a) = {!!}
weaken (inj₂ a) = {!!}
weaken (sumElimP q x a a₁ a₂) = {!!}


subst-var : ∀ {Δ₁ Δ₂} {Γ₁ : Context Δ₁} {Γ₂ : Context Δ₂} {A}
          → (x : Γ₁ ∋ A)
          → (s : Γ₂ ⊢ A)
          → (y : Γ₁ ∋ A)
          → Γ₂ ⊢ A
subst-var = {!!}


subst' : ∀ {Δ₁ Δ₂} {Ω₁ : Context Δ₁} {Ω₂ : Context Δ₂} 
       → (∀ {A} {Γ₁ : Context Δ₁} {Γ₂ : Context Δ₂} → Γ₁ ∋ A → Γ₂ ⊢ A)
       → (∀ {B} → Ω₁ ⊢ B → Ω₂ ⊢ B)
subst' f (` x) = f x
subst' f (ƛ:⟨ q ⟩ A ⇒ b) = {!!}
subst' f (appP x b b₁) = {!!}
subst' f (unitP x) = {!!}
subst' f (unitElimP x b b₁) = {!!}
subst' f (boxP q x b) = {!!}
subst' f (boxElimP x b b₁) = {!!}
subst' f (pairP x b b₁) = {!!}
subst' f (pairElimP x b b₁) = {!!}
subst' f (inj₁ b) = {!!}
subst' f (inj₂ b) = {!!}
subst' f (sumElimP q x b b₁ b₂) = {!!}




_[_] : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A B q} → (Γ₁ ,:⟨ q ⟩ B ⊢ A) → (Γ₂ ⊢ B) → q ** Γ₂ ++ Γ₁ ⊢ A
_[_] {Δ} {Γ₁} {Γ₂} {A} {B} {q} a s = subst' {_} {_} {Γ₁ ,:⟨ q ⟩ B} {q ** Γ₂ ++ Γ₁} f {A} a
  where
    f : ∀ {A} {Γ₁ : Context (B ∷ Δ)} {Γ₂ : Context Δ} → Γ₁ ∋ A → Γ₂ ⊢ A
    f (Z emp) = {!s!}
    f (S t) = {!!}
{-

data Value {Δ} : ∀ {Γ : Context Δ} {A} → Γ ⊢ A → Set₁ where

  V-Var : ∀ {Γ : Context Δ} {A}
        → (v : Γ ∋ A)
        → Value (` v)

  V-Lam : ∀ {Γ : Context Δ} {A B q} {a : Γ ,:⟨ q ⟩ A ⊢ B}
        → Value (ƛ:⟨ q ⟩ A ⇒ a)

  V-unit : ∀ {Γ : Context Δ}
          → Value (unit {Γ = Γ})

  V-Box : ∀ {Γ : Context Δ} {q A} {a : Γ ⊢ A}
        → Value (box⟨ q ⟩ a)

  V-Conj : ∀ {Γ₁ Γ₂ : Context Δ} {A B} {a : Γ₁ ⊢ A} {b : Γ₂ ⊢ B}
          → Value ⟨ a , b ⟩

  V-Inj₁ : ∀ {Γ : Context Δ} {A B} {a : Γ ⊢ A}
          → Value (inj₁ {B = B} a)

  V-Inj₂ : ∀ {Γ : Context Δ} {A B} {b : Γ ⊢ B}
          → Value (inj₂ {A = A} b)



-- small step call by name
data _⟶_ {Δ} : ∀ {Γ : Context Δ} {A} → Γ ⊢ A → Γ ⊢ A → Set₁ where

  S-AppCong : ∀ {Γ : Context Δ} {A B q} {a a' : Γ ⊢ A -⟨ q ⟩→ B} {b : Γ ⊢ A}
            → a ⟶ a'
            → a · b ⟶ a' · b

  S-Beta : ∀ {Γ : Context Δ} {A B q} {a : Γ ,:⟨ q ⟩ A ⊢ B} {b : Γ ⊢ A}
          → (ƛ:⟨ q ⟩ A ⇒ a) · b ⟶ (a [ b ])

  S-UnitCong : ∀ {Γ₁ Γ₂ : Context Δ} {A} {a a' : Γ₁ ⊢ Unit} {b : Γ₂ ⊢ A}
              → a ⟶ a'
              → let-unit≔ a in' b ⟶ let-unit≔ a' in' b

  S-UnitBeta : ∀ {Γ Γ₁ : Context Δ} {B} {b : Γ ⊢ B}
              → let-unit≔ unit {Γ = Γ₁} in' b ⟶ b

  -- not from paper
{-
  S-BoxCong : ∀ {Γ : Context Δ} {A q} {a a' : Γ ⊢ A}
            → a ⟶ a'
            → box⟨ q ⟩ a ⟶ box⟨ q ⟩ a'


  S-LetBoxCong : ∀ {Γ Γ' : Context Δ} {A B q} {b b' : Γ ⊢ [ q ] A} {a : Γ' ,:⟨ q ⟩ A ⊢ B}
                → b ⟶ b'
                → let-box≔ b in' a ⟶ let-box≔ b' in' a
-}

  -- call by name, b does not have to be a value
  S-BoxBeta :  ∀ {Γ₁ Γ₂ : Context Δ} {q A B}
                  {b : Γ₁ ⊢ A}
                  {a : Γ₂ ,:⟨ q ⟩ A ⊢ B}
                → let-box≔ box⟨ q ⟩ b in' a ⟶ (a [ b ])

  S-PairBeta : ∀ {Γ₁ Γ₂ Γ : Context Δ} {A₁ A₂ B}
                {l : Γ₁ ⊢ A₁}
                {r : Γ₂ ⊢ A₂}
                {a : Γ ,:⟨ one' ⟩ A₁ ,:⟨ one' ⟩ A₂ ⊢ B}
              → let⟨,⟩≔ ⟨ l , r ⟩ in' a ⟶
                        (ƛ:⟨ one' ⟩ A₁ ⇒ (ƛ:⟨ one' ⟩ A₂ ⇒ a)) · l · r
                        -- reusing lambda here so that I don't have to make subst more powerful

  S-CaseBeta₁ : ∀ {Γ₁ Γ₂ : Context Δ} {A₁ A₂ B q}
                {a : Γ₁ ⊢ A₁}
                {f : Γ₂ ⊢ A₁ -⟨ q ⟩→ B}
                {g : Γ₂ ⊢ A₂ -⟨ q ⟩→ B}
              → case⟨ q ⟩ inj₁ a of f || g ⟶ f · a

  S-CaseBeta₂ : ∀ {Γ₁ Γ₂ : Context Δ} {A₁ A₂ B q}
                {a : Γ₁ ⊢ A₂}
                {f : Γ₂ ⊢ A₁ -⟨ q ⟩→ B}
                {g : Γ₂ ⊢ A₂ -⟨ q ⟩→ B}
              → case⟨ q ⟩ inj₂ a of f || g ⟶ g · a
 -}
```
