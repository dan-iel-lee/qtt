

## Yay

```
{-# OPTIONS --rewriting #-}

module QTT.CoreExtrinsic where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)
open import Agda.Builtin.Equality
-- open import Agda.Builtin.Equality.Rewrite

open import Relation.Nullary using (¬_)
open import Data.Nat
open import Data.Nat.Properties using (+-comm; +-assoc; +-identity; *-assoc; *-identity; *-zero; ≤-reflexive; ≤-antisym; ≤-trans)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) 
open import Data.String using (String)
open import Data.List using (List; map; []; _∷_; zip)
open import Function using (_∘_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Empty

record POSemiring (A : Set) : Set₁ where
  field
    _+'_ : A → A → A
    _*'_ : A → A → A
    zero' : A
    one' : A

    +-comm' : ∀ (a b : A) → a +' b ≡ b +' a
    +-assoc' : ∀ (a b c : A) → ( a +' b ) +' c ≡ a +' ( b +' c )
    +-identity' : ( ∀ (a : A) → zero' +' a ≡ a ) × ( ∀ (a : A) → a +' zero' ≡ a )

    *-assoc' : ∀ (a b c : A) → ( a *' b ) *' c ≡ a *' ( b *' c )
    *-identity' : ( ∀ (a : A) → one' *' a ≡ a ) × ( ∀ (a : A) → a *' one' ≡ a )
    *-zero' : ( ∀ (a : A) → zero' *' a ≡ zero' ) × ( ∀ (a : A) → a *' zero' ≡ zero' )

    _≤'_ : A → A → Set
    ≤'-refl : ∀ {a : A} → a ≤' a
    ≤'-antisym : ∀ {a b : A} → a ≤' b → b ≤' a → a ≡ b
    ≤'-trans : ∀ {a b c : A} → a ≤' b → b ≤' c → a ≤' c

nat-pos : POSemiring ℕ
nat-pos = record
            { _+'_ = _+_
            ; _*'_ = _*_
            ; zero' = 0
            ; one' = 1
            ; +-comm' = +-comm
            ; +-assoc' = +-assoc
            ; +-identity' = +-identity
            ; *-assoc' = *-assoc
            ; *-identity' = *-identity
            ; *-zero' = *-zero
            ; _≤'_ = _≤_
            ; ≤'-refl = λ { {a} → ≤-reflexive {a} refl }
            ; ≤'-antisym = ≤-antisym
            ; ≤'-trans = ≤-trans
            }

module Language {R : Set} {{mod : POSemiring R}} where

  _*'_ = POSemiring._*'_ mod
  _+'_ = POSemiring._+'_ mod
  zero' = POSemiring.zero' mod
  one' = POSemiring.one' mod

  *'-zero = POSemiring.*-zero' mod
  *'-identity = POSemiring.*-identity' mod
  +'-identity = POSemiring.+-identity' mod
  +'-comm = POSemiring.+-comm' mod
  +'-assoc = POSemiring.+-assoc' mod


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

  -- typing context indexed by a list of context elements
  data Context : (List Type) → Set₁ where
    Ø : Context []
    _,:⟨_⟩_ : {Δ : List Type} →
                    Context Δ → R → ∀ (A : Type) → Context ( A ∷ Δ )
  
  infixl 8 _,:⟨_⟩_

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



  data CEmpty : ∀ {Δ : List Type} → Context Δ → Set where
    Ø-empty : CEmpty Ø
    ,-empty : ∀ {Δ : List Type} {Γ₁ : Context Δ} {A : Type}
              → CEmpty Γ₁
              ---------
              → CEmpty (Γ₁ ,:⟨ zero' ⟩ A)


  data Term : Set₁ where
    -- 
    `_ : ℕ → Term

    ƛ:⟨_⟩_⇒_ : R → Type → Term → Term

    _·_ : Term → Term → Term

    unit : Term

    let-unit≔_in'_ : Term → Term → Term

    box⟨_⟩_ : R → Term → Term

    let-box≔_in'_ : Term → Term → Term

    ⟨_,_⟩ : Term → Term → Term

    let⟨,⟩≔_in'_ : Term → Term → Term

    inj₁ : Term → Term
    inj₂ : Term → Term

    case⟨_⟩_of_||_ : R → Term → Term → Term → Term

  -- LOOKUP
  data _∋_ : ∀ {Δ} → Context Δ → Type → Set₁ where

    Z : ∀ {Δ} {Γ : Context Δ} {A}
      -------
      → (zero' ** Γ ,:⟨ one' ⟩ A) ∋ A    -- only allow empty for simplicity,

    S_ : ∀ {Δ} {Γ : Context Δ} {A B}
       → Γ ∋ A
         --------
       → (Γ ,:⟨ zero' ⟩ B) ∋ A

  lookupIndex : ∀ {Δ} {Γ : Context Δ} {A} → Γ ∋ A → ℕ
  lookupIndex Z = 0
  lookupIndex (S lu) = suc (lookupIndex lu)

  infix 5 _∋_

  data _⊢_⦂_ {Δ} : Context Δ → Term → Type → Set₁
  infix 3 _⊢_⦂_

  data _⊢_⦂_ {Δ} where

    ST-Var : ∀ {Γ : Context Δ} {A : Type}
           → (lu : Γ ∋ A)
             -------
           → Γ ⊢ ` (lookupIndex lu) ⦂ A

    ST-Abs : ∀ {Γ : Context Δ} {A B b q}
           → (Γ ,:⟨ q ⟩ A) ⊢ b ⦂ B
             --------------
           → Γ ⊢ (ƛ:⟨ q ⟩ A ⇒ b) ⦂ (A -⟨ q ⟩→ B)

    ST-App : ∀ {Γ₁ Γ₂ : Context Δ} {A B a b q}
           → Γ₁ ⊢ a ⦂ (A -⟨ q ⟩→ B)
           → Γ₂ ⊢ b ⦂ A
             ----------
           → (q ** Γ₂ ++ Γ₁) ⊢ (a · b) ⦂ B

    ST-Unit : ∀ {Γ : Context Δ}
            → CEmpty Γ
              -------
            → Γ ⊢ unit ⦂ Unit

    ST-UnitE : ∀ {Γ₁ Γ₂ : Context Δ} {A a b}
             → Γ₁ ⊢ a ⦂ Unit
             → Γ₂ ⊢ b ⦂ A
               -------
             → (Γ₁ ++ Γ₂) ⊢ let-unit≔ a in' b ⦂ A

    ST-Box : ∀ {Γ : Context Δ} {A a q}
           → Γ ⊢ a ⦂ A
             --------
           → (q ** Γ) ⊢ box⟨ q ⟩ a ⦂ [ q ] A

    ST-BoxE : ∀ {Γ₁ Γ₂ : Context Δ} {A B a b q}
            → Γ₁ ⊢ a ⦂ [ q ] A
            → Γ₂ ,:⟨ q ⟩ A ⊢ b ⦂ B
              -----------
            → Γ₁ ++ Γ₂ ⊢ let-box≔ a in' b ⦂ B

    ST-Pair : ∀ {Γ₁ Γ₂ : Context Δ} {A B a b}
            → Γ₁ ⊢ a ⦂ A
            → Γ₂ ⊢ b ⦂ B
              ------
            → (Γ₁ ++ Γ₂) ⊢ ⟨ a , b ⟩ ⦂ A ⊗ B

    ST-PairE : ∀ {Γ₁ Γ₂ : Context Δ} {A₁ A₂ B a b}
             → Γ₁ ⊢ a ⦂ A₁ ⊗ A₂
             → Γ₂ ,:⟨ one' ⟩ A₁ ,:⟨ one' ⟩ A₂ ⊢ b ⦂ B
               ------------
             → (Γ₁ ++ Γ₂) ⊢ let⟨,⟩≔ a in' b ⦂ B

    ST-Inj1 : ∀ {Γ : Context Δ} {A B a}
            → Γ ⊢ a ⦂ A
              -----
            → Γ ⊢ inj₁ a ⦂ A ⊕ B

    ST-Inj2 : ∀ {Γ : Context Δ} {A B b}
            → Γ ⊢ b ⦂ B
              -----
            → Γ ⊢ inj₂ b ⦂ A ⊕ B

    ST-Case : ∀ {Γ₁ Γ₂ : Context Δ} {A₁ A₂ B q a f g}
            → Γ₁ ⊢ a ⦂ A₁ ⊕ A₂
            → Γ₂ ⊢ f ⦂ A₁ -⟨ q ⟩→ B
            → Γ₂ ⊢ g ⦂ A₂ -⟨ q ⟩→ B
              ---------
            → (q ** Γ₁ ++ Γ₂) ⊢ case⟨ q ⟩ a of f || g ⦂ B

  -- substitution
  _[_] : Term → Term → Term
  (` x) [ b ] = {!!}
  (ƛ:⟨ x ⟩ x₁ ⇒ a) [ b ] = {!!}
  (a · a₁) [ b ] = {!!}
  unit [ b ] = {!!}
  (let-unit≔ a in' a₁) [ b ] = {!!}
  (box⟨ x ⟩ a) [ b ] = {!!}
  (let-box≔ a in' a₁) [ b ] = {!!}
  ⟨ a , a₁ ⟩ [ b ] = {!!}
  (let⟨,⟩≔ a in' a₁) [ b ] = {!!}
  inj₁ a [ b ] = {!!}
  inj₂ a [ b ] = {!!}
  (case⟨ x ⟩ a of a₁ || a₂) [ b ] = {!!}




  infix 25 `_
  infixl 21 _·_
  infix 22 let-unit≔_in'_
  infix 22 let-box≔_in'_
  infix 22 let⟨,⟩≔_in'_
  infix 22 case⟨_⟩_of_||_
  infix 23 box⟨_⟩_


