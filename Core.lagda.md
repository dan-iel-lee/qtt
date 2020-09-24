## Yay

```
module QTT.Core where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat
open import Data.Nat.Properties using (+-comm; +-assoc; +-identity; *-assoc; *-identity; *-zero; ≤-reflexive; ≤-antisym; ≤-trans)
open import Data.Product using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩ )
open import Data.String using (String)
open import Data.Vec using (Vec; map; []; _∷_; zip)
open import Function using (_∘_)
open import Data.Vec.Membership.Propositional

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
  zero' = POSemiring.zero' mod
  one' = POSemiring.one' mod

  data Type : Set₁ where
    Unit : Type
    _-<_>→_ : Type → R → Type → Type
    [_]_ : R → Type → Type



  Id : Set
  Id = String
  
  data Term : Set₁ where
    `_ : Id → Term
    ƛ_:<_>_⇒_ : Id → R → Type → Term → Term
    _·_ : Term → Term → Term


  data ContextElem : Set₁ where
    Elem : Id → R → Type → ContextElem
    
  syntax Elem id a A = id :< a > A

  Context : ℕ → Set₁
  Context n = Vec ContextElem n

  _**_ : ∀ {n : ℕ} → R → Context n → Context n
  a ** Γ = map ( λ { ( Elem id b B ) → id :< a *' b > B } ) Γ

  -- how to enforce equality of contexts?
  _++_ : ∀ {n : ℕ} → (Γ₁ : Context n) → (Γ₂ : Context n ) → Context n
  Γ₁ ++ Γ₂ = map {!!} (zip Γ₁ Γ₂)

  domain : ∀ {n : ℕ} → Context n → Vec Id n
  domain = map (λ { ( id :< _ > _ ) → id })




  data WellTyped : ∀ {n : ℕ} → (Γ : Context n) → (x : Term) → (A : Type) → Set₁ where
    ST-Var : ∀ {n : ℕ} → {x : Id} → {Γ : Context n} → (A : Type) →

                x ∉ domain Γ
                  --------
              → WellTyped (( x :< one' > A ) ∷ zero' ** Γ) (` x) A

    ST-Weak : ∀ {n : ℕ} → {x : Id} → {Γ : Context n} → (A B : Type) → (a : Term) →

                 x ∉ domain Γ
               → WellTyped Γ a B
                   -------
               → WellTyped (( x :< zero' > A ) ∷ Γ ) a B

    ST-Lambda : ∀ {n : ℕ} → {x : Id} → {Γ : Context n} → {A B : Type} → {a b : Term} → {q : R} →

                  WellTyped ((x :< q > A) ∷ Γ) b B
                    ---------
                → WellTyped Γ (ƛ x :< q > A ⇒ b) (A -< q >→ B)

    {- ST-App : asdf asdf asdf
                  WellTyped Γ₁ a (A -< q >→ B)
                  WellTyped Γ₂ b A
                → WellTyped Γ (a · b) B -}

{-
record Variable (V : Set) : Set where
  field
    associate : V → Term -> V
    extract : V → Term

-}

-- data Term : Set where
  
  

```
