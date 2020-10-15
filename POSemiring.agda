module QTT.POSemiring where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)

open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax; _,_) 

open import Data.Nat
open import Data.Nat.Properties using (+-comm; +-assoc; +-identity; *-assoc; *-identity; *-zero; ≤-reflexive; ≤-antisym; ≤-trans)
open import Relation.Binary using (Decidable)

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

    _≛_ : Decidable {A = A} _≡_

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
            ; _≛_ = _≟_
            }
