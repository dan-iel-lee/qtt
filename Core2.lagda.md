
## Yay

```
module QTT.Core2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)
open import Relation.Nullary using (¬_)
open import Data.Nat
open import Data.Nat.Properties using (+-comm; +-assoc; +-identity; *-assoc; *-identity; *-zero; ≤-reflexive; ≤-antisym; ≤-trans)
open import Data.Product using (_×_; proj₁; proj₂) 
open import Data.String using (String)
open import Data.List using (List; map; []; _∷_; zip)
open import Function using (_∘_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (Any; here; there)

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

  data Type : Set₁ where
    Unit : Type
    _-⟨_⟩→_ : Type → R → Type → Type
    [_]_ : R → Type → Type

  infix 20 [_]_
  infix 19 _-⟨_⟩→_




  Id : Set
  Id = String

  data Term : Set₁ where
    `_ : Id → Term
    ƛ_:⟨_⟩_⇒_ : Id → R → Type → Term → Term
    _·_ : Term → Term → Term

    unit : Term
    let-unit≔_in'_ : Term → Term → Term
    box⟨_⟩_ : R → Term → Term
    let-box_≔_in'_ : Id → Term → Term → Term

--   ⟨_,_⟩ : Term → Term → Term
--   let⟨_,_⟩≔_in'_ : Id → Id → Term → Term → Term
--
--   inj₁_ : Term → Term
--   inj₂_ : Term → Term
--   case⟨_⟩_of_||_ : R → Term → Term → Term → Term

  infix 20 `_
  infix 19 ƛ_:⟨_⟩_⇒_
  infix 18 _·_




  -- typing context elements
  data ContextElem : Set₁ where
    Elem : Id → Type → ContextElem

  syntax Elem id A = id := A

  -- typing context indexed by a list of context elements
  data Context : (List ContextElem) → Set₁ where
    Ø : Context []
    _#_:⟨_⟩_ : {Δ : List ContextElem} →
                    Context Δ → ∀ (id : Id) → R → ∀ (A : Type) → Context ( (id := A) ∷ Δ )

  infixl 15 _#_:⟨_⟩_

  -- context scaling
  _**_ : {Δ : List ContextElem} → R → Context Δ → Context Δ
  infix 10 _**_
  _ ** Ø = Ø
  a ** Γ # x :⟨ q ⟩ A  =  Γ # x  :⟨ a *' q ⟩ A

  -- context addition
  _++_ : {Δ : List ContextElem} → (Γ₁ : Context Δ) → (Γ₂ : Context Δ) → Context Δ
  infix 9 _++_
  Ø ++ Ø = Ø
  Γ₁ # x :⟨ q1 ⟩ A  ++  Γ₂ # .x :⟨ q2 ⟩ .A  =  (Γ₁ ++ Γ₂) # x :⟨ q1 +' q2 ⟩ A

  -- domain extraction
  domain : List ContextElem → List Id
  domain = map (λ { ( id := _ ) → id })


  -- 
  data CEmpty : ∀ {Δ : List ContextElem} → Context Δ → Set where
    Ø-empty : CEmpty Ø
    #-empty : ∀ {Δ : List ContextElem} {Γ₁ : Context Δ} {x : Id} {A : Type}
            → CEmpty Γ₁
              ---------
            → CEmpty (Γ₁ # x :⟨ zero' ⟩ A)
    



  data WellTyped : {Δ : List ContextElem} → (Γ : Context Δ) → (x : Term) → (A : Type) → Set₁
  infix 14 WellTyped
  syntax WellTyped Γ x A = Γ ⊢ x :' A

  data WellTyped where 

    ST-Var :  {Δ : List ContextElem} {x : Id} {Γ : Context Δ} {A : Type} →

                CEmpty Γ
              → x ∉ domain Δ
                  --------
              → ( (zero' ** Γ) # x :⟨ one' ⟩ A ) ⊢ (` x) :' A

    ST-Weak :  {Δ : List ContextElem} {x : Id} {Γ : Context Δ} {A B : Type} {a : Term} →

                 x ∉ domain Δ
               → Γ ⊢ a :' B
                   -------
               → (Γ # x :⟨ zero' ⟩ A ) ⊢ a :' B

    ST-Lambda :  {Δ : List ContextElem} {x : Id} {Γ : Context Δ} {A B : Type} {a b : Term} {q : R} →

                  (Γ # x :⟨ q ⟩ A ) ⊢ b :' B
                    ---------
                → Γ ⊢ (ƛ x :⟨ q ⟩ A ⇒ b) :' (A -⟨ q ⟩→ B)

    ST-App :  {Δ : List ContextElem} {Γ₁ Γ₂ : Context Δ} {A B : Type} {a b : Term} {q : R} → 
                  Γ₁ ⊢ a :' (A -⟨ q ⟩→ B)
                → Γ₂ ⊢ b :' A
                    ----------
                → (Γ₁ ++ q ** Γ₂) ⊢ (a · b) :' B

    ST-Unit : Ø ⊢ unit :' Unit

    ST-UnitE :   {Δ : List ContextElem} {Γ₁ Γ₂ : Context Δ} {B : Type} {a b : Term} →

                  Γ₁ ⊢ a :' Unit
                → Γ₂ ⊢ b :' B
                    ----------
                → (Γ₁ ++ Γ₂) ⊢ let-unit≔ a in' b :' B

    ST-Box :  {Δ : List ContextElem} {Γ : Context Δ} {A : Type} {a : Term} {q : R} →

                  Γ ⊢ a :' A
                    ---------
                → (q ** Γ) ⊢ box⟨ q ⟩ a :' ([ q ] A)

    ST-BoxE :  {Δ : List ContextElem} {Γ₁ Γ₂ : Context Δ} {A B : Type} {a b : Term} {q : R} {x : Id} → 

                   Γ₁ ⊢ a :' ([ q ] A)
                →  Γ₂ # x :⟨ q ⟩ A ⊢ b :' B
                      --------------
                → (Γ₁ ++ Γ₂) ⊢ (let-box x ≔ a in' b) :' B

```

### Examples

```
open Language {ℕ} {{nat-pos}}

pxe : "x" ≢ "f"
pxe = λ()

example : (Ø # "f" :⟨ 1 ⟩ Unit -⟨ 3 ⟩→ Unit  # "x" :⟨ 3 ⟩ Unit ) ⊢ ((` "f") · (` "x")) :' Unit
example = ST-App (ST-Weak ((λ {(here px) → pxe px; (there ()) })) (ST-Var Ø-empty (λ()) )) (ST-Var (#-empty Ø-empty) (λ {(here px) → pxe px; (there ()) }))
--example = ST-App ((ST-Weak (λ {(here px) → pxe px; (there ()) }) (ST-Var λ()) )) (ST-Var {!!})
-- example = ST-App ( ST-Weak (λ {(here px) → {!!} ; (there pxs) → (λ()) pxs}) ( ST-Var (λ())) ) (ST-Var (λ {(here px) → (λ()) px ; (there pxs) → (λ()) pxs}))
```

## Heap semantics

```


```

{-
record Variable (V : Set) : Set where
  field
    associate : V → Term -⟩ V
    extract : V → Term

-}

-- data Term : Set where
  
  

```
