

## Yay

```
{-# OPTIONS --rewriting #-}

module QTT.Core3 where

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

```

## Basic definitions

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

  -- typing context indexed by a list of context elements
  data Context : (List Type) → Set₁ where
    Ø : Context []
    _,:⟨_⟩_ : {Δ : List Type} →
                    Context Δ → R → ∀ (A : Type) → Context ( A ∷ Δ )



  zeroCtx : (Δ : List Type) → Context Δ
  zeroCtx [] = Ø
  zeroCtx (x ∷ Δ) = (zeroCtx Δ) ,:⟨ zero' ⟩ x
  
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

  -- context concat
  _<>_ : {Δ₁ Δ₂ : List Type} → (Γ₂ : Context Δ₂) → (Γ₁ : Context Δ₁) → Context (Δ₁ <>' Δ₂)
  b <> Ø = b
  b <> (a ,:⟨ x ⟩ A) = (b <> a) ,:⟨ x ⟩ A

  infixl 7 _<>_

  -- context arithmetic laws
  -- ========================

  -- lemma : any contexts indexed by the same List are the same when times 0
  -- help the type checker figure out equalities when things are zeroed
  zero-** : ∀ {Δ} → (Γ : Context Δ) → zero' ** Γ ≡ zeroCtx Δ
  zero-** Ø = refl
  zero-** {Δ = .A ∷ Δ₁} (Γ ,:⟨ x ⟩ A) rewrite zero-** Γ | (proj₁ *'-zero) x = refl
  {-
  zero-** Ø Ø = refl
  zero-** (Γ₁ ,:⟨ x ⟩ A) (Γ₂ ,:⟨ x₁ ⟩ .A)
          rewrite zero-** Γ₁ Γ₂ | (proj₁ *'-zero) x
                                | (proj₁ *'-zero) x₁ = refl-}

  {-# REWRITE zero-** #-}


  -- lemma : adding a zeroed out context is the identity
  ++-identity : ∀ {Δ} → (Γ : Context Δ) → (zeroCtx Δ ++ Γ) ≡ Γ
  ++-identity Ø = refl
  ++-identity (Γ ,:⟨ x ⟩ A) 
             rewrite ++-identity Γ | proj₁ +'-identity x = refl

  ++-identity2 : ∀ {Δ} → (Γ : Context Δ) → Γ ++ zeroCtx Δ ≡ Γ
  ++-identity2 Ø = refl
  ++-identity2 (Γ ,:⟨ x ⟩ A) 
              rewrite ++-identity2 Γ | proj₂ +'-identity x = refl

  {-# REWRITE ++-identity #-}
  {-# REWRITE ++-identity2 #-}

  one-** : ∀ {Δ} (Γ : Context Δ) → one' ** Γ ≡ Γ
  one-** Ø = refl
  one-** (Γ ,:⟨ x ⟩ A) rewrite one-** Γ | (proj₁ *'-identity) x = refl

  ++-comm : ∀ {Δ} (Γ₁ Γ₂ : Context Δ) → Γ₁ ++ Γ₂ ≡ Γ₂ ++ Γ₁
  ++-comm Ø Ø = refl
  ++-comm (g1 ,:⟨ x ⟩ A) (g2 ,:⟨ x₁ ⟩ .A) rewrite ++-comm g1 g2
                                       | +'-comm x x₁ = refl

  ++-assoc : ∀ {Δ} (Γ₁ Γ₂ Γ₃ : Context Δ) → Γ₁ ++ (Γ₂ ++ Γ₃) ≡ (Γ₁ ++ Γ₂) ++ Γ₃
  ++-assoc Ø g2 g3 rewrite ++-identity g2 | ++-identity (g2 ++ g3) = refl
  ++-assoc (g1 ,:⟨ x ⟩ A) (g2 ,:⟨ x₁ ⟩ .A) (g3 ,:⟨ x₂ ⟩ .A)
           rewrite ++-assoc g1 g2 g3
                 | sym (+'-assoc x x₁ x₂) = refl

  ++-swap : ∀ {Δ} (Γ₁ Γ₂ Γ₃ : Context Δ) → Γ₂ ++ (Γ₁ ++ Γ₃) ≡ (Γ₁ ++ Γ₂) ++ Γ₃
  ++-swap Γ₁ Γ₂ Γ₃ rewrite ++-assoc Γ₂ Γ₁ Γ₃ | ++-comm Γ₂ Γ₁ = refl

{-
  zero-cons : ∀ {A} (Δ) (Γ : Context Δ) → zeroCtx (A ∷ Δ) ≡ (zero' ** Γ) ,:⟨ zero' ⟩ A
  zero-cons d g = refl

  {-# REWRITE zero-cons #-}

-}
  {-# REWRITE one-** #-}
  {-# REWRITE ++-swap #-}
  -- {-# REWRITE <>-identity #-}
  -- {-# REWRITE ++-comm #-}
  -- {-# REWRITE ++-assoc #-}
  


  data CEmpty : ∀ {Δ : List Type} → Context Δ → Set where
    Ø-empty : CEmpty Ø
    ,-empty : ∀ {Δ : List Type} {Γ₁ : Context Δ} {A : Type}
              → CEmpty Γ₁
              ---------
              → CEmpty (Γ₁ ,:⟨ zero' ⟩ A)

  empty-concat : ∀ {Δ₁ Δ₂} {Γ₁ : Context Δ₁} {Γ₂ : Context Δ₂}
               → CEmpty (Γ₂ <> Γ₁)
               → CEmpty Γ₁ × CEmpty Γ₂
  empty-concat {Γ₁ = Ø} {Γ₂ = Γ₂} emp = Ø-empty , emp
  empty-concat {Γ₁ = Γ₁ ,:⟨ .zero' ⟩ A} {Γ₂ = Γ₂} (,-empty emp)
               with empty-concat {Γ₂ = Γ₂} emp
  ...             | l , r = ,-empty l , r

  postulate
    empty-concat2 :  ∀ {Δ₁ Δ₂} {Γ₁ : Context Δ₁} {Γ₂ : Context Δ₂}
                → CEmpty Γ₁
                → CEmpty Γ₂
                → CEmpty (Γ₂ <> Γ₁)


  empty-zeroCtx : ∀ {Δ} {Γ : Context Δ} → CEmpty Γ → Γ ≡ zeroCtx Δ
  empty-zeroCtx {_} {.Ø} Ø-empty = refl
  empty-zeroCtx {_} {.(_ ,:⟨ zero' ⟩ _)} (,-empty emp) rewrite empty-zeroCtx emp = refl

  
{-}
  empty-zeroctx : ∀ {Δ} {Γ : Context Δ} → Γ ≡ zeroCtx Δ → CEmpty Γ
  empty-zeroctx {Γ = Ø} eq = Ø-empty
  empty-zeroctx {Γ = Γ ,:⟨ x ⟩ A} eq = {!!}
-}
  -- LOOKUP
  data _∋_ : ∀ {Δ} → Context Δ → Type → Set₁ where

    Zero : ∀ {Δ} {Γ : Context Δ} {A}
         → CEmpty Γ
           -------
         → (Γ ,:⟨ one' ⟩ A) ∋ A    -- only allow empty for simplicity,
                              -- can introduce more via weakening

    S_ : ∀ {Δ} {Γ : Context Δ} {A B}
       → Γ ∋ A
         --------
       → (Γ ,:⟨ zero' ⟩ B) ∋ A

  infix 5 _∋_

  -- Z : ∀ {Δ} {Γ : Context Δ} {A}
  --     -------
  --   → (zero' ** Γ ,:⟨ one' ⟩ A) ∋ A    -- only allow empty for simplicity,
  -- Z {Γ = Γ} = Zero {Γ = Γ} refl

{-
  lookup : ∀ {Δ} → Context Δ → ℕ → Type
  lookup (Γ ,:⟨ one' ⟩ A) zero     =  A
  lookup (Γ ,:⟨ zero' ⟩ _) (suc n)  =  lookup Γ n
  lookup ∅       _        =  ⊥-elim impossible
    where postulate impossible : ⊥

  count : ∀ {Δ} {Γ : Context Δ} → (n : ℕ) → Γ ∋ lookup Γ n
  count {Γ = Γ ,:⟨ one' ⟩ A} 0 = Z
-}

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

    unitP : ∀ {Δ} {θ : Context Δ} Γ -- changed to allow zeroed out context
           → θ ≡ zero' ** Γ
           → θ ⊢ Unit

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

  -- needed to refactor some terms to have proofs passed in (for subst)
  -- but step relation doesn't require these proofs
  _·_ : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A B q}
      → Γ₁ ⊢ A -⟨ q ⟩→ B
      → Γ₂ ⊢ A
        ------
      → q ** Γ₂ ++ Γ₁ ⊢ B
  a · b = appP refl a b

  unit : ∀ {Δ} {Γ : Context Δ} -- changed to allow zeroed out context
       → (zero' ** Γ) ⊢ Unit
  unit {Γ = Γ} = unitP Γ refl

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


{-
  ext : ∀ {Δ} {Γ : Context Δ} {q}
    → (∀ {A C} → Γ ∋ A → Γ ,:⟨ zero' ⟩ C ∋ A)
    → (∀ {A B C} → Γ ,:⟨ q ⟩ B ∋ A → Γ ,:⟨ zero' ⟩ C ,:⟨ q ⟩ B ∋ A)
  ext {Γ = Γ} p {C = C} Z = Z {Γ = Γ ,:⟨ zero' ⟩ C}
  ext p (S v) = S (p v)

  rename : ∀ {Δ} {Γ : Context Δ}
    → (∀ {A C} → Γ ∋ A → Γ ,:⟨ zero' ⟩ C ∋ A)
    → (∀ {A C} → Γ ⊢ A → Γ ,:⟨ zero' ⟩ C ⊢ A)
  rename f (` x) = ` f x
  rename f (ƛ:⟨ q ⟩ A ⇒ a) = ƛ:⟨ q ⟩ A ⇒ {!!}
  rename f (a · a₁) = {!!}
  rename f unit = {!!}
  rename f (let-unit≔ a in' a₁) = {!!}
  rename f (box⟨ q ⟩ a) = {!!}
  rename f (let-box≔ a in' a₁) = {!!}
  rename f ⟨ a , a₁ ⟩ = {!!}
  rename f (let⟨,⟩≔ a in' a₁) = {!!}
  rename f (inj₁ a) = {!!}
  rename f (inj₂ a) = {!!}
  rename f (case⟨ q ⟩ a of a₁ || a₂) = {!!}


  -- substitution
  subst : ∀ {Δ} {Γ₁ Γ₂ : Context Δ}
    → (∀ {A} → Γ₁ ∋ A → Γ₂ ⊢ A)
    → (∀ {A} → Γ₁ ⊢ A → Γ₂ ⊢ A)
  subst f (` x) = f x
  subst f (ƛ:⟨ q ⟩ A ⇒ a) = {!!}
  subst f (a · a₁) = {!!}
  subst f unit = {!!}
  subst f (let-unit≔ a in' a₁) = {!!}
  subst f (box⟨ q ⟩ a) = {!!}
  subst f (let-box≔ a in' a₁) = {!!}
  subst f ⟨ a , a₁ ⟩ = {!!}
  subst f (let⟨,⟩≔ a in' a₁) = {!!}
  subst f (inj₁ a) = {!!}
  subst f (inj₂ a) = {!!}
  subst f (case⟨ q ⟩ a of a₁ || a₂) = {!!}
  -}
{-
  var-eq : ∀ {Δ} {Γ : Context Δ} {A} → ℕ → Γ ∋ A → Bool
  var-eq zero Z = true
  var-eq (suc n) (S v) = var-eq n v
  var-eq _ _ = false -}

  subst-var : ∀ {Δ₁ Δ₂} {Γ₁ : Context Δ₁} {Γ₂ : Context Δ₂} {Γ₃ : Context (Δ₁ <>' Δ₂)} {A B q}
            → Γ₂ ,:⟨ q ⟩ B <> Γ₁ ∋ A
            → (Γ₃ ⊢ B)
              ---------
            → q ** Γ₃ ++ (Γ₂ <> Γ₁) ⊢ A
  subst-var {Γ₁ = Ø} (Zero emp) s rewrite empty-zeroCtx emp = s
  subst-var {Γ₁ = Ø} (S x) s = ` x
  subst-var {Δ₁} {Γ₁ = Γ₁' ,:⟨ .one' ⟩ A} (Zero emp) s rewrite ((proj₁ +'-identity) one')
            with empty-concat {Γ₁ = Γ₁'} emp
  ...       | l , ,-empty r = ` {!Zero (empty-concat2 l r)!}
  subst-var {Γ₁ = Γ₁ ,:⟨ .(POSemiring.zero' mod) ⟩ A} (S x) s = {!!}

  subst : ∀ {Δ₁ Δ₂} {Γ₁ : Context Δ₁} {Γ₂ : Context Δ₂} {Γ₃ : Context (Δ₁ <>' Δ₂)} {A B q}
          (var : ℕ) {ev : length Δ₁ ≡ var}
        → Γ₂ ,:⟨ q ⟩ B <> Γ₁ ⊢ A
        → (Γ₃ ⊢ B)
          ---------
        → q ** Γ₃ ++ (Γ₂ <> Γ₁) ⊢ A
  subst v (` x) s = subst-var x s
  subst v (ƛ:⟨ q₁ ⟩ A ⇒ a) s = {!!}
  subst v (appP x a a₁) s = {!!}
  subst v (unitP Γ x) s = {!!}
  subst v (unitElimP x a a₁) s = {!!}
  subst v (boxP q₁ x a) s = {!!}
  subst v (boxElimP x a a₁) s = {!!}
  subst v (pairP x a a₁) s = {!!}
  subst v (pairElimP x a a₁) s = {!!}
  subst v (inj₁ a) s = {!!}
  subst v (inj₂ a) s = {!!}
  subst v (sumElimP q₁ x a a₁ a₂) s = {!!}

  _[_] : ∀ {Δ} {Γ₁ Γ₂ : Context Δ} {A B q} → (Γ₁ ,:⟨ q ⟩ B ⊢ A) → (Γ₂ ⊢ B) → q ** Γ₂ ++ Γ₁ ⊢ A
  _[_] = {!!}


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

```

## Proofs

```


```

## Examples

```
open Language {ℕ} {{nat-pos}}

-- example : Ø ⊢ Unit
-- example = (ƛ:⟨ 1 ⟩ Unit ⇒ (` Z {Γ = Ø})) · unit {Γ = Ø}
-- example = (ƛ:⟨ 1 ⟩ Unit ⇒ (` Z)) · unit
{-
not : Ø ⊢ Unit ⊕ Unit -⟨ 1 ⟩→ Unit ⊕ Unit
not = ƛ:⟨ 1 ⟩ Unit ⊕ Unit ⇒ (case⟨ 1 ⟩ ` Z of
  ƛ:⟨ 1 ⟩ Unit ⇒ (inj₂ (` Z))
  || (ƛ:⟨ 1 ⟩ Unit ⇒ (inj₁ (` Z)) ))
-}

```

