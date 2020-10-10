```
module QTT.Examples where

open import Data.Nat
open import Data.Nat.Properties using (+-comm; +-assoc; +-identity; *-assoc; *-identity; *-zero; ≤-reflexive; ≤-antisym; ≤-trans)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)

open import QTT.POSemiring


open import QTT.Definitions {ℕ} {{nat-pos}}


carith-test : ∀ {A} → (Ø ,:⟨ 2 ⟩ A) ≈ 1 ** (Ø ,:⟨ 1 ⟩ A) ++ (Ø ,:⟨ 1 ⟩ A)
carith-test = CArith-, CArith-Ø refl

csurr-test : ∀ {A B C} → (Ø ,:⟨ 1 ⟩ A ,:⟨ 2 ⟩ B ,:⟨ 1 ⟩ C) ≈ 2 * (Ø ,:⟨ 0 ⟩ A ,:⟨ 1 ⟩ B ,:⟨ 0 ⟩ C) # (Ø ,:⟨ 1 ⟩ A ,:⟨ 1 ⟩ C)
csurr-test = CSurr-S (CSurr-Z (,-empty Ø-empty))
```
