```
module QTT.take2.Examples where

open import Data.Nat
open import Data.Nat.Properties using (+-comm; +-assoc; +-identity; *-assoc; *-identity; *-zero; ≤-reflexive; ≤-antisym; ≤-trans)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)

open import QTT.POSemiring


open import QTT.take2.Definitions {ℕ} {{nat-pos}}

twoᶜ : ∀ {Δ A} → Δ ⊢ (A -⟨ 1 ⟩→ A) -⟨ 2 ⟩→ (A -⟨ 1 ⟩→ A)
twoᶜ {_} {A} = ƛ:⟨ 2 ⟩ (A -⟨ 1 ⟩→ A) ⇒ ƛ:⟨ 1 ⟩ A ⇒ (` (S Z) · (` (S Z) · ` Z))


twoc-quant : ∀ {A} → (Ø ⊨ ƛ:⟨ 2 ⟩ (A -⟨ 1 ⟩→ A) ⇒ ƛ:⟨ 1 ⟩ A ⇒ (` (S Z) · (` (S Z) · ` Z)))
twoc-quant {A} = Lambda (Lambda (App {A = A} (CArith-, (CArith-, (CArith-Emp Ø-empty) refl) refl) (VarS (VarZ {_} {Ø} Ø-empty)) (App (CArith-, (CArith-Emp ($-empty Ø-empty)) refl) (VarS (VarZ Ø-empty)) (VarZ {_} {Ø ,⟨ zero' ⟩ (A -⟨ 1 ⟩→ A)} ($-empty Ø-empty)))))


twoc-inner : ∀ {Δ A} → Δ , (A -⟨ 1 ⟩→ A) ⊢ A -⟨ 1 ⟩→ A
twoc-inner {_} {A} = ƛ:⟨ 1 ⟩ A ⇒ (` (S Z) · (` (S Z) · ` Z))

twoc-subst : (twoc-inner {∅} {Unit}) [ ` Z ] ≡ ` (S Z) · (` (S Z) · ` Z)
twoc-subst = ?
```
