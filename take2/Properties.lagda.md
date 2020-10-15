```
open import QTT.POSemiring using (POSemiring)

module QTT.take2.Properties {R : Set} {{mod : POSemiring R}} where

open import QTT.take2.Definitions {R} {{mod}}


substitution : ∀ {Δ A B q} {Γ₁ Γ₂ Γ : QContext Δ} {a : Δ , B ⊢ A} {b : Δ ⊢ B}
             → Γ₁ ,⟨ q ⟩ B ⊨ a
             → Γ₂ ⊨ b
             → Γ ≈ q ⨂ Γ₂ ⨁ Γ₁
             → Γ ⊨ a [ b ]
substitution (QTT.take2.Definitions._⊨_.VarZ x) b eq = ?
substitution (QTT.take2.Definitions._⊨_.VarS a) b eq = ?
substitution (QTT.take2.Definitions._⊨_.Lambda a) b eq = ?
substitution (QTT.take2.Definitions._⊨_.App x a a₁) b eq = ?

```
