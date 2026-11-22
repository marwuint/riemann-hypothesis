import Mathlib
import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.L2.SG.ClassAct

open Formalism.UG Module

section Abstract

variable {G : Type} [Group G]

def Normalises (D K : Subgroup G) : Prop := ∀ δ ∈ D, ∀ κ ∈ K, δ * κ * δ⁻¹ ∈ K

theorem Normalises.inv_conj {D K : Subgroup G} (h : Normalises D K) {δ : G} (hδ : δ ∈ D) {κ : G}
    (hκ : κ ∈ K) : δ⁻¹ * κ * δ ∈ K := by
  have := h δ⁻¹ (D.inv_mem hδ) κ hκ
  simpa using this

end Abstract

end Formalism.L2.SG.ClassAct
