import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Polynomial

noncomputable section

variable (p : ℕ) [Fact p.Prime]

abbrev Q0 : IntermediateField ℚ_[p] (PadicAlgCl p) := ⊥

variable {p}

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
