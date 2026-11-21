import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Kummer
import ReciprocityTheory.ClassFieldTheory.LocalClassField.FinCoh
import ReciprocityTheory.ClassFieldTheory.LocalClassField.EqZeroOfResEqZeroOfCoprime

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p}

scoped instance discreteTopology_muT (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (l : ℕ) [NeZero l] :
    DiscreteTopology (Kummer.muT p F l).V :=
  inferInstanceAs (DiscreteTopology (ZMod l))

end ReciprocityTheory.DiscreteGroups.LocalClassField
