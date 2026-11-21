import ReciprocityTheory.SemistableReduction.LatSemiSt

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

abbrev QI : Type := CyclotomicField 4 ℚ

instance : IsCyclotomicExtension {4} ℚ QI := by
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  exact CyclotomicField.isCyclotomicExtension (n := 4) (K := ℚ)

instance : IsCMField QI :=
  IsCyclotomicExtension.Rat.isCMField QI (S := {4}) ⟨4, rfl, by norm_num⟩

end ReciprocityTheory.MultiplicativeHeights
