import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.EqZeroOfOppositeSign
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial
open scoped TensorProduct Pointwise

namespace GlobalTheory.CM.LatModel

abbrev CyclotomicFieldTwentyEight : Type := CyclotomicField 28 ℚ

instance isCyclotomicExtension_cyclotomicField28 : IsCyclotomicExtension {28} ℚ CyclotomicFieldTwentyEight := CyclotomicField.isCyclotomicExtension 28 ℚ

instance isCMField_cyclotomicField28 : IsCMField CyclotomicFieldTwentyEight := IsCyclotomicExtension.Rat.isCMField CyclotomicFieldTwentyEight (S := {28}) ⟨28, rfl, by norm_num⟩

end GlobalTheory.CM.LatModel
