import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityGalois
import GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityDescent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic GroundTheory.Arith.Abelian Module IntermediateField
open scoped nonZeroDivisors Real UpperHalfPlane

noncomputable section

abbrev cyclo3 : Type := CyclotomicField 3 ℚ

instance : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩

instance : IsCyclotomicExtension {3} ℚ cyclo3 := CyclotomicField.isCyclotomicExtension 3 ℚ

instance : NumberField cyclo3 := IsCyclotomicExtension.numberField {3} ℚ _

theorem finrank_cyclo3 : finrank ℚ cyclo3 = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 3) cyclo3
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

instance : Algebra.IsQuadraticExtension ℚ cyclo3 := ⟨finrank_cyclo3⟩

instance : IsTotallyComplex cyclo3 :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) cyclo3 (by norm_num)

instance : IsCyclotomicExtension {3 ^ (0 + 1)} ℚ cyclo3 := by
  simpa using (inferInstance : IsCyclotomicExtension {3} ℚ cyclo3)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
