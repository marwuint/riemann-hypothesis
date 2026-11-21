import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import GroundTheory.ArithmeticGeometry.IwasawaModules.SpanFinrankMaximalIdealLeTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsComponentDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByFormField
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PExistsForm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleSupport

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace VerticalDivisorsCommuting

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem intNum_snoc {F : Type u} [Field F] (V : Ideal (MRing ι F)) {n : ℕ} (L : Fin n → K → ℤ)
    (b : K → ℤ) :
    intNum F V (Fin.snoc (α := fun _ => K → ℤ) L b) = intNum F V (Matrix.vecCons b L) := by
  rw [← CutByFormField.vecCons_comp_finRotate]
  exact FieldNumbers.IntNumSymm.proof F K ι V (n + 1) _ _

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end VerticalDivisorsCommuting

end

end GroundTheory.Heights₂.Heights.NumbersDVR
