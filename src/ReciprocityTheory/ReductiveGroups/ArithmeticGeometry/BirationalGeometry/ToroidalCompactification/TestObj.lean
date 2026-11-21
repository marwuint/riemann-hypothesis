import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma tensor_punit_eq_zero (x : ℝ ⊗[ℤ] PUnit.{1}) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul r u => rw [Subsingleton.elim u 0, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

instance : Subsingleton (ℝ ⊗[ℤ] PUnit.{1}) :=
  ⟨fun a b => by rw [tensor_punit_eq_zero a, tensor_punit_eq_zero b]⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test
