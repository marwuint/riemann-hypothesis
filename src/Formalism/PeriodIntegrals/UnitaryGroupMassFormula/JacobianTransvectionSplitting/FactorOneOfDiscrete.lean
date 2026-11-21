import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.DiscreteHaar

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace PI.NglqJacSplitW

section Mod

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [LocallyCompactSpace F]

theorem modF_of_ne {a : F} (h : a ≠ 0) :
    modF F a = ((distribHaarChar F (Units.mk0 a h) : ℝ≥0) : ℝ≥0∞) := by
  rw [modF, dif_neg h]

theorem modF_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : modF F (a * b) = modF F a * modF F b := by
  rw [modF_of_ne (mul_ne_zero ha hb), modF_of_ne ha, modF_of_ne hb,
    show Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb from Units.ext rfl, map_mul]
  push_cast
  rfl

end Mod

end PI.NglqJacSplitW
