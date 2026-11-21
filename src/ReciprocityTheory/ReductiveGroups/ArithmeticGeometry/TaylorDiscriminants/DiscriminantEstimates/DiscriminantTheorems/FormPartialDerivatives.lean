import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.PerpVecPerpSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.PerpendicularDeterminants.PerpVecOfPerp

theorem perpendicular_vector_exists : ReciprocityTheory.ChartRestriction.G.TB.PerpVecSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.PerpVecSt
  intro R _ V _ _ p h e e' g c
  exact PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_perp R V p h e e' g c

theorem perpendicular_vector_perp : ReciprocityTheory.ChartRestriction.G.TB.PerpVecPerpSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.PerpVecPerpSt
  intro R _ V _ _ p h e e' g hg
  exact PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_of_perp R V p h e e' g hg
