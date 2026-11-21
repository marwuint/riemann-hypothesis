import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice

noncomputable section

namespace ChkDv

open Formalism.BasicNotions

theorem c2E : PI.Dv.projection_lemma_base_level ↔ Formalism.MainNotions.PrimeDegreeVariant.projection_lemma_base_level := Iff.rfl
theorem c2dE : PI.Dv.gram_det_kernel_base_level ↔ Formalism.MainNotions.PrimeDegreeVariant.gram_det_kernel_base_level := Iff.rfl
theorem c7E : PI.Dv.division_rows_base_level ↔ Formalism.MainNotions.PrimeDegreeVariant.division_rows_base_level := Iff.rfl

end ChkDv
