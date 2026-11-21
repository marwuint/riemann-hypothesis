import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfCo

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct

theorem isReduced_tens_field (F E C : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Field C] [Algebra F C] : IsReduced (C ⊗[F] E) := by
  have : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  exact Algebra.FormallyUnramified.isReduced_of_field C (C ⊗[F] E)

end PI.VolStabSW
