import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstY

noncomputable section

namespace PI.AprimeInfW

theorem jm_true (k : ℕ) : Formalism.REAL.Jm (fun _ : Fin k => true) = 1 := by
  simp [Formalism.REAL.Jm]

end PI.AprimeInfW
