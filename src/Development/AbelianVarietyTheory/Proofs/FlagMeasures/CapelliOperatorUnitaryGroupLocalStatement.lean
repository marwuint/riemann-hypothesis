import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorUnitaryGroupLocal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_operator_unitaryGroup_local : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  exact @GlobalTheory.CapelliLocality.capelliH_local
