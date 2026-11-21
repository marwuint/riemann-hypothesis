import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasurePolarForm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvO

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperboloid_invariant_measure_polar_form : PI.RhsWLim.W.RI.HypQ := by
  exact @GlobalTheory.HyperboloidPolar.hypQ
