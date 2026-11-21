import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeHermitianCombinationOfSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaugeHermitianCombination_of_steps : AddSt → ActSt → UnitSt → BiaddSt → FinSt := by
  exact @GlobalTheory.IsoTriv.HermRead.finSt_of
