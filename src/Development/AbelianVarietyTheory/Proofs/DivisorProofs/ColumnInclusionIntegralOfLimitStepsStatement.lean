import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionIntegralOfLimitSteps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnInclusionIntegral_of_limitSteps : LimActSt → LimPtSt → LimFrameSt → InclSt := by
  exact @GlobalTheory.IsoTriv.Incl.inclSt_of_lim
