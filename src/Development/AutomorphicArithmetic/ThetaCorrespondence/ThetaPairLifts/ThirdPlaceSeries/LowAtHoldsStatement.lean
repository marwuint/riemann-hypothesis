import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowWeightStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHolds

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowAt : _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace := GlobalTheory.BigOn.Exp.lowAt_holds_alt
end
