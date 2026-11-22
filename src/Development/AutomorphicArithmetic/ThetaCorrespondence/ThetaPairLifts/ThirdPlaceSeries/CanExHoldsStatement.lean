import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalExistence
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanExHolds

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigOn_canEx : _root_.GlobalTheory.BigOn.Exp.CanonicalExists := GlobalTheory.BigOn.Exp.canEx_holds_alt
end
