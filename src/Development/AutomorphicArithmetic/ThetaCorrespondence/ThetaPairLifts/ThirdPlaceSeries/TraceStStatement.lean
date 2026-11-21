import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceSt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupLe_traceSt : _root_.GlobalTheory.BigOn.Exp.TupLe.TraceCondition := by
  exact @_root_.GlobalTheory.BigOn.Exp.TupLe.traceSt_alt
end
