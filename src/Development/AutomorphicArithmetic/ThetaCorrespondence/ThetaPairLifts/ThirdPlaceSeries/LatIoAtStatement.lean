import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntersectionAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatIoAt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latIoAt' : _root_.GlobalTheory.BigOn.Exp.SerBase.LatticeInclusionAt := by
  exact @_root_.GlobalTheory.BigOn.Exp.SerBase.latIoAt_alt
end
