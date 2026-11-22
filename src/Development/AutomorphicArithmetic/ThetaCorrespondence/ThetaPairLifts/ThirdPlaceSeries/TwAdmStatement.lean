import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtComp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwAdm

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_admissible' : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt := GlobalTheory.BigOn.Exp.twAdm_alt
end
