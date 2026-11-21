import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyHypothesesOfWorkingClassSevenDuties
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop

namespace GlobalTheory.Fc.Ind

def lowScalarPt (C CH : ℝ) : PtP := fun _ _ _ p => (p.S true).L6 (p.N C CH)

end GlobalTheory.Fc.Ind

end
