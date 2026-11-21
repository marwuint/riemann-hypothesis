import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Formalism.LocalRingCardinality.DataNChTie
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
import Formalism.LocalToGlobal.IndefiniteReal.RealRec
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionFirst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionThird
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PNmjOfPDivOfClassSumPin

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pNmj_of_pDiv_classSumPin : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b → GlobalTheory.ExportPin.ClassSumPin b.pt → _root_.GlobalTheory.Fc.Ind.NormJumpPointSummands D O c b := by
  first | exact @_root_.GlobalTheory.Fc.Ind.pNmj_of_pDiv_of_classSumPin_alt | exact _root_.GlobalTheory.Fc.Ind.pNmj_of_pDiv_of_classSumPin_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.pNmj_of_pDiv_of_classSumPin_alt <;> assumption)
end
