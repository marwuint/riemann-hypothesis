import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchingOfWeilField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSucc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSizeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConstantStandardHermitianEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationEtaleOfQuadraticField

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_of_weilField : WeilField → ∀ r, UnitMatch r := by
  intro hW r
  induction r with
  | zero => exact _root_.GlobalTheory.JR.SizeOne.unitMatch_zero
  | succ r ih => exact _root_.GlobalTheory.JR.UnitStep.unitMatch_succ (_root_.GlobalTheory.JR.weilEt_of_weilField hW) _root_.GlobalTheory.JR.gammaOne_holds r (_root_.GlobalTheory.JR.fourierMatch_of_weilField hW (r + 1)) ih

end GlobalTheory.JR
