import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchOfWeilRepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationEtaleOfQuadraticField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleOrbitalFourierRankOneTransfer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConstantStandardHermitianEqOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourierMatch_of_weilField : WeilField → ∀ r, FourierMatch r := fun h =>
  _root_.GlobalTheory.JR.fourierMatch_of_weil (_root_.GlobalTheory.JR.weilEt_of_weilField h) _root_.GlobalTheory.JR.RankOneTransfer.rankOne _root_.GlobalTheory.JR.gammaOne_holds

end GlobalTheory.JR
