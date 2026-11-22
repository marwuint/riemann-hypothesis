import Formalism.HermitianCurvature.CompositeFormulaOfDensities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSplitAssocMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HerClassesOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopDensNonnegOfKappa
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignedCoordinateEqSignSmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfWaveQQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvSelf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem sfinite_of_isHaarOn {k r : ℕ} (U : Set (B.Mat k r)) (μ : Measure (Mt k r)) (h : B.IsHaarOn U μ) :
    SFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

end Formalism.FourierDecayAlt.P5
