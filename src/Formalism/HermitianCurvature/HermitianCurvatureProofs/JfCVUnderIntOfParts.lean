import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem mdim0 : Q.mdim k r 0 = 2 * r + k + 1 := by
  rfl

end Formalism.FourierDecayAlt.P.JFxB

