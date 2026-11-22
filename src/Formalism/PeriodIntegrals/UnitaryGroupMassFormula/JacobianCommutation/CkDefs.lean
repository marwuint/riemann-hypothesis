import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.StatementJF
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.JCC.Ck

def PartialsContinuousDifferentiable : Prop :=
  ∀ (d : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Set (Fin d → ℝ))
    (F : (Fin d → ℝ) → E) (D : Fin d → (Fin d → ℝ) → E),
    IsOpen V → (∀ i, ContinuousOn (D i) V) →
    (∀ y ∈ V, ∀ i, HasDerivAt (fun t : ℝ => F (y + t • Pi.single i (1 : ℝ))) (D i y) 0) →
    ∀ y ∈ V, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (D i y)) y

end PI.UnitaryGroupMassFormula.JCC.Ck
