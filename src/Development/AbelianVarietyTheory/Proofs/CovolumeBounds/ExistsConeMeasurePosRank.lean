import Mathlib
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmHalfIntegralGeneratorMemAlgebraicClosure

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open scoped ENNReal ComplexOrder ComplexConjugate

noncomputable section

namespace GlobalTheory.HCXi.ConeOne

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8

def radMeas (N : ℕ) : Measure ℂ := (volume : Measure ℂ).withDensity fun c => ENNReal.ofReal (‖c‖ ^ (2 * N))

instance (N : ℕ) : SFinite (radMeas N) := by unfold radMeas; infer_instance

def par (k r' : ℕ) (p : ℂ × HPar k r') : Fin (2 * (1 + r') + k + 1) → ℂ :=
  p.1 • (es0 k r' + liftVec k 1 r' p.2.1 + hb k r' p.2.1 p.2.2 • e0 k r')

lemma cone_def (k r' : ℕ) :
    coneMeas k r' = ((radMeas (2 * r' + k + 1)).prod (volume : Measure (HPar k r'))).map (par k r') := rfl

instance hparSFinite (k r' : ℕ) : SFinite (volume : Measure (HPar k r')) := by
  rw [Measure.volume_eq_prod]; infer_instance

end GlobalTheory.HCXi.ConeOne

namespace GlobalTheory.HCXi

end GlobalTheory.HCXi
