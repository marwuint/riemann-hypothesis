import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialAdjointOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def CptInCC : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E) (C : Set (B.Mat k r)),
    B.CkOn ⊤ (B.GV k r) F → IsCompact C → (∀ g, g ∉ C → F g = 0) → ∀ (A : ℝ) (m : ℕ), B.InCC A m F

theorem thr_big (k r m : ℕ) :
    TransportedAlt k r (9 * ((r : ℝ) + 1) * ((((2 * r + k + 1 : ℕ) : ℝ)) ^ 2 + 1) + 6 * (r : ℝ) * (m : ℝ)) m := by
  unfold TransportedAlt
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) r, sq_nonneg (((2 * r + k + 1 : ℕ) : ℝ))]

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
