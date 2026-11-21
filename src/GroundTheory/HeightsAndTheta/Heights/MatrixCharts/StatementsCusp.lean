import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def leadMinor {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (i : ℕ) : ℝ :=
  (Matrix.of fun a b : Fin i =>
    if h : (a : ℕ) < d ∧ (b : ℕ) < d then S ⟨a, h.1⟩ ⟨b, h.2⟩ else 0).det

end

end GroundTheory.Heights₂.Heights
