import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.BoundsY
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix MCBounds
open scoped ComplexOrder

noncomputable section

theorem MCBounds.map_sub_smul_one {g : ℕ} (s : ℝ) (A : Matrix (Fin g) (Fin g) ℝ) :
    (A - s • (1 : Matrix (Fin g) (Fin g) ℝ)).map (fun x : ℝ => (x : ℂ)) =
      A.map (fun x : ℝ => (x : ℂ)) - (s : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ) := by
  ext j k
  by_cases h : j = k <;> simp [h]

theorem MCBounds.conj_sub_smul_one {g k : ℕ} (F : Matrix (Fin g) (Fin k) ℂ) (s : ℂ)
    (Z : Matrix (Fin g) (Fin g) ℂ) :
    Fᴴ * (Z - s • (1 : Matrix (Fin g) (Fin g) ℂ)) * F = Fᴴ * Z * F - s • (Fᴴ * F) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem MCBounds.re_det_ofReal_smul {k : ℕ} (s : ℝ) (H : Matrix (Fin k) (Fin k) ℂ) :
    ((s : ℂ) • H).det.re = s ^ k * H.det.re := by
  rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

end

end GroundTheory.Heights₂.Heights
