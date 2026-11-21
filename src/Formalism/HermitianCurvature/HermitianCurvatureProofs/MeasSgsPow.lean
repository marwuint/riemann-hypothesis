import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralAdjoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem gN_mt_cont : Continuous fun x : Mt k r => B.gN (Matrix.of x) := by
  unfold B.gN
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))

theorem conv_pt (hNI : NormInv) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) {t g : Mx k r}
    (ht : t ∈ UH (Hpk k r)) (hg : g ∈ UH (Hpk k r)) :
    B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) := by
  obtain ⟨_, hmul, hinv⟩ := Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) (Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r)
  have htg : t⁻¹ * g ∈ UH (Hpk k r) := hmul _ (hinv t ht).2 _ hg
  have hA : 1 ≤ B.gN t := ((hNI k r).2 t ht).2
  have hG : 1 ≤ B.gN g := ((hNI k r).2 g hg).2
  have hC : 1 ≤ B.gN (t⁻¹ * g) := ((hNI k r).2 _ htg).2

  have hsub : B.gN g ≤ B.gN t * B.gN (t⁻¹ * g) := by
    have h1 : t * (t⁻¹ * g) = g := by
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ (hinv t ht).1, one_mul]
    calc B.gN g = B.gN (t * (t⁻¹ * g)) := by rw [h1]
      _ ≤ _ := (hNI k r).1 _ _
  have hA0 : 0 < B.gN t := by linarith
  have hC0 : 0 < B.gN (t⁻¹ * g) := by linarith
  have hG0 : 0 < B.gN g := by linarith
  have h1 : B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b) ≤ B.gN g ^ (-b) := by
    rw [← Real.mul_rpow hA0.le hC0.le, Real.rpow_neg (by positivity), Real.rpow_neg hG0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hG0 b) (Real.rpow_le_rpow hG0.le hsub hb)
  have h2 : B.gN (t⁻¹ * g) ^ (-a) ≤ B.gN (t⁻¹ * g) ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  calc B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-a)
      ≤ B.gN t ^ (-a) * B.gN (t⁻¹ * g) ^ (-b) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hA0.le _)
    _ = B.gN t ^ (b - a) * (B.gN t ^ (-b) * B.gN (t⁻¹ * g) ^ (-b)) := by
        rw [← mul_assoc, ← Real.rpow_add hA0, show b - a + -b = -a by ring]
    _ ≤ B.gN t ^ (b - a) * B.gN g ^ (-b) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hA0.le _)

end Formalism.FourierDecayAlt.P.S3dx6
