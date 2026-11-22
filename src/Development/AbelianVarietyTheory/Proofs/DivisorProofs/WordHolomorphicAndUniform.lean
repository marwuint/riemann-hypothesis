import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal ContDiff

noncomputable section
namespace GlobalTheory.WeakHolFamily

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem norm_lp_one (a : lp (fun _ : ℕ => ℂ) 1) : ‖a‖ = ∑' n, ‖a n‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp)]; simp

theorem summable_lp_one (a : lp (fun _ : ℕ => ℂ) 1) : Summable fun n => ‖a n‖ := by
  simpa using (lp.memℓp a).summable (by simp)

theorem norm_pair_le (a : lp (fun _ : ℕ => ℂ) 1) {y : ℕ → ℂ} {M : ℝ} (hy : ∀ n, ‖y n‖ ≤ M) :
    ‖∑' n, a n * y n‖ ≤ ‖a‖ * M := by
  rw [norm_lp_one]
  refine tsum_of_norm_bounded ((summable_lp_one a).hasSum.mul_right M) fun n => ?_
  rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hy n) (norm_nonneg _)

end GlobalTheory.WeakHolFamily

namespace GlobalTheory.WeakHolFamily

end GlobalTheory.WeakHolFamily
