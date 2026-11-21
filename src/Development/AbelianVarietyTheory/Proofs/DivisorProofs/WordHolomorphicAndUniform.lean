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

theorem summable_pair (a : lp (fun _ : ℕ => ℂ) 1) {y : ℕ → ℂ} {M : ℝ} (hy : ∀ n, ‖y n‖ ≤ M) :
    Summable fun n => a n * y n :=
  Summable.of_norm_bounded ((summable_lp_one a).mul_right M) fun n => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hy n) (norm_nonneg _)

theorem norm_pair_le (a : lp (fun _ : ℕ => ℂ) 1) {y : ℕ → ℂ} {M : ℝ} (hy : ∀ n, ‖y n‖ ≤ M) :
    ‖∑' n, a n * y n‖ ≤ ‖a‖ * M := by
  rw [norm_lp_one]
  refine tsum_of_norm_bounded ((summable_lp_one a).hasSum.mul_right M) fun n => ?_
  rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hy n) (norm_nonneg _)

def pairLin {y : ℕ → ℂ} {M : ℝ} (hy : ∀ n, ‖y n‖ ≤ M) : lp (fun _ : ℕ => ℂ) 1 →ₗ[ℂ] ℂ where
  toFun a := ∑' n, a n * y n
  map_add' a b := by
    have e : ∀ n, (a + b : lp (fun _ : ℕ => ℂ) 1) n * y n = a n * y n + b n * y n := fun n => by
      rw [lp.coeFn_add, Pi.add_apply, add_mul]
    simp only [e]
    exact (summable_pair a hy).tsum_add (summable_pair b hy)
  map_smul' c a := by
    have e : ∀ n, (c • a : lp (fun _ : ℕ => ℂ) 1) n * y n = c * (a n * y n) := fun n => by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    simp only [e, RingHom.id_apply, smul_eq_mul]
    exact tsum_mul_left

def pairCLM {y : ℕ → ℂ} {M : ℝ} (hy : ∀ n, ‖y n‖ ≤ M) : lp (fun _ : ℕ => ℂ) 1 →L[ℂ] ℂ :=
  (pairLin hy).mkContinuous M fun a => by rw [mul_comm]; exact norm_pair_le a hy

theorem pairCLM_apply {y : ℕ → ℂ} {M : ℝ} (hy : ∀ n, ‖y n‖ ≤ M) (a : lp (fun _ : ℕ => ℂ) 1) :
    pairCLM hy a = ∑' n, a n * y n := rfl

end GlobalTheory.WeakHolFamily

namespace GlobalTheory.WeakHolFamily

end GlobalTheory.WeakHolFamily
