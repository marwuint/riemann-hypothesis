import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

noncomputable section

open GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.UAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem dop_smul_comb (c : ℂ) (z : List (ℝ → GAd σ J) →₀ ℂ) (f : GAd σ J → ℂ) : dop (c • z) f = c • dop z f := by
  funext g
  simp only [dop, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _), Finsupp.mul_sum]
  simp only [smul_eq_mul, mul_assoc]

theorem IsCentral.smul {z : List (ℝ → GAd σ J) →₀ ℂ} (h : IsCentral σ J z) (c : ℂ) : IsCentral σ J (c • z) :=
  ⟨fun l hl γ hγ => h.1 l (Finsupp.support_smul hl) γ hγ, fun f hf a ha g => by
    simp only [dop_smul_comb, Pi.smul_apply, h.2 f hf a ha g]⟩

end GlobalTheory.UAut

end
