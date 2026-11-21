import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EnvOfMat
import Formalism.HermitianCurvature.StatementB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Matrix

noncomputable section

namespace GlobalTheory.SOrb.CCBridge

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

lemma lin_bound {𝕜 L M : Type*} [RCLike 𝕜] [NormedAddCommGroup L] [NormedSpace 𝕜 L] [FiniteDimensional 𝕜 L]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] (u : L →ₗ[𝕜] M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖u x‖ ≤ C * ‖x‖ :=
  ⟨‖LinearMap.toContinuousLinearMap u‖, norm_nonneg _, (LinearMap.toContinuousLinearMap u).le_opNorm⟩

def opEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv

lemma opn_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : opn g = ‖opEquiv n g‖ := rfl

section Frob

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

lemma opn_frob_compare (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, opn g ≤ K * ‖g‖ ∧ ‖g‖ ≤ K * opn g := by
  obtain ⟨a, ha, h3⟩ := lin_bound (opEquiv n).toLinearMap
  obtain ⟨b, hb, h4⟩ := lin_bound (opEquiv n).symm.toLinearMap
  refine ⟨1 + a + b, by positivity, fun g => ?_⟩
  have h3 : ‖opEquiv n g‖ ≤ a * ‖g‖ := h3 g
  have h4 : ‖(opEquiv n).symm (opEquiv n g)‖ ≤ b * ‖opEquiv n g‖ := h4 (opEquiv n g)
  rw [LinearEquiv.symm_apply_apply] at h4
  rw [opn_eq]
  have := norm_nonneg g
  have := norm_nonneg (opEquiv n g)
  constructor <;> nlinarith

lemma opn_gN_compare (k r : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ g : Mat k r, opn g ≤ K * gN g ∧ gN g ≤ K * opn g := by
  obtain ⟨K, hK, h⟩ := opn_frob_compare (2 * r + k + 1)
  exact ⟨K, hK, fun g => by rw [gN_eq_frob]; exact h g⟩

end Frob

lemma rpow_compare {K : ℝ} (hK : 0 < K) (A : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h1 : x ≤ K * y)
    (h2 : y ≤ K * x) : x ^ A ≤ K ^ |A| * y ^ A := by
  rcases le_total 0 A with hA | hA
  · rw [abs_of_nonneg hA, ← Real.mul_rpow hK.le hy.le]
    exact Real.rpow_le_rpow hx.le h1 hA
  · have h3 : y / K ≤ x := by rw [div_le_iff₀ hK]; linarith
    have := Real.rpow_le_rpow_of_nonpos (by positivity) h3 hA
    rw [Real.div_rpow hy.le hK.le] at this
    rw [abs_of_nonpos hA, Real.rpow_neg hK.le]
    calc x ^ A ≤ y ^ A / K ^ A := this
      _ = _ := by ring

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end GlobalTheory.SOrb.CCBridge

namespace GlobalTheory.SOrb

end GlobalTheory.SOrb
