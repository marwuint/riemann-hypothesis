import Mathlib
import Formalism.PeriodIntegrals.IsoDualPair

noncomputable section

open scoped ComplexConjugate

namespace PI.IsoDualPair.UnitaryGroupMassFormula

open PI.IsoDualPair

instance finite_colChoice {Lt : Type} [Finite Lt] (N : ℕ) (nu : Lt → YoungDiagram) :
    Finite (ColChoice N nu) := by
  unfold ColChoice
  have : ∀ a, Finite (Fin a ↪o Fin N) := fun a =>
    Finite.of_injective (fun e : Fin a ↪o Fin N => (e : Fin a → Fin N))
      (fun e f h => DFunLike.coe_injective h)
  infer_instance

noncomputable instance fintype_colChoice {Lt : Type} [Finite Lt] (N : ℕ) (nu : Lt → YoungDiagram) :
    Fintype (ColChoice N nu) := Fintype.ofFinite _

variable {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram}

lemma prC_eq (φ ψ : LaC N nu) : prC φ ψ = ∑ J, φ J * ψ J := finsum_eq_sum_of_fintype _

lemma symmetricMeasure_l2Norm_eq_resolutionL2 (φ : LaC N nu) : l2 φ = ∑ J, ‖φ J‖ ^ 2 := finsum_eq_sum_of_fintype _

lemma cs (φ ψ : LaC N nu) : ‖prC φ ψ‖ ^ 2 ≤ l2 φ * l2 ψ := by
  rw [prC_eq, symmetricMeasure_l2Norm_eq_resolutionL2, symmetricMeasure_l2Norm_eq_resolutionL2]
  calc ‖∑ J, φ J * ψ J‖ ^ 2 ≤ (∑ J, ‖φ J‖ * ‖ψ J‖) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun J _ => norm_mul_le _ _)
    _ ≤ (∑ J, ‖φ J‖ ^ 2) * ∑ J, ‖ψ J‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

def pairL : Vnu N nu →ₗ[ℂ] Module.Dual ℂ (Vnu N nu) :=
  LinearMap.mk₂ ℂ (fun φ ψ : Vnu N nu => prC (φ : LaC N nu) ψ)
    (fun a b c => by
      simp only [Submodule.coe_add, prC_eq, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun J _ => by ring)
    (fun r a b => by
      simp only [Submodule.coe_smul, prC_eq, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun J _ => by ring)
    (fun a b c => by
      simp only [Submodule.coe_add, prC_eq, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun J _ => by ring)
    (fun r a b => by
      simp only [Submodule.coe_smul, prC_eq, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun J _ => by ring)

lemma pairL_apply (φ ψ : Vnu N nu) : pairL φ ψ = prC (φ : LaC N nu) ψ := rfl

end PI.IsoDualPair.UnitaryGroupMassFormula
