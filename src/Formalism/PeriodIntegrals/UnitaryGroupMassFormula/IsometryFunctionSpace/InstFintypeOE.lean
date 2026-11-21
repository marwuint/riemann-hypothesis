import Mathlib
import Formalism.PeriodIntegrals.IsoFunV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryFunctionSpace.DetSubmatrixNoninj

open Matrix Finset MvPolynomial

noncomputable section

namespace PI.IsoFunVW

open PI.IsoFunV

noncomputable instance instFintypeOE (m n : ℕ) : Fintype (Fin m ↪o Fin n) :=
  @Fintype.ofFinite _ (finite_oe m n)

noncomputable instance instFintypeCC {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) : Fintype (ColChoice N nu) := by
  unfold ColChoice; infer_instance

def linW {σ : Type} (w : (σ →₀ ℕ) → ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun P := ∑ α ∈ P.support, coeff α P * w α
  map_add' P Q := by
    classical
    have key : ∀ (R : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ)), R.support ⊆ S →
        ∑ α ∈ R.support, coeff α R * w α = ∑ α ∈ S, coeff α R * w α := by
      intro R S hS
      refine Finset.sum_subset hS (fun α _ hα => ?_)
      rw [MvPolynomial.mem_support_iff, not_not] at hα
      simp [hα]
    rw [key (P + Q) (P.support ∪ Q.support) support_add,
      key P (P.support ∪ Q.support) subset_union_left,
      key Q (P.support ∪ Q.support) subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [coeff_add, add_mul]
  map_smul' c P := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine (Finset.sum_subset support_smul (fun α _ hα => ?_)).trans ?_
    · rw [MvPolynomial.mem_support_iff, not_not] at hα
      simp [hα]
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [coeff_smul, smul_eq_mul, mul_assoc]

theorem linW_apply {σ : Type} (w : (σ →₀ ℕ) → ℂ) (P : MvPolynomial σ ℂ) :
    linW w P = ∑ α ∈ P.support, coeff α P * w α := rfl

end PI.IsoFunVW

end
