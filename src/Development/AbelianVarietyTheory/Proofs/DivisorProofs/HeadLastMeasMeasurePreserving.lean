import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadLApply
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm GlobalTheory.LocFub

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocFub

def headLastIsom (n : ℕ) : V (n + 1) →ₗᵢ[ℂ] WithLp 2 (V n × ℂ) where
  toLinearMap := (WithLp.linearEquiv 2 ℂ (V n × ℂ)).symm.toLinearMap ∘ₗ
    LinearMap.prod (headL n).toLinearMap ((EuclideanSpace.proj (Fin.last n) : V (n + 1) →L[ℂ] ℂ).toLinearMap)
  norm_map' v := by
    have h : ‖(WithLp.toLp 2 (headL n v, v (Fin.last n)) : WithLp 2 (V n × ℂ))‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fin.sum_univ_castSucc]
      simp [headL_apply]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem headLastIsom_apply (n : ℕ) (v : V (n + 1)) :
    headLastIsom n v = WithLp.toLp 2 (headL n v, v (Fin.last n)) := rfl

theorem headLastIsom_surjective (n : ℕ) : Function.Surjective (headLastIsom n) := by
  intro p
  obtain ⟨q, rfl⟩ : ∃ q, p = WithLp.toLp 2 q := ⟨WithLp.ofLp p, (WithLp.toLp_ofLp (p := 2) p).symm⟩
  refine ⟨WithLp.toLp 2 (Fin.snoc (α := fun _ => ℂ) (WithLp.ofLp q.1) q.2), ?_⟩
  rw [headLastIsom_apply]
  congr 1
  ext
  · simp [headL_apply]
  · simp

def headLastMeas (n : ℕ) : V (n + 1) ≃ᵐ V n × ℂ :=
  ((LinearIsometryEquiv.ofSurjective (headLastIsom n) (headLastIsom_surjective n)).toHomeomorph.toMeasurableEquiv).trans
    (MeasurableEquiv.toLp 2 (V n × ℂ)).symm

theorem headLastMeas_apply (n : ℕ) (v : V (n + 1)) : headLastMeas n v = (headL n v, v (Fin.last n)) := rfl

end GlobalTheory.LocFub
