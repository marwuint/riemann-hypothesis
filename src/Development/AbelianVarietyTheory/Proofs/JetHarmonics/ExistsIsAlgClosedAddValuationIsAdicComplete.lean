import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNnrealValuationOfAddValuation

namespace GlobalTheory

open scoped NNReal

theorem expNegTop_inj_of_eq {a b : WithTop ℚ} (h : expNegTop a = expNegTop b) : a = b :=
  le_antisymm ((expNegTop_le_iff _ _).1 h.ge) ((expNegTop_le_iff _ _).1 h.le)

noncomputable def expNegAbsoluteValue {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) :
    AbsoluteValue F ℝ where
  toFun x := (expNegValuation v x : ℝ)
  map_mul' x y := by rw [map_mul, NNReal.coe_mul]
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by rw [NNReal.coe_eq_zero, Valuation.zero_iff]
  add_le' x y := by
    have h := (expNegValuation v).map_add x y
    have h' : expNegValuation v (x + y) ≤ expNegValuation v x + expNegValuation v y :=
      h.trans (max_le le_self_add le_add_self)
    exact_mod_cast h'

theorem isNonarchimedean_expNegAbsoluteValue {F : Type} [Field F]
    (v : AddValuation F (WithTop ℚ)) : IsNonarchimedean (expNegAbsoluteValue v) := by
  intro x y
  have h := (expNegValuation v).map_add x y
  change ((expNegValuation v (x + y) : ℝ≥0) : ℝ) ≤
    max ((expNegValuation v x : ℝ≥0) : ℝ) ((expNegValuation v y : ℝ≥0) : ℝ)
  exact_mod_cast h

theorem exists_norm_eq_of_completion {K : Type*} [NormedField K] [IsUltrametricDist K]
    (x : UniformSpace.Completion K) : ∃ y : K, ‖x‖ = ‖y‖ := by
  haveI : IsUltrametricDist (UniformSpace.Completion K) := IsUltrametricDist.of_normedAlgebra K
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp⟩
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.1 (UniformSpace.Completion.denseRange_coe (α := K)) x
    ‖x‖ (norm_pos_iff.2 hx)
  refine ⟨y, ?_⟩
  rw [← UniformSpace.Completion.norm_coe y]
  rw [dist_comm, dist_eq_norm] at hy
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x) (y := y - x) hy.ne'
  rw [add_sub_cancel, max_eq_left hy.le] at h
  exact h.symm

theorem exists_addValuation_expNegTop_eq_nnnorm {C : Type} [NormedField C] [IsUltrametricDist C]
    (h : ∀ x : C, ∃ t : WithTop ℚ, expNegTop t = ‖x‖₊) :
    ∃ v : AddValuation C (WithTop ℚ), ∀ x, expNegTop (v x) = ‖x‖₊ := by
  choose f hf using h
  refine ⟨AddValuation.of f ?_ ?_ ?_ ?_, hf⟩
  · apply expNegTop_inj_of_eq
    rw [hf, nnnorm_zero, expNegTop_top]
  · apply expNegTop_inj_of_eq
    rw [hf, nnnorm_one, expNegTop_zero]
  · intro x y
    rcases le_max_iff.1 (IsUltrametricDist.nnnorm_add_le_max x y) with h | h
    · exact min_le_of_left_le ((expNegTop_le_iff _ _).1 (by rwa [hf, hf]))
    · exact min_le_of_right_le ((expNegTop_le_iff _ _).1 (by rwa [hf, hf]))
  · intro x y
    apply expNegTop_inj_of_eq
    rw [expNegTop_add, hf, hf, hf, nnnorm_mul]

end GlobalTheory
