import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.AddPreservesExpCongruence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.OrthogonalSplitPolarizationVanishes

noncomputable section

namespace PI.FglPhSplit.Wk

open PI.FglPhSplit

variable {K : Type} [Field K]

def AllIn (W : Subring K) {σ : Type} (F : MvPowerSeries σ K) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ W

theorem allIn_mul {W : Subring K} {σ : Type} {F G : MvPowerSeries σ K} (hF : AllIn W F)
    (hG : AllIn W G) : AllIn W (F * G) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hF _) (hG _)

theorem expMv_eq_subst [CharZero K] {σ : Type} {F : MvPowerSeries σ K}
    (hF : MvPowerSeries.constantCoeff F = 0) :
    expMv F = PowerSeries.subst F (PowerSeries.exp K) := by
  classical
  ext α
  have hs : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  rw [coeff_expMv, PowerSeries.coeff_subst hs,
    finsum_eq_sum_of_support_subset _ (s := Finset.range ((α.sum fun _ k => k) + 1)) ?_]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul, map_div₀, map_one, map_natCast]
    ring
  · intro n hn
    simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hn ⊢
    by_contra hc
    apply hn
    have hdeg : (α.sum fun _ k => k) = Finsupp.degree α := rfl
    rw [MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent (m := 1)
      (by rw [pow_one]; exact hF) (by omega), smul_zero]

section Rename₂

variable {ι ι' : Type} [Fintype ι]

theorem cc_psubst {σ : Type} (P : PowerSeries K) (hP : PowerSeries.constantCoeff P = 0)
    {y : MvPowerSeries σ K} (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst y P) = 0 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hy)]
  refine finsum_induction (p := fun x => x = 0) rfl (fun x z hx hz => by rw [hx, hz, add_zero]) fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hP, zero_smul]
  · rw [map_pow, hy, zero_pow hd.ne', smul_zero]

variable (g : Dat K) (hex0 : PowerSeries.constantCoeff g.ex = 0)
  (hl0 : PowerSeries.constantCoeff g.l = 0)
include hex0 hl0

end Rename₂

end PI.FglPhSplit.Wk

end
