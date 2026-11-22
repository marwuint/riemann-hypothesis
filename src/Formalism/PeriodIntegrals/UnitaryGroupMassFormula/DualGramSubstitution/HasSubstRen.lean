import Formalism.PeriodIntegrals.FglGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.ExpCongruenceExtendsToSum

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.PhDualGram

open PI.FglGram MvPowerSeries

variable {p : ℕ} [Fact p.Prime]

def Wp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

section Rename₂

variable {σ τ : Type} [Finite σ] (r : σ → τ)

theorem hasSubst_ren : HasSubst (fun s => (X (r s) : MvPowerSeries τ ℂ_[p])) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_X _)

def ren : MvPowerSeries σ ℂ_[p] →ₐ[ℂ_[p]] MvPowerSeries τ ℂ_[p] :=
  substAlgHom (hasSubst_ren r)

theorem ren_apply (F : MvPowerSeries σ ℂ_[p]) :
    ren r F = MvPowerSeries.subst (fun s => (X (r s) : MvPowerSeries τ ℂ_[p])) F :=
  substAlgHom_apply _ F

theorem ren_X (s : σ) : ren r (X s : MvPowerSeries σ ℂ_[p]) = X (r s) := by
  rw [ren_apply, MvPowerSeries.subst_X (hasSubst_ren r)]

theorem ren_C (c : ℂ_[p]) : ren r (C c : MvPowerSeries σ ℂ_[p]) = C c := by
  rw [ren_apply, MvPowerSeries.subst_C]

variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hl0 : PowerSeries.constantCoeff l = 0)

omit [Finite σ] in
include hl0 in
theorem cc_lin {ι' : Type} [Fintype ι'] (c : ι' → ℂ_[p]) (w : ι' → MvPowerSeries σ ℂ_[p])
    (hw : ∀ j, constantCoeff (w j) = 0) :
    constantCoeff (∑ j, C (c j) * lg l (w j)) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => by
    rw [map_mul, lg, PI.FglPhSplit.Wk.cc_psubst _ hl0 (hw j), mul_zero]

end Rename₂

end PI.UnitaryGroupMassFormula.PhDualGram

end
