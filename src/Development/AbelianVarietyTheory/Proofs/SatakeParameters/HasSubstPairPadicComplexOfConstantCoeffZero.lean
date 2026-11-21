import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogSubstExpSubOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvNegLogMvMul

noncomputable section

namespace GlobalTheory.ThBe0.Inhab

open MvPowerSeries Formalism.FG.InjVAux GlobalTheory.SubringSeries Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric GlobalTheory.ThBe0

variable {l : ℕ} [hl : Fact l.Prime] {κ : Type}

theorem coeff_logF_cases (n : ℕ) : (PowerSeries.coeff n (logF l) = 0 ∧ ∀ j, n ≠ l ^ (2 * j)) ∨
    ∃ j, n = l ^ (2 * j) := by
  by_cases h : ∃ j, n = l ^ (2 * j)
  · exact Or.inr h
  · push Not at h
    refine Or.inl ⟨?_, h⟩
    rw [logF, PowerSeries.coeff_mk]
    exact Finset.sum_eq_zero fun j _ => if_neg (h j)

theorem coeff_zero_logF : PowerSeries.coeff 0 (logF l) = 0 := by
  rcases coeff_logF_cases (l := l) 0 with h | ⟨j, h⟩
  · exact h.1
  · exact absurd h.symm (pow_ne_zero _ hl.out.ne_zero)

theorem cc_logF : PowerSeries.constantCoeff (logF l) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_logF]

theorem hasSubst_pair_padicComplex_of_constantCoeff_zero {x y : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    HasSubst (fun i : Fin 2 => if i = 0 then x else y) :=
  hasSubst_of_constantCoeff_zero fun i => by split_ifs <;> assumption

theorem subst_powerSeriesEvalTwoGroups {κ' : Type} {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a)
    {x y : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (E : MvPowerSeries (Fin 2) ℂ_[l]) : subst a (at2 E x y) = at2 E (subst a x) (subst a y) := by
  rw [at2, at2, subst_comp_subst_apply (hasSubst_pair_padicComplex_of_constantCoeff_zero hx hy) ha]
  congr 1
  funext i
  split_ifs <;> rfl

theorem subst_psubst {κ' : Type} {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a)
    {x : MvPowerSeries κ ℂ_[l]} (hx : constantCoeff x = 0) (f : PowerSeries ℂ_[l]) :
    subst a (f.subst x) = f.subst (subst a x) :=
  subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hx).const ha f

theorem cc_lg (k : κ) : constantCoeff (lg k : MvPowerSeries κ ℂ_[l]) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X k) _ cc_logF

end GlobalTheory.ThBe0.Inhab
