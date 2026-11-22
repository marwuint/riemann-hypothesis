import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualGramSubstitution.HasSubstRen

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.PhDualGram

open PI.FglGram MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}

theorem cc_add (hex0 : PowerSeries.constantCoeff ex = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    {σ : Type} {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    constantCoeff (add l ex x y) = 0 := by
  unfold add pt lg
  exact PI.FglPhSplit.Wk.cc_psubst _ hex0 (by
    rw [map_add, PI.FglPhSplit.Wk.cc_psubst _ hl0 hx, PI.FglPhSplit.Wk.cc_psubst _ hl0 hy, add_zero])

end PI.UnitaryGroupMassFormula.PhDualGram

end
