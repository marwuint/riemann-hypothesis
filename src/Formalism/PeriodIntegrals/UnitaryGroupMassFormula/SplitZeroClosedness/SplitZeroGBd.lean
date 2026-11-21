import Formalism.PeriodIntegrals.SplitZeroG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.CoeffPowMulPowEqZeroOfLt
import Formalism.PeriodIntegrals.BeDiagZp

noncomputable section

open Classical

namespace PI.SZGW

open PI.BeDiagZp

section Bridge

variable {p : ℕ} [Fact p.Prime] {σ : Type} (l ex ph : PowerSeries ℂ_[p])

theorem add_eq (a b : MvPowerSeries σ ℂ_[p]) : PI.SplitZeroG.add l ex a b = add l ex a b := rfl
theorem phAt_eq (a : MvPowerSeries σ ℂ_[p]) : PI.SplitZeroG.phAt ph a = phAt ph a := rfl
end Bridge

end PI.SZGW
