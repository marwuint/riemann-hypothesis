import Formalism.PeriodIntegrals.BeDiagZp

noncomputable section

open Classical

namespace PI.BeDiagZp

open MvPowerSeries

namespace IntegralPowerSeriesBall

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem coeff_expMv (f : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff α (expMv f) =
      ∑ n ∈ Finset.range (Finsupp.degree α + 1), coeff α (f ^ n) / (n.factorial : ℂ_[p]) := rfl

end IntegralPowerSeriesBall

open IntegralPowerSeriesBall

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

end PI.BeDiagZp
