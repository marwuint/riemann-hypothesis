import Mathlib
import Formalism.PeriodIntegrals.FglChordFactor
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AddIntG

noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

theorem isWq_bridge {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h : IsWq W wq) : PI.AddIntG.IsWq W wq := h

theorem flog_bridge {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    flog W wq = PI.AddIntG.flog W wq := rfl

theorem add_bridge {p : ℕ} [Fact p.Prime] {σ : Type*} (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) :
    add l ex a b = PI.AddIntG.add l ex a b := rfl

end PI.FglChordFactor.Wk
