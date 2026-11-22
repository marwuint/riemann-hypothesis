import Mathlib
import Formalism.PeriodIntegrals.FglChordFactor
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AddIntG

noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

theorem isWq_bridge {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h : IsWq W wq) : PI.AddIntG.IsWq W wq := h

end PI.FglChordFactor.Wk
