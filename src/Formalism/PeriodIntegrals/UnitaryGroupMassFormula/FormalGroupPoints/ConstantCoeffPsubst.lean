import Mathlib
import Formalism.PeriodIntegrals.FglPtW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem

noncomputable section

namespace PI.FglPtW.Wk

open PI.AddIntG.Wk

variable {K : Type*} [CommRing K]

theorem serOver_iff (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    SerOver S f ↔ f ∈ SerS S σ := by
  constructor
  · intro h
    refine ⟨fun n => ⟨MvPowerSeries.coeff n f, h n⟩, ?_⟩
    ext n
    first
    | rfl
    | simp [MvPowerSeries.coeff_map]
  · rintro ⟨g, rfl⟩ n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n g).2

end PI.FglPtW.Wk

end
