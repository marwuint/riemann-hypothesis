import Formalism.GaussJetBounds.StatementN
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

section Exp

variable {K : Type u} [NormedField K] [CharZero K] {ι : Type} [Fintype ι]

lemma constantCoeff_mvExp (f : MvPowerSeries ι K) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (mvExp f) = 1 := by
  unfold mvExp
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    finsum_eq_single _ 0]
  · simp
  · intro n hn
    simp [hf, hn]

end Exp

end Formalism.DworkPowerSeriesWeights
