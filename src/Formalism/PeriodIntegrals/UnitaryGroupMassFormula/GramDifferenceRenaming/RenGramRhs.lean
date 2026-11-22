import Formalism.PeriodIntegrals.FglGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualGramSubstitution.BeMulByZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.CoeffPowMulPowEqZero

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.SDiffGram

open PI.FglGram MvPowerSeries
open PI.UnitaryGroupMassFormula.PhDualGram (ren ren_apply ren_psubst ren_X ren_C simeq_ren cc_lin ren_lin ren_be ren_PhOn)
open PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram (Good simeq_iff_good good_add good_sub expMv_zero int_one)

variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}

end PI.UnitaryGroupMassFormula.SDiffGram

end
