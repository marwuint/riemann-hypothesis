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

def PhVF (l ex ph : PowerSeries ℂ_[p]) {κ T σ : Type} [Fintype κ] [Fintype T]
    (B : T → κ → ℂ_[p] × ℂ_[p]) (w : T → MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  ∑ k, phAt ph (lin l ex (fun e => (B e k).1) w)

theorem PhOn_eq {κ T : Type} [Fintype κ] [Fintype T] (B : T → κ → ℂ_[p] × ℂ_[p]) :
    PhOn l ex ph B = PhVF l ex ph B (fun e => X e) := rfl

end PI.UnitaryGroupMassFormula.SDiffGram

end
