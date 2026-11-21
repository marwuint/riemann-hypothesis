import Mathlib
import Formalism.PeriodIntegrals.JetsPhW
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InverseOmegaHolds

noncomputable section

open Classical

namespace PI.JetsPhW.Inv

variable {p : ℕ} [Fact p.Prime]

theorem dX_eq_derivative (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative ℂ_[p] f := by
  ext n
  simp only [dX, PowerSeries.coeff_mk, PowerSeries.coeff_derivative]
  ring

theorem inverse_omega_holds : InvOmega :=
  _root_.UpperTheory.Reformulated.B.Gwa1.inverse_omega_holds

end PI.JetsPhW.Inv
