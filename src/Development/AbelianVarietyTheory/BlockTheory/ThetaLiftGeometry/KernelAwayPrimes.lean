import Mathlib
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalRingCardinality.DataKerP
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalToGlobal.Divisibility.CoefMod

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

def IntAt {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : ℂ) : Prop :=
  a ∈ Qbar ∧ ‖lamC lam a‖ ≤ 1

variable {D : D7}

theorem exp_le (D : D7) (i : ℕ) (hi : i < D.R.m) :
    D.R.f * D.R.N i * D.R.N (i + 1) ≤ D.R.f * D.R.N D.R.m * (D.R.N D.R.m + D.R.t) := by
  have h1 : D.R.N i ≤ D.R.N D.R.m := by
    unfold Ranks.N; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _
  have h2 : D.R.N (i + 1) ≤ D.R.N D.R.m + D.R.t := by
    unfold Ranks.N
    exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _) (Nat.le_add_right _ _)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

end
