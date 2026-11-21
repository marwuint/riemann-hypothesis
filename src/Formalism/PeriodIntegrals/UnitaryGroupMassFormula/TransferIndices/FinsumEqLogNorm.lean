import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.DvTransferIdxOf

noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero

private theorem log_nonpos_of_le_one (m : ℤᵐ⁰) (h : m ≤ 1) : WithZero.log m ≤ 0 := by
  rcases eq_or_ne m 0 with h0 | h0
  · rw [h0, WithZero.log_zero]
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero] at h
    exact WithZero.exp_le_exp.mp h

theorem volume_nonneg : VNonneg := by
  intro K _ _ w x
  unfold vAdd
  have h := log_nonpos_of_le_one (w.valuation K (algebraMap (𝓞 K) K x)) (w.valuation_le_one x)
  omega

end PI.Dv.TIW
