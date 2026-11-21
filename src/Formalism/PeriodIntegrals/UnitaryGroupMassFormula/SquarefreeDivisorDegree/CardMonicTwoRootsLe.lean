import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeDivisorDegree.MonicFintype

open Polynomial Finset

noncomputable section

namespace PI.SqfDivDeg.W

open Classical

theorem pt (k : ℕ) : 2 * k ≤ (k * k - k) + 2 * (if k = 0 then 0 else 1) := by
  match k with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
    have h : (k + 2) * (k + 2) - (k + 2) = (k + 2) * (k + 1) := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    rw [h]
    simp
    nlinarith

end PI.SqfDivDeg.W
