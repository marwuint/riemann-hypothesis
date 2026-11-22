import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.DimensionConstantBounds

noncomputable section

namespace GlobalTheory.ConstCompare

open Formalism.BasicNotions Formalism.MainNotions NumberField
open GlobalTheory.IndefiniteRowSideFullHecke

variable {D : D7}

theorem choose_two_add (p q : ℕ) :
    p * q + p * (p - 1) / 2 + q * (q - 1) / 2 = (p + q).choose 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← Nat.add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ← ih]
    simp only [Nat.choose_one_right]
    ring

theorem q_eq (D : D7) : WeightAlgebra.qq D = DimensionConstantBounds.q D := rfl

theorem g0_eq (D : D7) : WeightAlgebra.g0 D = DimensionConstantBounds.g0 D := rfl

theorem degF_eq {j : ℕ} (w : WeightFamilies.Wt D j) : WeightAlgebra.DF w = DimensionConstantBounds.degF w := rfl

theorem normShift_eq (D : D7) (j : ℕ) : WeightAlgebra.n0 D j = DimensionConstantBounds.n0 D j := rfl

theorem Z_eq (L : SizeData₂ D) : WeightAlgebra.Zb D L = DimensionConstantBounds.Z L := rfl

end GlobalTheory.ConstCompare

end
