import Mathlib

noncomputable section

namespace PI.PrimesDyadicRS.W

def At (y : ℝ) : Prop :=
  3 * y / (5 * Real.log y) < (Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ)

end PI.PrimesDyadicRS.W
