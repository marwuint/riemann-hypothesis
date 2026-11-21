import Mathlib
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

theorem no_form_of_bidegree_one_one : PowerCongruenceIffEqual := by
  unfold PowerCongruenceIffEqual
  intro l d s s' hl hs hs' hdiv
  have h1 : l ^ s < l ^ d := Nat.pow_lt_pow_right (by omega) hs
  have h2 : l ^ s' < l ^ d := Nat.pow_lt_pow_right (by omega) hs'
  have h3 : 1 ≤ l ^ s := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ l ^ s' := Nat.one_le_pow _ _ (by omega)
  have h5 : 1 ≤ l ^ d := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub h5, Nat.cast_pow, Nat.cast_one] at hdiv
  have h1' : (l : ℤ) ^ s < (l : ℤ) ^ d := by exact_mod_cast h1
  have h2' : (l : ℤ) ^ s' < (l : ℤ) ^ d := by exact_mod_cast h2
  have h3' : (1 : ℤ) ≤ (l : ℤ) ^ s := by exact_mod_cast h3
  have h4' : (1 : ℤ) ≤ (l : ℤ) ^ s' := by exact_mod_cast h4
  have hz := Int.eq_zero_of_abs_lt_dvd hdiv (by rw [abs_lt]; constructor <;> linarith)
  have h6 : (l : ℤ) ^ s = (l : ℤ) ^ s' := by linarith
  have h7 : l ^ s = l ^ s' := by exact_mod_cast h6
  exact Nat.pow_right_injective hl h7

end Formalism.HermitianLattices.IntegralLatticeDensity
