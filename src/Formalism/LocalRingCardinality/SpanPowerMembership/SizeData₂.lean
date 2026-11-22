import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.BasicNotions

def scBig (B : ℕ) : Scale where
  x := ((B + 2 : ℕ) : ℝ) ^ (500 : ℝ)
  eps := 1 / 100
  one_lt_alt := by
    apply Real.one_lt_rpow _ (by norm_num)
    have : (2 : ℝ) ≤ ((B + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ B + 2)
    linarith
  eps_pos := by norm_num
  eps_lt := by norm_num
  J := 1
  one_le_J := le_rfl

def sc0 : Scale where
  x := (2 : ℝ) ^ (200 : ℝ)
  eps := 1 / 100
  one_lt_alt := Real.one_lt_rpow (by norm_num) (by norm_num)
  eps_pos := by norm_num
  eps_lt := by norm_num
  J := 1
  one_le_J := le_rfl

end Formalism.BasicNotions.Examples₂
