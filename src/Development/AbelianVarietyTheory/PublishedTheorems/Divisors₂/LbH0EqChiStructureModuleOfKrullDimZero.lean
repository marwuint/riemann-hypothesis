import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.NefNumericsModel

section Space
open ProjSpace
variable (k : Type) [Field k]

theorem selfIntersection_O1 (N : ℕ) : topSelfIntersection k (O1 k N) N = 1 := by
  have hc : ∀ j : ℕ, chi k (twistZ (structureModule (PSpace k N)) (O1 k N) (-(j : ℤ))) =
      Ring.choose (-(j : ℤ) + N) N := fun j => ProjCoh.chi_sheafO k N _
  rw [topSelf_def, interNum_const_eq_sum k _ (O1_isLB k N) N, Finset.sum_eq_single 0]
  · rw [hc]
    simp [Ring.choose_natCast]
  · intro j hj hj0
    have hjN : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hn : -(j : ℤ) + N = ((N - j : ℕ) : ℤ) := by
      rw [Nat.cast_sub hjN]; ring
    rw [hc, hn, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (show N - j < N by omega)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos N)) h

end Space

end GlobalTheory.NefNumericsModel
