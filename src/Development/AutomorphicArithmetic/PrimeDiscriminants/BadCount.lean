import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.PrimeDiscriminants.BadPrimes

open NumberField

namespace Formalism.BasicNotions.Host

variable {R : Ranks} (H : Host R)

theorem sum_bad_log_div_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S, Real.log p / ((p : ℝ) - 1) ≤
      S.card + 2 + 4 * Real.log H.rdE := by
  set U := Nat.primeFactors (2 * (discr H.E).natAbs) ∪ S with hU
  have hprime : ∀ p ∈ U, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact hS p h
  have hterm1 : ∀ p ∈ U, Real.log p / ((p:ℝ) - 1) ≤ 1 := by
    intro p hp
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    rw [div_le_one (by linarith)]
    exact Real.log_le_sub_one_of_pos (by linarith)
  have hterm2 : ∀ p ∈ U, Real.log p / ((p:ℝ) - 1) ≤ Real.log p := by
    intro p hp
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    exact div_le_self (Real.log_natCast_nonneg p) (by linarith)
  rw [← Finset.sum_filter_add_sum_filter_not U (· ∈ H.small)]
  have hA : ∑ p ∈ U.filter (· ∈ H.small), Real.log p / ((p:ℝ) - 1) ≤ 4 * Real.log H.rdE := by
    calc _ ≤ ∑ p ∈ U.filter (· ∈ H.small), Real.log (p:ℝ) :=
          Finset.sum_le_sum fun p hp => hterm2 p (Finset.mem_filter.mp hp).1
      _ ≤ ∑ p ∈ H.small, Real.log (p:ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).2)
            (fun p _ _ => Real.log_natCast_nonneg p)
      _ ≤ _ := sum_small_log_le H
  have hB : ∑ p ∈ U.filter (· ∉ H.small), Real.log p / ((p:ℝ) - 1) ≤ S.card + 2 := by
    calc _ ≤ ∑ p ∈ U.filter (· ∉ H.small), (1:ℝ) :=
          Finset.sum_le_sum fun p hp => hterm1 p (Finset.mem_filter.mp hp).1
      _ = ((U \ H.small).card : ℝ) := by rw [Finset.sum_const, nsmul_one, Finset.sdiff_eq_filter]
      _ ≤ _ := by exact_mod_cast card_bad_sdiff_le H S
  linarith

end Formalism.BasicNotions.Host
