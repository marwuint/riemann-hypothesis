import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions Formalism.MainNotions.WeilJacquetShalikaLaw

namespace Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

theorem sz_div_le_fact {p : ℕ} (hp : p.Prime) (n : ℕ) : n / p ≤ (n.factorial).factorization p := by
  haveI := Fact.mk hp
  rw [Nat.factorization_def _ hp, padicValNat_factorial (b := Nat.log p n + 2) (by omega)]
  have h1 : (1 : ℕ) ∈ Finset.Ico 1 (Nat.log p n + 2) := by simp
  have h2 := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1
  simp only [pow_one] at h2
  exact h2

private theorem primesLE_eq_filter_prime_range (n : ℕ) :
    Nat.primesLE n = Finset.filter Nat.Prime (Finset.range (n + 1)) := by
  ext p
  simp [Nat.primesLE, Nat.mem_primesBelow]

theorem sz_sum_div_log (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log (n.factorial : ℕ) := by
  have hsub : Nat.primesLE n ⊆ (n.factorial).factorization.support := by
    intro p hp
    rw [primesLE_eq_filter_prime_range, Finset.mem_filter, Finset.mem_range] at hp
    rw [Finsupp.mem_support_iff]
    exact (hp.2.factorization_pos_of_dvd (Nat.factorial_ne_zero n) (hp.2.dvd_factorial.mpr (by omega))).ne'
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p
      ≤ ∑ p ∈ Nat.primesLE n, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        rw [primesLE_eq_filter_prime_range, Finset.mem_filter] at hp
        apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg _)
        exact_mod_cast sz_div_le_fact hp.2 n
    _ ≤ ∑ p ∈ (n.factorial).factorization.support, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p _ _
        exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

theorem sz_log_fact (n : ℕ) : Real.log (n.factorial : ℕ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have h2 : (0 : ℝ) < (n.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos n
  calc Real.log (n.factorial : ℕ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log h2 h1
    _ = n * Real.log n := Real.log_pow n _

theorem sz_mertens (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hprime : ∀ p ∈ Nat.primesLE n, p.Prime := by
    intro p hp
    rw [primesLE_eq_filter_prime_range, Finset.mem_filter] at hp
    exact hp.2
  have htheta : ∑ p ∈ Nat.primesLE n, Real.log p ≤ n * Real.log 4 := by
    have h1 : Real.log ((primorial n : ℕ) : ℝ) = ∑ p ∈ Nat.primesLE n, Real.log p := by
      rw [primesLE_eq_filter_prime_range, primorial, Nat.cast_prod, Real.log_prod]
      intro p hp
      exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
    rw [← h1, ← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast primorial_pos n)
    exact_mod_cast primorial_le_4_pow n
  have hfloor : ∀ p ∈ Nat.primesLE n, (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
    intro p hp
    have hpp := hprime p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    rw [div_le_iff₀ hp0]
    have h1 : (p : ℝ) * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) = n := by exact_mod_cast Nat.div_add_mod n p
    have h2 : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt n hpp.pos
    nlinarith
  have hmain : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ n * Real.log n + n * Real.log 4 := by
    calc (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p
        = ∑ p ∈ Nat.primesLE n, (n : ℝ) / p * Real.log p := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          ring
      _ ≤ ∑ p ∈ Nat.primesLE n, ((((n / p : ℕ) : ℝ) + 1) * Real.log p) := by
          apply Finset.sum_le_sum
          intro p hp
          exact mul_le_mul_of_nonneg_right (hfloor p hp) (Real.log_natCast_nonneg _)
      _ = ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p + ∑ p ∈ Nat.primesLE n, Real.log p := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p _
          ring
      _ ≤ n * Real.log n + n * Real.log 4 := by
          have h := (sz_sum_div_log n).trans (sz_log_fact n)
          linarith
  exact le_of_mul_le_mul_left (by rw [mul_add]; exact hmain) hn0

theorem sz_lpF_le (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) :
    lpF l d Ds ≤ (l : ℝ) / ((l : ℝ) ^ 2 - 1) * ∑ s, Ds s := by
  unfold lpF
  have h : 0 ≤ sSup (lpFeasible l d Ds) := by
    apply Real.sSup_nonneg
    rintro y ⟨xs, h0, -, -, rfl⟩
    exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => h0 s i
  linarith

end Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

end
