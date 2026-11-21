import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.QuotientMetricDivisors.SixthReductionExplicit
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.ConjLoss

theorem sum_padic_log_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    ∑ p ∈ P, Real.log p * (padicValNat p n : ℝ) ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hd : ∏ p ∈ P, p ^ padicValNat p n ∣ n := by
      refine Finset.prod_dvd_of_isRelPrime ?_ fun p _ => pow_padicValNat_dvd
      intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.1
        (Nat.Coprime.pow _ _ ((Nat.coprime_primes (hP p hp) (hP q hq)).2 hpq))
    have h1 : ∑ p ∈ P, Real.log p * (padicValNat p n : ℝ) =
        Real.log (∏ p ∈ P, (p : ℝ) ^ padicValNat p n) := by
      rw [Real.log_prod]
      · exact Finset.sum_congr rfl fun p _ => by rw [Real.log_pow, mul_comm]
      · intro p hp
        have : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
        positivity
    rw [h1]
    apply Real.log_le_log
    · refine Finset.prod_pos fun p hp => ?_
      have : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
      positivity
    · exact_mod_cast Nat.le_of_dvd hn hd

theorem sum_primes_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) (X a A W : ℝ) (hX : 0 ≤ X) (hXa : X ≤ a)
    (ha : 1 ≤ a) (hA : 0 ≤ A) (hW : 0 ≤ W) :
    ∑ p ∈ P, Real.log p * |(padicValNat p n : ℝ) +
      (if (p : ℝ) ≤ X then A * Real.logb p a + W / ((p : ℝ) ^ 2 - 1) else 0)| ≤
      Real.log n + X * (A * Real.log a) + 2 * (W * Real.log a) := by
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have h1 : ∀ p ∈ P, Real.log p * |(padicValNat p n : ℝ) +
      (if (p : ℝ) ≤ X then A * Real.logb p a + W / ((p : ℝ) ^ 2 - 1) else 0)| ≤
      Real.log p * (padicValNat p n : ℝ) +
      (if (p : ℝ) ≤ X then A * Real.log a + 2 * (W * Real.log a) * ((p : ℝ) ^ 2)⁻¹ else 0) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hl : 0 < Real.log p := Real.log_pos (by linarith)
    have hq : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
    split_ifs with h
    · have hb : 0 ≤ Real.logb p a := Real.logb_nonneg (by linarith) ha
      rw [abs_of_nonneg (by positivity), mul_add, mul_add]
      have e1 : Real.log p * (A * Real.logb p a) = A * Real.log a := by
        unfold Real.logb; field_simp
      have e2 : Real.log p ≤ Real.log a := Real.log_le_log (by linarith) (h.trans hXa)
      have e3 : W / ((p : ℝ) ^ 2 - 1) ≤ 2 * W * ((p : ℝ) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ hq (by positivity)]
        have : 0 ≤ (p : ℝ) ^ 2 - 2 := by nlinarith
        nlinarith [mul_nonneg hW this]
      have e4 := mul_le_mul e2 e3 (by positivity) hla
      rw [e1]
      nlinarith
    · rw [add_zero, add_zero, abs_of_nonneg (Nat.cast_nonneg _)]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, add_assoc]
  refine add_le_add (sum_padic_log_le P hP n) ?_
  have hsub : P.filter (fun p : ℕ => (p : ℝ) ≤ X) ⊆ Finset.Ioo 1 (⌊X⌋₊ + 1) := by
    intro p hp
    obtain ⟨a1, a2⟩ := Finset.mem_filter.1 hp
    exact Finset.mem_Ioo.2 ⟨(hP p a1).one_lt, Nat.lt_succ_of_le (Nat.le_floor a2)⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul]
  have c1 : ((Finset.Ioo 1 (⌊X⌋₊ + 1)).card : ℝ) ≤ X := by
    refine le_trans ?_ (Nat.floor_le hX)
    rw [Nat.card_Ioo]
    exact_mod_cast (by omega : ⌊X⌋₊ + 1 - 1 - 1 ≤ ⌊X⌋₊)
  have c2 : ∑ p ∈ Finset.Ioo 1 (⌊X⌋₊ + 1), ((p : ℝ) ^ 2)⁻¹ ≤ 1 := by
    have := sum_Ioo_inv_sq_le (α := ℝ) 1 (⌊X⌋₊ + 1)
    norm_num at this ⊢
    exact this
  exact add_le_add (mul_le_mul_of_nonneg_right c1 (by positivity))
    (mul_le_of_le_one_right (by positivity) c2)

end GlobalTheory.ConjLoss

end
