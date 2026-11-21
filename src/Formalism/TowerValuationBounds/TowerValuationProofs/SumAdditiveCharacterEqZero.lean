import Formalism.TowerValuationBounds.HermitianSumValuationBound

noncomputable section
namespace Formalism.ValuationGridEstimates
open Finset

theorem height_bound_alt : AbsValuationSumBound := by
  intro W E _ lam val δ absx Wx Bδ hlam hsupp hpf
  classical
  have habs : ∀ x : ℝ, |x| = x + 2 * max 0 (-x) := by
    intro x
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h, max_eq_left (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_right (by linarith)]; ring
  have h1 : ∑ w ∈ Wx, lam w * |val w| =
      (∑ σ, Real.log (absx σ)) / Fintype.card E + 2 * ∑ w ∈ Wx, lam w * max 0 (-val w) := by
    rw [← hpf, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro w _
    rw [habs]; ring
  have hmean : (∑ σ, Real.log (absx σ)) / Fintype.card E ≤
      (∑ σ, Real.posLog (absx σ)) / Fintype.card E := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply sum_le_sum
    intro σ _
    rw [Real.posLog_def]
    exact le_max_right _ _
  refine ⟨h1, by rw [h1]; linarith, ?_⟩
  intro hδ hden hB F
  have h2 : ∑ w ∈ F, lam w * |val w| ≤ ∑ w ∈ Wx, lam w * |val w| := by
    calc ∑ w ∈ F, lam w * |val w| ≤ ∑ w ∈ F ∪ Wx, lam w * |val w| :=
          sum_le_sum_of_subset_of_nonneg subset_union_left
            (fun w _ _ => mul_nonneg (hlam w) (abs_nonneg _))
      _ = ∑ w ∈ Wx, lam w * |val w| := by
          symm
          apply sum_subset subset_union_right
          intro w _ hw
          rw [hsupp w hw]; simp
  have h3 : ∑ w ∈ Wx, lam w * max 0 (-val w) ≤ 3 * Bδ := by
    calc ∑ w ∈ Wx, lam w * max 0 (-val w) ≤ ∑ w ∈ Wx, 3 * (lam w * δ w) := by
          apply sum_le_sum
          intro w _
          have : max 0 (-val w) ≤ 3 * δ w := max_le (by linarith [hδ w]) (by linarith [hden w])
          nlinarith [hlam w]
      _ = 3 * ∑ w ∈ Wx, lam w * δ w := by rw [Finset.mul_sum]
      _ ≤ 3 * Bδ := by linarith [hB Wx]
  linarith

lemma log_div_sq_le_difference (m : ℕ) (hm : 4 ≤ m) :
    Real.log ((m + 1 : ℕ) : ℝ) / (((m + 1 : ℕ) : ℝ)) ^ 2 ≤
      (1 + Real.log m) / m - (1 + Real.log ((m + 1 : ℕ) : ℝ)) / ((m + 1 : ℕ) : ℝ) := by
  have hx : (4 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  set x : ℝ := (m : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  set L1 := Real.log (x + 1) with hL1
  set L0 := Real.log x with hL0
  have hdiff : L1 - L0 ≤ 1 / x := by
    have h1 : L1 - L0 = Real.log ((x + 1) / x) := by
      rw [Real.log_div (by linarith) (by linarith)]
    have h2 := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    have h3 : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  have hbig : (5 : ℝ) / 4 ≤ L1 := by
    have h4 : Real.log 4 ≤ L1 := Real.log_le_log (by norm_num) (by linarith)
    have h5 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have e1 : (1 + L1) / (x * (x + 1)) - 1 / x ^ 2 - L1 / (x + 1) ^ 2 =
      (L1 * x - x - 1) / (x ^ 2 * (x + 1) ^ 2) := by
    field_simp; ring
  have e2 : (1 + L0) / x - (1 + L1) / (x + 1) - ((1 + L1) / (x * (x + 1)) - 1 / x ^ 2) =
      (L0 - L1 + 1 / x) / x := by
    field_simp; ring
  have p1 : 0 ≤ (L1 * x - x - 1) / (x ^ 2 * (x + 1) ^ 2) :=
    div_nonneg (by nlinarith) (by positivity)
  have p2 : 0 ≤ (L0 - L1 + 1 / x) / x := div_nonneg (by linarith) hx0.le
  linarith

lemma sum_log_div_sq_telescoping (M : ℕ) (hM : 4 ≤ M) :
    ∑ n ∈ Icc 5 M, Real.log n / (n : ℝ) ^ 2 ≤ (1 + Real.log 4) / 4 - (1 + Real.log M) / M := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := log_div_sq_le_difference M hM
    linarith

theorem prime_sum_bound : PrimeLogSquareSumLtOne := by
  intro P hP
  set M : ℕ := max (P.sup id) 4 with hMdef
  have hM : 4 ≤ M := le_max_right _ _
  have hsub : P ⊆ {2, 3} ∪ Icc 5 M := by
    intro l hl
    have hp := hP l hl
    have h2 := hp.two_le
    have hle : l ≤ M := le_trans (Finset.le_sup (f := id) hl) (le_max_left _ _)
    have h4 : l ≠ 4 := by
      rintro rfl; exact absurd hp (by norm_num)
    simp only [mem_union, mem_insert, mem_singleton, mem_Icc]
    omega
  have hnn : ∀ n : ℕ, 0 ≤ Real.log n / (n : ℝ) ^ 2 := by
    intro n; exact div_nonneg (Real.log_natCast_nonneg n) (by positivity)
  have h1 : ∑ l ∈ P, Real.log l / (l : ℝ) ^ 2 ≤ ∑ l ∈ {2, 3} ∪ Icc 5 M, Real.log l / (l : ℝ) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnn n)
  have hd : Disjoint ({2, 3} : Finset ℕ) (Icc 5 M) := by
    rw [disjoint_left]; intro x hx hx'
    simp only [mem_insert, mem_singleton] at hx; rw [mem_Icc] at hx'; omega
  rw [sum_union hd, sum_pair (by norm_num)] at h1
  have h2 := sum_log_div_sq_telescoping M hM
  have h3 : 0 ≤ (1 + Real.log M) / M :=
    div_nonneg (by have := Real.log_natCast_nonneg M; linarith) (Nat.cast_nonneg _)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h5 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have h6 := Real.log_two_lt_d9
  push_cast at h1
  linarith

theorem prime_budget_bound : PrimeLogBudget := by
  intro N0 BN0 h P hP
  have h1 := h P hP
  have h2 := prime_sum_bound P hP
  have e : ∑ l ∈ P, (N0 l + ((l : ℝ) ^ 2)⁻¹) * Real.log l =
      ∑ l ∈ P, N0 l * Real.log l + ∑ l ∈ P, Real.log l / (l : ℝ) ^ 2 := by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro l _; rw [div_eq_mul_inv]; ring
  rw [e]; linarith

end Formalism.ValuationGridEstimates
