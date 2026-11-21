import Mathlib

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Finset

theorem padicValNat_factorial_add_sum (l : ℕ) [Fact l.Prime] (m S : ℕ) :
    padicValNat l m.factorial + ∑ j ∈ range S, padicValNat l (m + 1 + j) =
      padicValNat l (m + S).factorial := by
  induction S with
  | zero => simp
  | succ n ih =>
    have h1 : (m + (n + 1)).factorial = (m + n + 1) * (m + n).factorial := by
      rw [show m + (n + 1) = m + n + 1 by omega, Nat.factorial_succ]
    have h2 : padicValNat l ((m + n + 1) * (m + n).factorial) =
        padicValNat l (m + n + 1) + padicValNat l (m + n).factorial :=
      padicValNat.mul (by omega) (Nat.factorial_ne_zero _)
    rw [Finset.sum_range_succ, h1, h2, show m + 1 + n = m + n + 1 by omega]
    omega

theorem padicValNat_factorial_le_div_sub_one' (l : ℕ) [hp : Fact l.Prime] (n : ℕ) :
    (padicValNat l n.factorial : ℝ) ≤ n / ((l : ℝ) - 1) := by
  have hl : 2 ≤ l := hp.out.two_le
  have hlR : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have key := sub_one_mul_padicValNat_factorial (p := l) n
  have hle : (l - 1) * padicValNat l n.factorial ≤ n := by
    rw [key]; exact Nat.sub_le _ _
  have hcast : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have h' : ((l : ℝ) - 1) * (padicValNat l n.factorial : ℝ) ≤ n := by
    rw [← hcast]; exact_mod_cast hle
  rw [le_div_iff₀ hlR]
  linarith [mul_comm ((l : ℝ) - 1) (padicValNat l n.factorial : ℝ)]

private theorem sum_Ico_int_eq_sum_range_add (a : ℤ) (S : ℕ) (f : ℤ → ℕ) :
    ∑ i ∈ Finset.Ico a (a + S), f i = ∑ j ∈ range S, f (a + j) := by
  induction S with
  | zero => simp
  | succ n ih =>
    have hI : Finset.Ico a (a + ((n + 1 : ℕ) : ℤ)) = insert (a + n) (Finset.Ico a (a + n)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Ico]
      push_cast
      constructor <;> intro h <;> omega
    rw [hI, Finset.sum_insert (by simp), ih, Finset.sum_range_succ, add_comm]

theorem exists_sum_padicValInt_window_eq (l : ℕ) (a : ℤ) (S N : ℕ)
    (ha : ∀ i ∈ Finset.Ico a (a + S), i ≠ 0 ∧ |i| ≤ (N : ℤ)) :
    ∃ m : ℕ, m + S ≤ N ∧ ∑ i ∈ Finset.Ico a (a + S), padicValInt l i =
      ∑ j ∈ range S, padicValNat l (m + 1 + j) := by
  rcases Nat.eq_zero_or_pos S with rfl | hS
  · exact ⟨0, by simp, by simp⟩
  have hfirst := ha a (by simp only [Finset.mem_Ico]; omega)
  have hlast := ha (a + S - 1) (by simp only [Finset.mem_Ico]; omega)
  rw [sum_Ico_int_eq_sum_range_add]
  rcases lt_or_gt_of_ne hfirst.1 with hneg | hpos
  · have hend : a + S ≤ 0 := by
      by_contra hc
      have h0 := ha 0 (by simp only [Finset.mem_Ico]; omega)
      exact h0.1 rfl
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ -a - S by omega)
    refine ⟨m, ?_, ?_⟩
    · have := (abs_le.mp hfirst.2).1
      omega
    · rw [← Finset.sum_range_reflect (fun j => padicValNat l (m + 1 + j)) S]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have he : a + (j : ℤ) = -(((m + 1 + (S - 1 - j) : ℕ)) : ℤ) := by omega
      rw [padicValInt, he, Int.natAbs_neg]
      rfl
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ a - 1 by omega)
    refine ⟨m, ?_, ?_⟩
    · have := (abs_le.mp hlast.2).2
      omega
    · apply Finset.sum_congr rfl
      intro j _
      have he : a + (j : ℤ) = ((m + 1 + j : ℕ) : ℤ) := by push_cast; omega
      rw [padicValInt, he]
      rfl

theorem sum_padicValInt_window_le (l : ℕ) [Fact l.Prime] (a : ℤ) (S N : ℕ)
    (ha : ∀ i ∈ Finset.Ico a (a + S), i ≠ 0 ∧ |i| ≤ (N : ℤ)) :
    ((∑ i ∈ Finset.Ico a (a + S), padicValInt l i : ℕ) : ℝ) ≤ N / ((l : ℝ) - 1) := by
  obtain ⟨m, hmN, heq⟩ := exists_sum_padicValInt_window_eq l a S N ha
  rw [heq]
  have h1 := padicValNat_factorial_add_sum l m S
  have h2 := padicValNat_factorial_le_div_sub_one' l (m + S)
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlR : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have h3n : ∑ j ∈ range S, padicValNat l (m + 1 + j) ≤ padicValNat l (m + S).factorial := by
    omega
  have h3 : ((∑ j ∈ range S, padicValNat l (m + 1 + j) : ℕ) : ℝ) ≤
      (padicValNat l (m + S).factorial : ℝ) := by exact_mod_cast h3n
  have h4 : ((m + S : ℕ) : ℝ) / ((l : ℝ) - 1) ≤ N / ((l : ℝ) - 1) := by
    rw [le_div_iff₀ hlR, div_mul_cancel₀ _ hlR.ne']
    exact_mod_cast hmN
  linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
