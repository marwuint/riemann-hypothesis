import Mathlib

namespace GlobalTheory

theorem multiset_mem_list_sum' {α : Type*} (l : List (Multiset α)) (x : α) :
    x ∈ l.sum ↔ ∃ m ∈ l, x ∈ m := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.sum_cons, Multiset.mem_add, ih]

theorem multiset_le_list_sum' {α : Type*} (l : List (Multiset α)) (m : Multiset α) (h : m ∈ l) :
    m ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Multiset.le_add_right _ _
    · exact (ih h).trans (Multiset.le_add_left _ _)

theorem norm_natCast_cpow_ofReal {q : ℕ} (hq : 0 < q) (s : ℝ) :
    ‖(q : ℂ) ^ ((s : ℝ) : ℂ)‖ = (q : ℝ) ^ s := by
  rw [Complex.norm_natCast_cpow_of_pos hq]
  simp

theorem rpow_exponent_inj_of_one_lt {b : ℝ} (hb : 1 < b) {x y : ℝ} (h : b ^ x = b ^ y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact absurd h (ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))
  · exact hxy
  · exact absurd h (ne_of_gt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))

end GlobalTheory
