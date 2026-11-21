import Mathlib

open scoped LaurentSeries PowerSeries

namespace GlobalTheory.PsiBasis

variable {k : Type} [Field k]

noncomputable def comp (l : ℕ) (hl : 0 < l) (i : ℕ) : k⸨X⸩ →ₗ[k] k⸨X⸩ where
  toFun y :=
    { coeff := fun m => y.coeff (l * m + i)
      isPWO_support' := by
        apply Set.IsWF.isPWO
        apply BddBelow.isWF
        refine ⟨min 0 (y.order - i), fun m hm => ?_⟩
        by_contra h
        apply hm
        apply HahnSeries.coeff_eq_zero_of_lt_order
        have h1 : m < 0 := lt_of_lt_of_le (not_le.1 h) (min_le_left _ _)
        have h2 : m < y.order - i := lt_of_lt_of_le (not_le.1 h) (min_le_right _ _)
        have h3 : (1 : ℤ) ≤ l := by exact_mod_cast hl
        nlinarith }
  map_add' x y := by ext m; simp
  map_smul' c x := by ext m; simp

theorem comp_coeff (l : ℕ) (hl : 0 < l) (i : ℕ) (y : k⸨X⸩) (m : ℤ) :
    (comp l hl i y).coeff m = y.coeff (l * m + i) := rfl

theorem p_zpow (s : ℤ) :
    (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s = HahnSeries.single s 1 := by
  cases s with
  | ofNat n => simp [HahnSeries.single_pow]
  | negSucc n =>
    rw [zpow_negSucc, HahnSeries.single_pow, HahnSeries.inv_single]
    simp [Int.negSucc_eq]

theorem p_pow (s : ℕ) :
    (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s = HahnSeries.single (s : ℤ) 1 := by
  simp [HahnSeries.single_pow]

theorem mem_iff (s : ℤ) (x : k⸨X⸩) :
    (∃ b : k⟦X⟧, x = (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s * (b : k⸨X⸩)) ↔
      ∀ m < s, x.coeff m = 0 := by
  rw [p_zpow]
  constructor
  · rintro ⟨b, rfl⟩ m hm
    rw [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe, if_pos (by omega), mul_zero]
  · intro h
    refine ⟨PowerSeries.mk fun n => x.coeff (s + n), ?_⟩
    ext m
    rw [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe, one_mul]
    split_ifs with hm
    · exact h m (by omega)
    · rw [PowerSeries.coeff_mk]; congr 1; omega

section
variable (l : ℕ) (hl : 0 < l) (φ : k⸨X⸩ →+* k⸨X⸩)
  (hφ : ∀ (x : k⸨X⸩) (m : ℤ), (φ x).coeff m = if (l : ℤ) ∣ m then x.coeff (m / l) else 0)
include hl hφ

theorem comp_pow_mul {i j : ℕ} (hi : i < l) (hj : j < l) (a : k⸨X⸩) :
    comp l hl i ((HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ j * φ a)
      = if j = i then a else 0 := by
  ext m
  have hl' : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
  rw [comp_coeff, p_pow, HahnSeries.coeff_single_mul, one_mul, hφ]
  by_cases h : j = i
  · subst h
    simp [Int.mul_ediv_cancel_left _ hl']
  · rw [if_neg h, if_neg]
    · simp
    · intro hd
      have : (l : ℤ) ∣ (i : ℤ) - j := by
        have h2 := dvd_sub hd (dvd_mul_right (l : ℤ) m)
        have e : (l : ℤ) * m + i - j - l * m = i - j := by ring
        rwa [e] at h2
      have := Int.eq_zero_of_abs_lt_dvd this (by rw [abs_lt]; constructor <;> omega)
      omega

theorem comp_one_add_pow_mul {i j : ℕ} (hi : i < l) (hj : j < l) (a : k⸨X⸩) :
    comp l hl i ((1 + (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩)) ^ j * φ a)
      = (j.choose i) • a := by
  rw [add_comm, add_pow, Finset.sum_mul, map_sum]
  have : ∀ m ∈ Finset.range (j + 1),
      comp l hl i ((HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ m * 1 ^ (j - m) *
        (j.choose m : k⸨X⸩) * φ a) = if m = i then (j.choose i) • a else 0 := by
    intro m hm
    have hm' : m < l := by have := Finset.mem_range.1 hm; omega
    rw [one_pow, mul_one, mul_assoc, ← map_natCast φ, ← map_mul,
      comp_pow_mul l hl φ hφ hi hm']
    split_ifs with h
    · subst h; rw [nsmul_eq_mul]
    · rfl
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simpa using h), zero_smul]

end

noncomputable def psi (l : ℕ) (hl : 0 < l) : k⸨X⸩ →ₗ[k] k⸨X⸩ :=
  ∑ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • comp l hl i

theorem psi_apply (l : ℕ) (hl : 0 < l) (y : k⸨X⸩) :
    psi l hl y = ∑ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • comp l hl i y := by
  simp only [psi, LinearMap.sum_apply, LinearMap.smul_apply]

end GlobalTheory.PsiBasis
