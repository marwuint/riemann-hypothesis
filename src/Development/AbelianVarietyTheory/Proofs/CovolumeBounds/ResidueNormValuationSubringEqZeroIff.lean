import Mathlib

namespace GlobalTheory

open Filter Topology MvPowerSeries

section

variable {C : Type*} [NormedField C] [IsUltrametricDist C] {σ : Type*}

local notation "𝒪" => Valuation.valuationSubring (NormedField.valuation (K := C))

theorem mem_normValuationSubring_iff (x : C) : x ∈ 𝒪 ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
  rfl

theorem residue_normValuationSubring_eq_zero_iff (x : 𝒪) :
    IsLocalRing.residue 𝒪 x = 0 ↔ ‖(x : C)‖ < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff, NormedField.valuation_apply]
  rfl

omit [IsUltrametricDist C] in
theorem norm_finsuppProd_pow (t : σ →₀ ℕ) (z : σ → C) :
    ‖t.prod (z · ^ ·)‖ = t.prod (fun i n => ‖z i‖ ^ n) := by
  simp [Finsupp.prod, norm_prod]

theorem finsuppProd_pow_mono (t : σ →₀ ℕ) {c d : σ → ℝ} (h0 : ∀ i, 0 ≤ c i) (h : ∀ i, c i ≤ d i) :
    t.prod (c · ^ ·) ≤ t.prod (d · ^ ·) :=
  Finset.prod_le_prod (fun i _ => pow_nonneg (h0 i) _) fun i _ => pow_le_pow_left₀ (h0 i) (h i) _

theorem infinite_residueField_of_isAlgClosed [IsAlgClosed C] :
    Infinite (IsLocalRing.ResidueField 𝒪) := by
  by_contra hk
  rw [not_infinite_iff_finite] at hk
  have := Fintype.ofFinite (IsLocalRing.ResidueField 𝒪)
  set q := Fintype.card (IsLocalRing.ResidueField 𝒪) with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Polynomial.X ^ q - Polynomial.X + 1 : Polynomial C) (by
    have : (Polynomial.X ^ q - Polynomial.X + 1 : Polynomial C).degree = q := by
      rw [Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_sub_eq_left_of_degree_lt]
      · simp
      · simpa using hq1
      · rw [Polynomial.degree_sub_eq_left_of_degree_lt]
        · simpa using (zero_lt_one.trans hq1)
        · simpa using hq1
    rw [this]
    simpa using (zero_lt_one.trans hq1).ne')
  have hx' : x ^ q = x - 1 := by
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one] at hx
    linear_combination hx
  have hx1 : ‖x‖ ≤ 1 := by
    by_contra! h
    have h1 : ‖x - 1‖ ≤ ‖x‖ := by
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
      simpa using h.le
    have h2 : ‖x‖ ^ 1 < ‖x‖ ^ q := pow_lt_pow_right₀ h hq1
    rw [← hx', norm_pow] at h1
    linarith [pow_one ‖x‖]
  let y : 𝒪 := ⟨x, (mem_normValuationSubring_iff _).2 hx1⟩
  have hy : y ^ q = y - 1 := Subtype.ext (by simpa [y] using hx')
  have h3 := congrArg (IsLocalRing.residue 𝒪) hy
  rw [map_pow, map_sub, map_one, hq, FiniteField.pow_card] at h3
  simp [eq_sub_iff_add_eq] at h3

omit [IsUltrametricDist C] in
theorem norm_term_le (g : MvPowerSeries σ C) {c : σ → ℝ} {z : σ → C} (hz : ∀ i, ‖z i‖ ≤ c i)
    (t : σ →₀ ℕ) : ‖coeff t g * t.prod (z · ^ ·)‖ ≤ ‖coeff t g‖ * t.prod (c · ^ ·) := by
  rw [norm_mul, norm_finsuppProd_pow]
  exact mul_le_mul_of_nonneg_left (finsuppProd_pow_mono t (fun i => norm_nonneg (z i)) hz)
    (norm_nonneg _)

end

theorem exists_lt_norm_lt_one_of_isAlgClosed {C : Type*} [NontriviallyNormedField C]
    [IsAlgClosed C] (r : ℝ) (hr : r < 1) : ∃ x : C, r < ‖x‖ ∧ ‖x‖ < 1 := by
  obtain ⟨y, hy0, hy1⟩ := NormedField.exists_norm_lt_one C
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (le_max_right r 0)
    (max_lt hr one_pos)).eventually_lt_const hy0
  obtain ⟨n, hn, hn1⟩ := (h.and (eventually_gt_atTop 0)).exists
  obtain ⟨x, rfl⟩ := IsAlgClosed.exists_pow_nat_eq y hn1
  rw [norm_pow] at hn hy1
  exact ⟨x, (le_max_left r 0).trans_lt (lt_of_pow_lt_pow_left₀ n (norm_nonneg x) hn),
    (pow_lt_one_iff_of_nonneg (norm_nonneg x) hn1.ne').1 hy1⟩

end GlobalTheory
