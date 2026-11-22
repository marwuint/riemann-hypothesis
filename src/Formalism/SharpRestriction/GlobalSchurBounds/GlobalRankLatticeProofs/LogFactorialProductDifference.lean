import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaFiveOneOfTheoremTwo

noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

theorem exp_neg_r_le_third (D : D7) : Real.exp (-(D.R.r : ℝ)) ≤ 1 / 3 := by
  have hr : 2 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    first
      | (show 2 ≤ D.R.k + D.R.m - 1; omega)
      | omega
  have hr' : (2 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  calc Real.exp (-(D.R.r : ℝ)) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
    _ = 1 / Real.exp 2 := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3

theorem place_dimension_upper_bound (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (h3 : SigmaDegreeTwoSidedBoundOfGap D) (hgap : ∀ ρ, GapAtLeast (rowSgn D) (rowLam D ρ) (gap3 D 8192 (1 / 3)))
    (u : D.what₂.Word) (ρ : D.what₂.Tau) :
    Real.log (D.dsig ρ) - Real.log (dimV (uColR D u ρ)) ≤
      (D.R.k : ℝ) * D.R.m * (Real.log 3 + 5 * Real.log (2 * D.R.k) + 5 * sc.L + 10) := by
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  have hpl := place_data_under_section_B D sc C0 Δ w hB u ρ
  have b7 : 1 ≤ Δ := hB.2.2.2.2.2.2.1
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    exact_mod_cast (by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)
  have h := (h3 (1 / 3) (exp_neg_r_le_third D) (by norm_num) ρ
    (fun a b hab => le_trans (explicit_gap_le_general_gap D 8192 (1 / 3) le_rfl) (hgap ρ a b hab))).2
  rw [formal_degree_line_eq, count_plus_eq, count_minus_eq] at h
  obtain ⟨hd, hT, hlog⟩ := Formalism.LogVandermondeBounds.StandardLattice.UpperPlace_holds sc.eps sc.x sc.eps_pos sc.one_lt_alt.le D.R.k D.R.m Δ 3
      (uN D u ρ) (vN D ρ) (bN D ρ) (fun j => w j ρ) hm D.R.m_even (by omega) hmk b7 (by norm_num) hpl
      (fun i j hij hj => one_le_column_sub_of_lt D u ρ i j hij hj)
  have a1 := abs_param_sup_nonneg (rowLam D ρ)
  have a2 := abs_param_sup_le D ρ
  have hr1 : (1 : ℝ) ≤ ((D.R.k - 1 + D.R.m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ D.R.k - 1 + D.R.m)
  have h' : D.dsig ρ ≤ 4 * Formalism.LogVandermondeBounds.StandardLattice.dTau D.R.k D.R.m (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) *
      (3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * ((D.R.k - 1 + D.R.m : ℕ) : ℝ) *
        (vN D ρ 0 + bN D ρ (D.R.m - 1))) ^ ((D.R.k - 1 + D.R.m / 2) * (D.R.m / 2)) := by
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have c0 : 0 ≤ 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) := by positivity
    calc 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * lamAbs (rowLam D ρ)
        ≤ 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * (vN D ρ 0 + bN D ρ (D.R.m - 1)) :=
          mul_le_mul_of_nonneg_left a2 c0
      _ = 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * 1 * (vN D ρ 0 + bN D ρ (D.R.m - 1)) := by ring
      _ ≤ 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * ((D.R.k - 1 + D.R.m : ℕ) : ℝ) *
          (vN D ρ 0 + bN D ρ (D.R.m - 1)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 c0) (le_trans a1 a2)
  rw [dim_weyl_column_eq]
  have h4 := Real.log_le_log (D.dsig_pos ρ) h'
  have eL : sc.L = sc.x ^ sc.eps := rfl
  rw [eL]
  linarith

theorem facProd_pos' (N : ℕ) : 0 < facProd N := Formalism.MainNotions.StandardLattice.factorial_product_pos N

theorem log_factorial_product_difference (k r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) :
    Real.log (facProd r) - Real.log (facProd k) ≤ ((r - k : ℕ) : ℝ) * ((r : ℝ) * Real.log r) := by
  have hsplit : facProd r = facProd k * ∏ i ∈ Finset.Ico k r, ((i.factorial : ℕ) : ℝ) := by
    unfold facProd
    rw [Finset.prod_range_mul_prod_Ico _ hkr]
  have hk0 : 0 < facProd k := facProd_pos' k
  have hP0 : 0 < ∏ i ∈ Finset.Ico k r, ((i.factorial : ℕ) : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  rw [hsplit, Real.log_mul hk0.ne' hP0.ne', add_sub_cancel_left,
    Real.log_prod (fun i _ => by exact_mod_cast (Nat.factorial_pos i).ne')]
  calc ∑ i ∈ Finset.Ico k r, Real.log ((i.factorial : ℕ) : ℝ)
      ≤ ∑ i ∈ Finset.Ico k r, ((r : ℝ) * Real.log r) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hir : i ≤ r := (Finset.mem_Ico.mp hi).2.le
        have h1 : ((i.factorial : ℕ) : ℝ) ≤ (r : ℝ) ^ r := by
          exact_mod_cast (Nat.factorial_le_pow i).trans
            ((Nat.pow_le_pow_left hir i).trans (Nat.pow_le_pow_right (by omega) hir))
        calc Real.log ((i.factorial : ℕ) : ℝ) ≤ Real.log ((r : ℝ) ^ r) :=
              Real.log_le_log (by exact_mod_cast Nat.factorial_pos i) h1
          _ = (r : ℝ) * Real.log r := by rw [Real.log_pow]
    _ = ((r - k : ℕ) : ℝ) * ((r : ℝ) * Real.log r) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

theorem log_X_upper_arithmetic (f k m L CY lv l2v SL lg S5 S6 X : ℝ) (hf : 0 < f) (hk : 5 ≤ k) (hm : 44 ≤ m) (hmk : m ≤ k)
    (hL : 9 ≤ L) (hlv0 : 0 ≤ lv) (hlv : lv ≤ L) (h2v : 0 ≤ l2v) (hSL : SL ≤ f * m) (hlg0 : 0 ≤ lg)
    (hlg : lg ≤ 2 * CY * L) (hS5 : S5 ≤ 0)
    (hS6 : S6 ≤ f * (k * m * (2 + 5 * L + 5 * L + 10) + m * (2 * k * L)))
    (id : f * k * X = f * ((m - 1) * k + m * (m - 1) / 2) * lv - f * ((m - 1) / 2) * l2v + SL +
      f * (m * (2 * k + m - 1) / 2) * lg + f * S5 + S6) :
    X ≤ (15 + 3 * CY) * m * L := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hL0 : 0 < L := by linarith
  have hCY : 0 ≤ CY := by
    by_contra h
    push_neg at h
    have : 2 * CY * L < 0 := by nlinarith
    linarith
  have ht1 : f * ((m - 1) * k + m * (m - 1) / 2) * lv ≤ f * ((m - 1) * k + m * (m - 1) / 2) * L :=
    mul_le_mul_of_nonneg_left hlv (by have : 0 ≤ (m - 1) * k := by nlinarith
                                      have : 0 ≤ m * (m - 1) / 2 := by nlinarith
                                      positivity)
  have ht2 : 0 ≤ f * ((m - 1) / 2) * l2v := by
    have : 0 ≤ (m - 1) / 2 := by linarith
    positivity
  have ht4 : f * (m * (2 * k + m - 1) / 2) * lg ≤ f * (m * (2 * k + m - 1) / 2) * (2 * CY * L) :=
    mul_le_mul_of_nonneg_left hlg (by have : 0 ≤ m * (2 * k + m - 1) / 2 := by nlinarith
                                      positivity)
  have ht5 : f * S5 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hf.le hS5
  have hsum : f * k * X ≤ f * (((m - 1) * k + m * (m - 1) / 2) * L + m +
      m * (2 * k + m - 1) * CY * L + k * m * (12 + 12 * L)) := by
    rw [id]
    nlinarith
  have hpoly : ((m - 1) * k + m * (m - 1) / 2) * L + m + m * (2 * k + m - 1) * CY * L +
      k * m * (12 + 12 * L) ≤ k * ((15 + 3 * CY) * m * L) := by
    have a1 : 0 ≤ CY * L * m * (k - m + 1) := by
      have : 0 ≤ k - m + 1 := by linarith
      positivity
    have a2 : 0 ≤ k * m * (L - 9) := by
      have : 0 ≤ L - 9 := by linarith
      positivity
    have a3 : 0 ≤ m * (k - m) * L := by
      have : 0 ≤ k - m := by linarith
      positivity
    have a4 : 0 ≤ k * L := by positivity
    have a5 : m ≤ k * m * L := by nlinarith
    nlinarith
  have hfk : 0 < f * k := mul_pos hf hk0
  have : f * k * X ≤ f * k * ((15 + 3 * CY) * m * L) := by
    calc f * k * X ≤ f * (((m - 1) * k + m * (m - 1) / 2) * L + m +
          m * (2 * k + m - 1) * CY * L + k * m * (12 + 12 * L)) := hsum
      _ ≤ f * (k * ((15 + 3 * CY) * m * L)) := mul_le_mul_of_nonneg_left hpoly hf.le
      _ = f * k * ((15 + 3 * CY) * m * L) := by ring
  exact le_of_mul_le_mul_left this hfk

end Formalism.MainNotions.StandardLattice
