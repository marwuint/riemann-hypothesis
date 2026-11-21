import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaFiveOneOfTheoremTwo

noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

theorem b_ge_one_section_B (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) : 1 ≤ bN D ρ j := by
  unfold DataB at hB
  obtain ⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩ := hB
  have hL := scale_one_le_L sc
  have hkpos : (0 : ℝ) < D.R.k := by
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    nlinarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 0 < D.R.k := by exact_mod_cast hkpos
    exact_mod_cast Nat.one_le_of_lt this
  have hx := sc.one_lt_alt
  have hpos : ∀ i, i < D.R.m → 1 ≤ bN D ρ i := by
    intro i
    induction i with
    | zero =>
      intro _
      have h0 := (hb0 ρ).1
      have h4 : 1 ≤ bN D ρ 0 / sc.x := le_trans (by nlinarith) h0
      have h5 := (le_div_iff₀ (by linarith)).mp h4
      nlinarith
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := (hw ρ i (by omega)).2.1
      have h3 := hinc ρ i hi
      linarith
  exact hpos j hj

theorem weights_le_two_b (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) : w j ρ ≤ 2 * sc.b := by
  unfold DataB at hB
  obtain ⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩ := hB
  have hstep : ∀ i, i + 1 < D.R.m → w i ρ ≤ w (i + 1) ρ := fun i hi =>
    le_of_lt (lt_trans (hinc ρ i hi) (hw ρ (i + 1) hi).2.1)
  have hmono : ∀ d, ∀ i, i + d = D.R.m - 1 → w i ρ ≤ w (D.R.m - 1) ρ := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have h : i = D.R.m - 1 := by omega
      simp only [h, le_refl]
    | succ d ih =>
      intro i hi
      exact le_trans (hstep i (by omega)) (ih (i + 1) (by omega))
  exact le_trans (hmono (D.R.m - 1 - j) j (by omega)) (hb0 ρ).2

theorem log_weight_minus_log_b_bound (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    (D.R.k : ℝ) * Real.log (w j ρ) - ((D.R.k : ℝ) - 1) * Real.log (bN D ρ j) ≤ (D.R.k : ℝ) / sc.x + 2 * sc.L := by
  have hb1 := b_ge_one_section_B D sc C0 Δ w hB ρ j hj
  have hwl := weights_le_two_b D sc C0 Δ w hB ρ j hj
  unfold DataB at hB
  obtain ⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩ := hB
  obtain ⟨hw0, hbw, habs⟩ := hw ρ j hj
  have hL := scale_one_le_L sc
  have hx := sc.one_lt_alt
  have hkpos : (0 : ℝ) < D.R.k := by
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    nlinarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 0 < D.R.k := by exact_mod_cast hkpos
    exact_mod_cast Nat.one_le_of_lt this
  have hBpos : 0 < bN D ρ j := by linarith
  have hratio : Real.log (w j ρ) - Real.log (bN D ρ j) ≤ 1 / sc.x := by
    rw [← Real.log_div hw0.ne' hBpos.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hw0 hBpos)
    have h2 : w j ρ / bN D ρ j - 1 ≤ 1 / sc.x := by
      rw [div_sub_one hBpos.ne', div_le_div_iff₀ hBpos (by linarith)]
      have h4 := (abs_le.mp habs).2
      have h3 : (w j ρ - bN D ρ j) * sc.x ≤ bN D ρ j := by rwa [le_div_iff₀ (by linarith)] at h4
      linarith
    linarith
  have hlogW : Real.log (w j ρ) ≤ 2 * sc.L := by
    have h1 : Real.log (w j ρ) ≤ Real.log (2 * sc.b) := Real.log_le_log hw0 hwl
    have h2 : Real.log (2 * sc.b) = Real.log 2 + sc.L := by
      unfold Scale.b
      rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp]
    have h3 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  have hx1 : 0 < 1 / sc.x := one_div_pos.mpr (by linarith)
  have hkx : ((D.R.k : ℝ) - 1) * (1 / sc.x) ≤ (D.R.k : ℝ) / sc.x := by
    have e : ((D.R.k : ℝ) - 1) * (1 / sc.x) = (D.R.k : ℝ) / sc.x - 1 / sc.x := by ring
    linarith
  have hmul : ((D.R.k : ℝ) - 1) * (Real.log (w j ρ) - Real.log (bN D ρ j)) ≤
      ((D.R.k : ℝ) - 1) * (1 / sc.x) :=
    mul_le_mul_of_nonneg_left hratio (by linarith)
  nlinarith

theorem place_dimension_lower_bound (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (h2k : Real.log (2 * (D.R.k : ℝ)) ≤ sc.L)
    (hx : 2 * (Real.log 8 + 1 + Real.log sc.x) ≤ sc.L) (u : D.what₂.Word) (ρ : D.what₂.Tau)
    (h3 : (2 / 3 : ℝ) * dimV (rowLam D ρ) ≤ D.dsig ρ) :
    Real.log (2 / 3) + ((D.R.k : ℝ) - 1) * ∑ j ∈ range D.R.m, Real.log (bN D ρ j) - 5 * D.R.k * sc.L ≤
      Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) := by
  have hP := place_data_under_section_B D sc C0 Δ w hB u ρ
  have hm2 := D.R.two_le_m
  have hk5 := D.R.m_add_three_le_k
  have hΔ : 1 ≤ Δ := by
    unfold DataB at hB
    exact hB.2.2.2.2.2.2.1
  have hx1 : (1 : ℝ) ≤ sc.x := sc.one_lt_alt.le
  obtain ⟨hvu, hvr, hVV⟩ := Formalism.LogVandermondeBounds.StandardLattice.VandPlace_holds sc.eps sc.x sc.eps_pos hx1 D.R.k D.R.m Δ
    (uN D u ρ) (vN D ρ) (bN D ρ) (fun j => w j ρ) (by omega) (by omega) hΔ hP
  have hfac : 0 < facProd D.R.r := Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  have hvandu : vand (uColR D u ρ) = Formalism.LogVandermondeBounds.StandardLattice.vandN (uN D u ρ) D.R.k := by
    rw [column_param_eq_fun, vandermonde_fin_eq_nat]
  have hdimrow : dimV (rowLam D ρ) =
      Formalism.LogVandermondeBounds.StandardLattice.vandN (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) (D.R.k - 1 + D.R.m) /
        facProd D.R.r := by
    rw [dim_weyl_line_eq, rank_eq_sum]
    rfl
  set A := Formalism.LogVandermondeBounds.StandardLattice.vandN (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) (D.R.k - 1 + D.R.m) with hAdef
  set U := Formalism.LogVandermondeBounds.StandardLattice.vandN (uN D u ρ) D.R.k with hUdef
  have hdsig : (2 / 3 : ℝ) * (A / facProd D.R.r) ≤ D.dsig ρ := by
    rw [← hdimrow]
    exact h3
  have hA' : (2 / 3 : ℝ) * A ≤ D.dsig ρ * facProd D.R.r := by
    have := mul_le_mul_of_nonneg_right hdsig hfac.le
    rwa [mul_assoc, div_mul_cancel₀ _ hfac.ne'] at this
  have hdivle : (2 / 3 : ℝ) * A / U ≤ D.dsig ρ * facProd D.R.r / U := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hA' (inv_nonneg.mpr hvu.le)
  have hlog1 := Real.log_le_log (div_pos (mul_pos (by norm_num) hvr) hvu) hdivle
  rw [Real.log_div (mul_pos (by norm_num) hvr).ne' hvu.ne', Real.log_mul (by norm_num) hvr.ne'] at hlog1
  have hLd : sc.L = sc.x ^ sc.eps := rfl
  have h8 : Real.log (8 * (sc.x * Real.exp (sc.x ^ sc.eps))) = Real.log 8 + Real.log sc.x + sc.L := by
    rw [Real.log_mul (by norm_num) (mul_pos (by linarith) (Real.exp_pos _)).ne',
      Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, hLd]
    ring
  rw [h8] at hVV
  have hkpos : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
  have hlogk : Real.log D.R.k ≤ sc.L := le_trans (Real.log_le_log hkpos (by linarith)) h2k
  have hm1 := mul_le_mul_of_nonneg_left hx hkpos.le
  have hm2' := mul_le_mul_of_nonneg_left hlogk hkpos.le
  rw [hvandu]
  linarith

theorem log_X_lower_arithmetic (F K Mm Lr lv l2v G SL SG SP SW X lo : ℝ)
    (hF : 1 ≤ F) (hM : 44 ≤ Mm) (hMK : Mm ≤ K) (hL : 1 ≤ Lr) (hlv0 : 0 ≤ lv) (hlv : lv ≤ Lr) (hl2v : l2v ≤ Lr)
    (hG : 0 ≤ G) (hSL : -(F * (Mm - 1)) ≤ SL) (hSG : -2 ≤ SG)
    (hSPW : F * (-1 - 5 * K * Lr - (K + 2 * K * Lr)) ≤ SP - K * SW)
    (hid : F * K * X = F * ((Mm - 1) * K + Mm * (Mm - 1) / 2) * lv - F * ((Mm - 1) / 2) * l2v + SL +
      F * (Mm * (2 * K + Mm - 1) / 2) * G + F * SG + SP)
    (hlo : F * K * lo = K * SW + F * K * Mm * lv + F * K * Mm * G - 11 * F * K * Lr) : lo ≤ X := by
  have hK : 0 < K := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hFK : 0 < F * K := mul_pos (by linarith) hK
  have hMM : 0 ≤ Mm * (Mm - 1) / 2 := by nlinarith
  have key : F * K * (X - lo) = F * (Mm * (Mm - 1) / 2) * lv - F * K * lv - F * ((Mm - 1) / 2) * l2v +
      SL + F * (Mm * (Mm - 1) / 2) * G + F * SG + (SP - K * SW) + 11 * F * K * Lr := by
    linear_combination hid - hlo
  have hQ : 0 ≤ 3 * K * Lr - (Mm - 1) / 2 * Lr - Mm - 2 - K := by
    nlinarith [mul_le_mul_of_nonneg_right hMK (by linarith : (0 : ℝ) ≤ Lr),
      mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ K),
      mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ Mm)]
  have h1 : 0 ≤ F * (Mm * (Mm - 1) / 2) * lv := mul_nonneg (mul_nonneg hF0 hMM) hlv0
  have h2 : F * K * lv ≤ F * K * Lr := mul_le_mul_of_nonneg_left hlv hFK.le
  have h3 : F * ((Mm - 1) / 2) * l2v ≤ F * ((Mm - 1) / 2) * Lr :=
    mul_le_mul_of_nonneg_left hl2v (mul_nonneg hF0 (by linarith))
  have h4 : 0 ≤ F * (Mm * (Mm - 1) / 2) * G := mul_nonneg (mul_nonneg hF0 hMM) hG
  have h5 : F * (-2) ≤ F * SG := mul_le_mul_of_nonneg_left hSG hF0
  have h6 : 0 ≤ F * (3 * K * Lr - (Mm - 1) / 2 * Lr - Mm - 2 - K) := mul_nonneg hF0 hQ
  have hpos : 0 ≤ F * K * (X - lo) := by
    rw [key]
    nlinarith
  by_contra hlt
  push_neg at hlt
  have : F * K * (X - lo) < 0 := mul_neg_of_pos_of_neg hFK (by linarith)
  linarith

end Formalism.MainNotions.StandardLattice
