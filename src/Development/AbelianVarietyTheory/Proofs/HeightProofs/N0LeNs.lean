import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PageOKRun
import Development.AbelianVarietyTheory.Proofs.HeightProofs.XLeOfSqLeFMulR

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.RunJoin.InhAll
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Num GlobalTheory.RunJoin GlobalTheory.RunJoin.Inh
variable {D : D7} {j : ℕ}

def mu (D : D7) (j : ℕ) : ℝ := ((max (D.R.sigW j).2 1 : ℕ) : ℝ)

theorem one_le_mu : 1 ≤ mu D j := by
  unfold mu
  have : 1 ≤ max (D.R.sigW j).2 1 := le_max_right _ _
  exact_mod_cast this

theorem mu_le_r : mu D j ≤ D.R.r := by
  unfold mu
  have hr := Formalism.BasicNotions.Ranks.r_eq D.R
  have hk := Formalism.BasicNotions.Ranks.k_ge D.R
  have : max (D.R.sigW j).2 1 ≤ D.R.r := by
    show max (D.R.m - j) 1 ≤ D.R.r
    apply max_le <;> omega
  exact_mod_cast this

theorem size_eq (w : WeightFamilies.Wt D j) : w.size = DF w + D.R.f * mu D j * D.R.r * w.n + 1 := by
  simp only [WeightFamilies.Wt.size, DF, degP, mu]
  push_cast
  ring

theorem sig_add (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := by
  have hr := Formalism.BasicNotions.Ranks.r_eq D.R
  have hk := Formalism.BasicNotions.Ranks.k_ge D.R
  show (D.R.k + j - 1) + (D.R.m - j) = D.R.r
  omega

theorem dimY_eq_top (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : WeightFamilies.dimY D j = Dm D := by
  show WeightFamilies.dimY D j = WeightFamilies.dimY D D.R.m
  rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.dimY_m D]
  unfold WeightFamilies.dimY
  rw [GlobalTheory.ConstCompare.choose_two_add, sig_add h1 h2]

theorem n0_le_Ns (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : n0 D j ≤ D.R.r + 2 * g0 D * (Dm D + 1) := by
  have key : D.R.f * (D.R.sigW j).1 * (D.R.sigW j).2 ≤ D.R.f * ((D.R.sigW j).1 * (D.R.sigW j).2 +
      (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) / 2 + (D.R.sigW j).2 * ((D.R.sigW j).2 - 1) / 2) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  unfold n0
  rw [← dimY_eq_top h1 h2]
  unfold WeightFamilies.dimY
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right key 1)) _

theorem domAt_index {L : SizeData₂ D} {nW : ℕ} {CP : ℝ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (h : DomAt D L D.R.m nW CP) :
    DomAt D L j nW CP := by
  unfold DomAt at h ⊢
  obtain ⟨hC, hC20, hlam, hPN, hlog, hPU, hPO, _, hP12, hP73⟩ := h
  refine ⟨hC, hC20, hlam, hPN, hlog, hPU, hPO, ?_, hP12, ?_⟩
  ·
    have hn := n0_le_Ns (D := D) h1 h2
    have hd : Dm D = D.R.f * D.R.r.choose 2 := dimY_m D
    have hc : D.R.r.choose 2 ≤ D.R.r ^ 2 := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ _).trans (by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have hN : n0 D j ≤ D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * (D.R.f * D.R.r ^ 2 + 1) := by
      calc n0 D j ≤ D.R.r + 2 * g0 D * (Dm D + 1) := hn
        _ ≤ D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * (D.R.f * D.R.r ^ 2 + 1) := by
          rw [hd]; unfold g0; gcongr
    have hN' : (n0 D j : ℝ) ≤ (D.R.r : ℝ) + 2 * (2 * 5 ^ 4 * (D.R.r : ℝ)) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 + 1) := by
      exact_mod_cast hN
    have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
    have hr : (6 : ℝ) ≤ D.R.r := by exact_mod_cast r_ge D
    have hL : (1 : ℝ) ≤ L.sc.L := one_le_L L
    have hR3 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 3 := by positivity
    have hFR2 : (1 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by nlinarith
    have a1 : (D.R.r : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_left hFR2 (by linarith : (0 : ℝ) ≤ D.R.r)
      nlinarith
    have a2 : 64 * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 3) ≤ ((D.R.f : ℝ) * D.R.r) ^ 3 := by
      have h64 : (64 : ℝ) ≤ (D.R.f : ℝ) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right h64 hR3
      nlinarith
    have hFR : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by positivity
    have h3 : ((D.R.f : ℝ) * D.R.r) ^ 3 ≤ ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 3 := by
      apply pow_le_pow_left₀ hFR
      nlinarith
    have h4 : (D.R.r : ℝ) + 2 * (2 * 5 ^ 4 * (D.R.r : ℝ)) * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 + 1) ≤
        1000 * ((D.R.f : ℝ) * D.R.r) ^ 3 := by nlinarith
    have hZb : Zb D L = (D.R.f : ℝ) * D.R.r * L.sc.L := rfl
    rw [hZb]
    calc (n0 D j : ℝ) ≤ _ := hN'
      _ ≤ 1000 * ((D.R.f : ℝ) * D.R.r) ^ 3 := h4
      _ ≤ CP * ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 3 := mul_le_mul hC h3 (by positivity) (by linarith)
  · have e : DivisibilityWeightConstant D j = DivisibilityWeightConstant D D.R.m := by unfold DivisibilityWeightConstant; rw [dimY_eq_top h1 h2]
    rw [e]; exact hP73

theorem extra_le {A k b s PP TO rd r D2 nW nP q0 : ℝ} (h : Rn A k b s PP TO rd r D2 nW nP q0) {μ : ℝ} (hμ : μ ≤ r) :
    μ * A * (nP + TO * nW) ≤ A * b := by
  have hA := h.forty_eight_le_constant
  have hT := h.one_le_order_alt
  have hnW := h.nW_le
  have hn40 := h.forty_le_weight_count
  have hnP0 := h.projectivePointSizes
  have hnPW := h.nPW
  have hrA := h.rA
  have hr6 := h.r6
  have hb := h.sq_mul_sq_le
  have hTT := h.TO_le_sq
  have hX0 : 0 ≤ nP + TO * nW := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ TO) (by linarith : (0 : ℝ) ≤ nW)
    linarith
  have h1 : TO * nW ≤ TO ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hnW (by linarith)
  have hX : nP + TO * nW ≤ 2 * TO ^ 2 := by linarith
  have h3 : r * (nP + TO * nW) ≤ r * (2 * TO ^ 2) := mul_le_mul_of_nonneg_left hX (by linarith)
  have h5 : 2 * r ≤ A ^ 2 := by nlinarith
  have h4 : r * (2 * TO ^ 2) ≤ A ^ 2 * TO ^ 2 := by
    calc r * (2 * TO ^ 2) = (2 * r) * TO ^ 2 := by ring
      _ ≤ A ^ 2 * TO ^ 2 := mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
  have hrX : r * (nP + TO * nW) ≤ b := by linarith
  calc μ * A * (nP + TO * nW) ≤ r * A * (nP + TO * nW) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ (by linarith)) hX0
    _ = A * (r * (nP + TO * nW)) := by ring
    _ ≤ A * b := mul_le_mul_of_nonneg_left hrX (by linarith)

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

end GlobalTheory.RunJoin.InhAll
