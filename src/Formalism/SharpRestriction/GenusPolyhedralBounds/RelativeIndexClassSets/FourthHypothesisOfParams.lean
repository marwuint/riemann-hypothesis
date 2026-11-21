import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NonvanishingSectionCondition
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

section Run

variable (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L)

theorem A_le_kf : (D.R.f : ℝ) * D.R.r ≤ 2 * ((D.R.k : ℝ) * D.R.f) := by
  have h1 : D.R.r ≤ 2 * D.R.k := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have h2 : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  linarith

theorem fourth_hypothesis_of_params : L.sc.b ≤ (runOf T S hZ).ka.size ∧ (T.TO : ℝ) * (runOf T S hZ).wL.size ≤ 2 * (runOf T S hZ).ka.size ∧
    (runOf T S hZ).wF.size ≤ ((WeightFamilies.dimY D D.R.m : ℝ) + 2) * (runOf T S hZ).wL.size + 5 * D.R.f * (D.R.r : ℝ) ^ 2 * T.TO ∧
    WeightFamilies.PPv D L T.CP T.eP ^ 3 * (T.TO : ℝ) ^ 2 ≤ L.sc.b ∧ WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP ≤ L.sc.b ∧
    (∀ i, 2 * DF (runOf T S hZ).ka + 2 < D.host.g i) := by
  have hR := rn_of T S hZ
  have hbk := b_le_ka T S hZ
  have hTb : (T.TO : ℝ) ≤ L.sc.b := hR.toBs.TO_le_sb.trans hR.toBs.sb_le_b
  refine ⟨hbk, ?_, ?_, ?_, ?_, fun i => ?_⟩
  · have := (runOf T S hZ).T_wL_le
    have e : ((runOf T S hZ).T : ℝ) = (T.TO : ℝ) := rfl
    rw [e] at this
    linarith
  · have h := (runOf T S hZ).wF_size_le
    have e : ((runOf T S hZ).nP : ℝ) = (T.nP : ℝ) := rfl
    rw [e] at h
    have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
    have hr := hR.r6; have hT := hR.one_le_order_alt; have hn := hR.nPW; have hn2 := hR.nW_le
    have a0 : (0 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by positivity
    have a1 : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * 1 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * T.TO := mul_le_mul_of_nonneg_left hT a0
    have a2 : (D.R.f : ℝ) * D.R.r * T.nP ≤ (D.R.f : ℝ) * D.R.r * T.TO :=
      mul_le_mul_of_nonneg_left (hn.trans hn2) (by positivity)
    have a3 : (D.R.f : ℝ) * D.R.r * T.TO ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * T.TO := by
      have : (D.R.f : ℝ) * D.R.r ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have a4 : (1 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by nlinarith
    have e2 : ((Dm D : ℕ) : ℝ) = (WeightFamilies.dimY D D.R.m : ℝ) := rfl
    rw [e2] at h
    nlinarith
  · rw [WeightFamilies.PPv_rec T]
    exact hR.h32.trans hR.toBs.sb_le_b
  · rw [WeightFamilies.PPv_rec T, eRR, ← hR.sb_sq]
    exact mul_le_mul (hR.toBs.rd_pow_le (by norm_num)) hR.toBs.PP_le_sb hR.PP_pos.le hR.sb_pos.le
  · have h1 : (DF (runOf T S hZ).ka : ℝ) ≤ 4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b :=
      (DF_le_size _).trans (ka_le T S hZ)
    have h2 := hR.g_gt h1 (g_ge P i)
    exact_mod_cast h2

end Run

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
