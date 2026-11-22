import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThinSizeDominatesAtLargeScale
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopSizeAddLeThreeHalvesScale
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleLogMulLeSizeRatio
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem roomy_of_large : ∀ eps C A : ℝ, 0 < eps → 100 ≤ C → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → Roomy L C := by
  intro eps C A he hC
  have hC0 : (0 : ℝ) ≤ C := by linarith
  obtain ⟨x1, h1⟩ := _root_.GlobalTheory.HTW.thinSize_dominates eps he
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.scale_log_mul_b'_le_b eps C (max A 0) he hC0 (le_max_right _ _)
  refine ⟨max (max x1 x2) 4, fun D L P hL hA hx => ?_⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx4 : (4 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  obtain ⟨a1, a2, a3⟩ := h1 D L P hL hx1
  refine ⟨hC, a1, a2, a3, _root_.GlobalTheory.Ggeo.bT_add_div_le_three_halves D L P hx4, ?_⟩
  have hb : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg (by linarith)
  have hw : (D.host.Lw : ℝ) ≤ max A 0 * Real.log L.sc.x :=
    P.Lw_le.trans (mul_le_mul_of_nonneg_right (hA.trans (le_max_left _ _)) hlog)
  refine le_trans ?_ (h2 L.sc hL hx2)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC0) hb

end GlobalTheory.HTW
