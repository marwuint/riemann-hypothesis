import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernTensorAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernDualNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIsometricEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernRealClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernFlagIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormSqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedFirstChernSumIndep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcOmegaFormEqC2SubC1Product
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsMapHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernFormPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFirstChernGradedPullback
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LineForm

theorem basicForms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    (∀ L M : HermLB p, (hX.atlas σ).IsRealForm 1 (fld _ (c1F hX σ L)) ∧ (hX.atlas σ).del (fld _ (c1F hX σ L)) = 0 ∧
      (hX.atlas σ).dbar (fld _ (c1F hX σ L)) = 0 ∧ c1F hX σ (L.tens M) = c1F hX σ L + c1F hX σ M ∧ c1F hX σ L.dual = -c1F hX σ L ∧
      (L.Isometric M → c1F hX σ L = c1F hX σ M)) ∧
    (∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2),
      (hX.atlas σ).IsRealForm 1 (fld _ (omF hX σ h fl)) ∧ (hX.atlas σ).IsRealForm 2 (fld _ (c2F hX σ h fl)) ∧
      (hX.atlas σ).del (fld _ (c2F hX σ h fl)) = 0 ∧ (hX.atlas σ).dbar (fld _ (c2F hX σ h fl)) = 0 ∧
      c2F hX σ h fl = c2F hX σ h fl' ∧ omF hX σ h fl * omF hX σ h fl = 0 ∧
      c1F hX σ (VMetric.grLB fl 0 H) + c1F hX σ (VMetric.grLB fl 1 H) = c1F hX σ (VMetric.grLB fl' 0 H) + c1F hX σ (VMetric.grLB fl' 1 H) ∧
      (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) =
        fld _ (c2F hX σ h fl - c1F hX σ (VMetric.grLB fl 0 H) * c1F hX σ (VMetric.grLB fl 1 H))) ∧
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
      (hX.atlas σ).IsHolo (hY.atlas σ) (GlobalTheory.Points.PtsOver.map π w _) ∧
      (∀ L : HermLB p, fld _ (c1F hY σ (L.pull π w)) = pullF hX hY σ π w (fld _ (c1F hX σ L))) ∧
      ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
        fld _ (c2F hY σ (h.pull π w) fl') = pullF hX hY σ π w (fld _ (c2F hX σ h fl)) ∧
        c1F hY σ (VMetric.grLB fl' 0 (H.pull π w)) + c1F hY σ (VMetric.grLB fl' 1 (H.pull π w)) =
          c1F hY σ ((VMetric.grLB fl 0 H).pull π w) + c1F hY σ ((VMetric.grLB fl 1 H).pull π w) := by
  intro k _ X _ p D hX σ
  refine ⟨fun L M => ⟨(_root_.GlobalTheory.LineForm.FirstChern.c1F_isRealForm_closed k X p D hX σ L).1, (_root_.GlobalTheory.LineForm.FirstChern.c1F_isRealForm_closed k X p D hX σ L).2.1, (_root_.GlobalTheory.LineForm.FirstChern.c1F_isRealForm_closed k X p D hX σ L).2.2,
    _root_.GlobalTheory.LineForm.c1F_tens k X p D hX σ L M, _root_.GlobalTheory.LineForm.c1F_dual k X p D hX σ L, GlobalTheory.T.firstChern_isometric_eq k X p D hX σ L M⟩,
    fun E h H fl fl' => ⟨_root_.GlobalTheory.LineForm.isRealForm_omF k X p D hX σ E h H fl, (_root_.GlobalTheory.ChernReal.c2F_isRealForm_closed k X p D hX σ E h H fl).1, (_root_.GlobalTheory.ChernReal.c2F_isRealForm_closed k X p D hX σ E h H fl).2.1,
      (_root_.GlobalTheory.ChernReal.c2F_isRealForm_closed k X p D hX σ E h H fl).2.2, _root_.GlobalTheory.LineForm.c2F_flag_indep k X p D hX σ E h H fl fl', _root_.GlobalTheory.LineForm.omF_mul_self k X p D hX σ E h H fl,
      _root_.GlobalTheory.c1F_grLB_add_grLB_flag_indep k X p D hX σ E h H fl fl', _root_.GlobalTheory.LineForm.ddc_omF_eq k X p D hX σ E h H fl⟩,
    fun Y p' D' hY π w => ⟨_root_.GlobalTheory.LineForm.isHolo_ptsOver_map k X p D hX σ Y p' D' hY π w, _root_.GlobalTheory.ChernPull.c1F_pull_eq_pullF_c1F k X p D hX σ Y p' D' hY π w,
      fun E h H fl fl' => ⟨_root_.GlobalTheory.SecondChernPull.c2F_pull_eq_pullF_c2F k X p D hX σ Y p' D' hY π w E h H fl fl', _root_.GlobalTheory.LineForm.c1F_grLB_sum_pullback_eq_pullback_sum k X p D hX σ Y p' D' hY π w E h H fl fl'⟩⟩⟩

end GlobalTheory.LineForm
