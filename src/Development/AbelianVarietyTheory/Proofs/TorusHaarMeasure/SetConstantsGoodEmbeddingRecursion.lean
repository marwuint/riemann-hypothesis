import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpC
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Formalism.LocalToGlobal.ProjectiveLattices.ESecPfA
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SubMul
import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitRecord
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspEqZeroOfGenericValues
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.TranscendenceDegreeRatiosCuspFormsComponents
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

noncomputable section

namespace GlobalTheory.BigRec

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem bigAt_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (c : ℝ) (large₂ : SizeData₂ D) (CK C1 A1 h0 : ℝ) (Tn nP nW : ℕ), SetC large₂ (recPlus h j hj) CK C1 A1 ka wL wF Tn nP nW h0 → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) → (j < D.R.m → 0 < G.iet ∧ (recPlus h j hj).NonZeroComp _ G.et ∧ ∃ σ, GoodEmb T.Q.c σ ∧ PhRec h j σ G.w G.iet G.et c) → 0 ≤ c → 2 * c * g0 D ≤ 1 → (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th : (recB h.toLawsCore).Cusp j w1, (recPlus h j hj).NonZeroComp w1 th) → BigAt h j hj hG G := by
  intro D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hE hc hcg _
  exact ⟨hN, _root_.GlobalTheory.BigTrdeg.trdeg_ratios_record D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hE hc hcg⟩

end GlobalTheory.BigRec
