import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.LocRingPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.CurveSec
import Formalism.LocalToGlobal.ProjectiveLattices.LiftSec
import Formalism.LocalToGlobal.ProjectiveLattices.LiftModelHolds
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveModelExistsAllPrimesAllPoints
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CurveSectionStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LocStructStRecord
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionRatiosIntegral
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RealPtNZOfCurveHyp

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PrimeData

section General

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem ev_ne_zero_of_nonZeroComp (X : PJ D B P j) {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)]
    [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (hinj : ∀ (w : WeightFamilies.Wt D j) (g : B.Cusp j w), (∀ Z, gF Z (X.inc w g) = 0) → g = 0)
    {u : WeightFamilies.Wt D j} {F : B.Cusp j u} (hF : X.NonZeroComp u F) (Z : ι) {w : WeightFamilies.Wt D j} (g : B.Cusp j w)
    (hg : gF Z (X.inc w g) ≠ 0) (hg' : ∀ Z', Z' ≠ Z → gF Z' (X.inc w g) = 0) : gF Z (X.inc u F) ≠ 0 := by
  intro h0
  obtain ⟨H, hH⟩ := X.inc_mul u w F g
  have hH0 : H = 0 := by
    refine hinj _ H fun Z' => ?_
    rw [← hH, map_mul]
    by_cases hZ : Z' = Z
    · subst hZ
      rw [h0, zero_mul]
    · rw [hg' Z' hZ, mul_zero]
  rw [hH0, map_zero] at hH
  have := hF w g hH
  rw [this, map_zero, map_zero] at hg
  exact hg rfl

theorem ne_zero_of_nval_eq {T T' : CDVR} {e : ℕ} {x : T.Fr} {x' : T'.Fr} (hx : x ≠ 0)
    (h : nval T.V e x = nval T'.V e x') : x' ≠ 0 := by
  rintro rfl
  rw [nval_zero, nval_of_ne hx] at h
  exact EReal.coe_ne_top _ h

variable {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j}

theorem finiteDimensional_of_model {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
    {g0 : B.Cusp j wF} (C : CurveModel G la g0) :
    FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := by
  have : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥C.A' ⧸ C.JA) := C.fin
  exact LinearEquiv.finiteDimensional C.quotEquiv.toLinearEquiv

theorem isReduced_of_model {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
    {g0 : B.Cusp j wF} (C : CurveModel G la g0) : IsReduced (OsK (xplus X E hM) la G.w) := by
  have : IsReduced (↥C.A' ⧸ C.JA) := C.red
  exact isReduced_of_injective C.quotEquiv.symm.toRingHom C.quotEquiv.symm.injective

end General

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

include hT in

theorem nzAt_of_nonZeroComp (hV : GenValInjSt h j hG) (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BigAt h j hj hG G) {u : WeightFamilies.Wt D j}
    (F : (recB h.toLawsCore).Cusp j u) (hF : (recPlus h j hj).NonZeroComp u F) : NZAt hG (F : T.R j) := by
  intro Z
  obtain ⟨k, hk, -⟩ := hB.2 Z
  obtain ⟨g, e1, e2⟩ := hC Z wL (G.w k)
  have := ev_ne_zero_of_nonZeroComp (recPlus h j hj) (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    (fun w g hg => hV w g fun Z => (formsEvR_inc h j hj hG hT Z w g).symm.trans (hg Z)) hF Z g
    (fun h0 => hk (e1.symm.trans ((formsEvR_inc h j hj hG hT Z wL g).symm.trans h0)))
    (fun Z' hZ' => (formsEvR_inc h j hj hG hT Z' wL g).trans (e2 Z' hZ'))
  exact fun h0 => this ((formsEvR_inc h j hj hG hT Z u F).trans h0)

theorem fromW_ne_zero {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ]
    (hR : RealPtNZSt h j hj hG G la hU) (ζ : PtsG G la) :
    ∃ (y : (extAll h j hj).Pt' la) (hw : FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ y),
      ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), NZAt hG (F : T.R j) →
        hw.ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) ≠ 0 := by
  obtain ⟨y, Tc, ι, hl, hunr, ev, hu, hv, hdeg, hnz⟩ := hR ζ
  obtain ⟨hw⟩ := @fromW_of D (recB h.toLawsCore) T.G.P j (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)
    ka wL wF G la ζ (‹∀ ζ : PtsG G la, IsDVRAt ζ› ζ) y hU Tc ι hl hunr ev hu hv hdeg
  exact ⟨y, hw, fun w F hF => ne_zero_of_nval_eq (hnz w F hF) ((hv w F).symm.trans (hw.hv w F))⟩

end Inst

end GlobalTheory.PrimeData
