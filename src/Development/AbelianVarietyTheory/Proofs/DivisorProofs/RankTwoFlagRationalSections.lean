import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDensityExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricIsometricOfIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsoIsometric
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondChernDegreeFubiniStudyLine

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier
open scoped Classical

namespace GlobalTheory.CovTest.SwapLine

open GlobalTheory.VB GlobalTheory.VMetric GlobalTheory.CurveDens GlobalTheory.CxPts

section TwoFlags

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {V : X.Modules}

def lineQuot (fl : Vert.Flag V 2) : V ⟶ fl.gr 1 :=
  have : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  inv (fl.ι (Fin.succ 1)) ≫ fl.π 1

theorem ι_lineQuot (fl : Vert.Flag V 2) : fl.ι (Fin.succ 1) ≫ lineQuot fl = fl.π 1 := by
  have : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  exact IsIso.hom_inv_id_assoc _ _

theorem line_lineQuot (fl : Vert.Flag V 2) : fl.ι 1 ≫ lineQuot fl = 0 := by
  have e : fl.step 1 ≫ fl.ι (Fin.succ 1) = fl.ι 1 := fl.step_ι 1
  rw [← e]
  exact (Category.assoc _ _ _).trans ((congrArg (fl.step 1 ≫ ·) (ι_lineQuot fl)).trans
    (Limits.cokernel.condition _))

theorem shortExact_lineQuot (fl : Vert.Flag V 2) :
    (ShortComplex.mk (fl.ι 1) (lineQuot fl) (line_lineQuot fl)).ShortExact := by
  have : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  exact ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := stepSeq fl 1)
    (S₂ := ShortComplex.mk (fl.ι 1) (lineQuot fl) (line_lineQuot fl)) (Iso.refl _)
    (asIso (fl.ι (Fin.succ 1))) (Iso.refl _) ((Category.id_comp _).trans (fl.step_ι 1).symm)
    ((ι_lineQuot fl).trans (Category.comp_id _).symm)) (stepSeq_shortExact fl 1)

variable {h : VMetric p V 2} (H : h.IsCInf)

theorem isometric_grLB_zero (fl : Vert.Flag V 2) :
    (VMetric.det (H.restrict (fl.isSubbundle 1) (fl.isVB 1))).Isometric (grLB fl 0 H) := by
  have hS₀ := stepSeq_shortExact fl 0
  have i₂ : IsIso (stepSeq fl 0).g := hS₀.isIso_g_iff.2 (isVB_zero_iff.1 (fl.isVB (Fin.castSucc 0)))
  exact det_isometric_of_isIsometry k X p _ _ 1 (h.stepMet fl 0) (h.grMet fl 0) (H.restrict _ _)
    (H.grMet fl 0) (asIso (stepSeq fl 0).g) ((isIsometry_iff _).2 (VMetric.ext
      (funext fun σ => ChTwoModel.quot_eq_map ((h.stepMet fl 0).met σ) hS₀
        (fl.isVB (Fin.castSucc 0)) _)))

theorem isometric_grLB_one (fl : Vert.Flag V 2) :
    (VMetric.det (IsCInf.quot (S := .mk _ _ (line_lineQuot fl)) (r := 1) (s := 1) (shortExact_lineQuot fl)
      (fl.isVB 1) (fl.isVB_gr 1) H)).Isometric (grLB fl 1 H) := by
  have : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  exact (isometric_detQuot_and_bcInt_eq_of_iso k X p (stepSeq fl 1) (.mk _ _ (line_lineQuot fl)) 1 1
    (h.stepMet fl 1) h (H.restrict _ _) H (stepSeq_shortExact fl 1) (shortExact_lineQuot fl)
    (fl.isVB (Fin.castSucc 1)) (fl.isVB_gr 1) (fl.isVB 1) (fl.isVB_gr 1) (Iso.refl _)
    (asIso (fl.ι (Fin.succ 1))) ((Category.id_comp _).trans (fl.step_ι 1).symm)
    fun σ U s t y hy => ((h.met σ).form_restrict (fl.isSubbundle _) _ s t hy).symm).1.symm

end TwoFlags

end GlobalTheory.CovTest.SwapLine

end
