import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntPullFubiniStudyEqZeroOfNotDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFubiniStudyTotal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqDegreeMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionPullbackEqZeroOfNotDominantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassPullMulDegreeField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceIntegralSmoothProjectiveDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointNeZeroProjectiveSameDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionO1ProjectiveStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FubiniStudyPull

theorem fubiniStudy_pullback_chern_mass_eq_degree : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim)
    (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str),
    Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ
      (fun _ => 1) = (topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℝ) := by
  intro Y π hπ
  obtain ⟨hPI, hPdim, hPproj, hPsm⟩ := _root_.GlobalTheory.pspace_integral_dim_proj_smooth ℂ Y.dim
  haveI := hPI
  by_cases hη : π (genericPoint Y.X) = genericPoint (PSpace ℂ Y.dim)
  · have hδ := _root_.GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim hPproj
      Y.isProjOver hPdim Y.topologicalKrullDim_eq π hπ hη
    have hm := fun ε => _root_.GlobalTheory.ChernMassPull.mass ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str (RingHom.id ℂ)
      Y.dim hPproj Y.isProjOver hPsm π hπ hη hδ (ProjSpace.hermitianTwistingSheaf ℂ Y.dim).B
      ((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)) ((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).cInf _) ε
    obtain ⟨h1, h0⟩ := _root_.GlobalTheory.FSMass.chern_mass_hermitian_O_one_projective Y.dim
    have hi := GlobalTheory.T.topSelfIntersection_pullback_eq_degree_mul ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim hPproj
      Y.isProjOver hPdim.le π hπ hη hδ (ProjSpace.O1 ℂ Y.dim) (ProjSpace.O1_isLB ℂ Y.dim)
    have ht := GlobalTheory.T.top_self_intersection_O1_projective ℂ Y.dim
    rw [GdegPullProof.chernInt_one, hm 1, hm (-1), h1, h0]
    change _ = ((topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℤ) : ℝ)
    rw [hi, ht]
    simp
  · have hc := _root_.GlobalTheory.chernInt_pull_fubiniStudy_eq_zero_of_not_dominant Y π hπ ⟨genericPoint (PSpace ℂ Y.dim), fun h =>
      hη (h.antisymm (genericPoint_specializes _)).eq⟩
    have hn := GlobalTheory.T.topSelfIntersection_pullback_eq_zero_of_not_dominant ℂ (PSpace ℂ Y.dim) Y.X (PSpace.str ℂ Y.dim) Y.str Y.dim Y.isProjOver
      hPdim.le Y.topologicalKrullDim_eq.le π hη (ProjSpace.O1 ℂ Y.dim) (ProjSpace.O1_isLB ℂ Y.dim)
    rw [hc]
    change (0 : ℝ) = ((topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℤ) : ℝ)
    rw [hn]
    simp

end GlobalTheory.FubiniStudyPull

end
