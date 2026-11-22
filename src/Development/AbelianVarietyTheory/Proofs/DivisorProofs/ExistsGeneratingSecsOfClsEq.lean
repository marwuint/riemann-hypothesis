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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.CechPic

theorem exists_generating_secs_of_cls_eq : ∀ (X : Scheme.{0}) (L A : LB X) (hL : L.IsLB) (hA : A.IsLB), cls L hL = cls A hA → ∀ (ι : Type) (u : ι → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∃ v : ι → A.Sec, ⨆ i, nonzeroLocus (v i) = ⊤ := by
  intro X L A hL hA h ι u hu
  have hiso : LBIso A L := (cls_eq_iff hA hL).1 h.symm
  choose v hv using fun i => GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso hA hL hiso (u i)
  refine ⟨v, ?_⟩
  simp only [hv]
  exact hu

end GlobalTheory.CechPic
