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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegralIoiFsDensRadial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassLineBundleWeightOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralTopIndependentOfSmoothWeight

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory

theorem chernInt_indep_of_iso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) A), LBIso L A → φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := by
  intro Y L A φ ψ hLA hφ hψ
  obtain ⟨w, hw⟩ := hLA
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.ChernIso.chernMass_ofIso Y L A φ ψ.isLB w hw hφ
  rw [← h2]
  exact _root_.GlobalTheory.ChernMass.chernInt_one_eq Y A _ ψ h1 hψ

end GlobalTheory
