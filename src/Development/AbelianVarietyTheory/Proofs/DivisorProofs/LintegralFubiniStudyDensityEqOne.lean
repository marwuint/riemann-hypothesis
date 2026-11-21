import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvPowAddNormSqComplexSpace

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem lintegral_fubiniStudy_density_eq_one : ∀ n : ℕ, ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n,
    ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) = 1 := by
  intro n
  have hc : (0 : ℝ) ≤ n.factorial / Real.pi ^ n := by positivity
  have hmeas : Measurable fun v : ReciprocityTheory.L2DbarEstimates.V n =>
      ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) := by fun_prop
  have hsplit : ∀ v : ReciprocityTheory.L2DbarEstimates.V n,
      ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) =
        ENNReal.ofReal (n.factorial / Real.pi ^ n) *
          ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) := fun v => ENNReal.ofReal_mul hc
  simp_rw [hsplit]
  rw [lintegral_const_mul _ hmeas]
  have hV : ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n, ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) =
      ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((1 + ∑ i, ‖z i‖ ^ 2) ^ (n + 0 + 1))⁻¹) := by
    rw [← (FinChart.measurePreserving_toV (D := n)).lintegral_comp hmeas]
    congr 1
    funext z
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [hV, _root_.GlobalTheory.ComplexSpaceIntegral.lintegral_inv_pow_add_sum_norm_sq n 0 1 one_pos, ← ENNReal.ofReal_mul hc]
  have hpi : Real.pi ^ n ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [show (n.factorial : ℝ) / Real.pi ^ n * (Real.pi ^ n * (Nat.factorial 0 : ℝ) /
      (((n + 0).factorial : ℝ) * 1 ^ (0 + 1))) = 1 by
    simp only [Nat.factorial_zero, Nat.cast_one, add_zero, one_pow, mul_one]
    field_simp]
  exact ENNReal.ofReal_one

end GlobalTheory
