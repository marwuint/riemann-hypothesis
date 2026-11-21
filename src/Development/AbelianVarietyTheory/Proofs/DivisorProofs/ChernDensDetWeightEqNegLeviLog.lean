import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxE

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CurveDens

theorem cHess_apply_eq_ddbar {n : ℕ} {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hg : ContDiffAt ℝ 2 g x) (j k : Fin n) :
    ReciprocityTheory.L2DbarEstimates.cHess n g x j k =
      ddbar g x (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) := by
  have e : ReciprocityTheory.L2DbarEstimates.wdb n k g = fun y => dbar g y (EuclideanSpace.single k 1) := by
    funext y
    simp only [ReciprocityTheory.L2DbarEstimates.wdb, dbar_apply, ReciprocityTheory.L2DbarEstimates.bas, smul_eq_mul]
    ring
  rw [ddbar_eq_del_dbar hg, del_apply, ReciprocityTheory.L2DbarEstimates.cHess, Matrix.of_apply, e]
  simp only [ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas, smul_eq_mul]
  ring

end GlobalTheory.CurveDens

namespace GlobalTheory.CurveDens

end GlobalTheory.CurveDens
