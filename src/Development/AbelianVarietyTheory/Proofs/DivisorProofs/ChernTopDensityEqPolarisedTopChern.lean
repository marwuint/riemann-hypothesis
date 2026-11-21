import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeFormCoeffChernPolyEqPolarised

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem chernTop_eq_mixTop {n m : ℕ} (G : V n → Mat (fun _ : Unit => m) ℂ) (v : V n) :
    chernTop (MvPolynomial.X ((), n)) G v =
      (Real.pi ^ n)⁻¹ * (mixTop fun _ => curvAt (fun u => G u ()) v).re := by
  rw [chernTop, MvPolynomial.aeval_X, _root_.GlobalTheory.GoodTop.topCoeff_chernPoly_eq_mixTop]

end GlobalTheory.GoodTop
