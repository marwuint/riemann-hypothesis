import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSmallSecHermitianLineBundleArithVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundSemiPosNefOnFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithNefVolumeUpperBound
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem arithHilbertSamuel_of_ampleHS :
    GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → GlobalTheory.Published.ArithHilbertSamuel := by
  intro hC hA hS k _ X _ p D hX L N a hL ha
  refine ⟨Eventually.of_forall fun m => _root_.GlobalTheory.SmallFin.smallSec_finite k X p D hX _, ?_⟩
  refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
  filter_upwards [_root_.GlobalTheory.NefUpper.main hC hA hS k X p D hX L N a hL ha c hc,
    _root_.GlobalTheory.HSNef.LowerNef.main hC hA k X p D hX L N a (nefFib_of_isNef hL) hL.semiPos ha c hc] with m h1 h2
  have hm : ‖(m : ℝ) ^ (D + 1)‖ = (m : ℝ) ^ (D + 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs, hm, abs_le]
  constructor <;> linarith

end GlobalTheory.HSNef
