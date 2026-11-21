import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyFrameNearComplexPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChart
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isGramPair_of_isMetricFr : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H H' : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → IsMetricFr E H' → ∀ τ, IsGramPair (atlas X σ) (gramAt E H τ) (gramAt E H' τ) := by
  intro F _ σ X ι _ m k E H H' hH hH' τ
  have hA (y : CxPts X.str σ) := (E.nonempty (under y)).choose_spec
  refine ⟨fun y => ⟨(_root_.GlobalTheory.ChernCalc.isMetricFr_smoothUnitAt F σ X ι m k E H hH y _ (hA y) τ).1,
    (_root_.GlobalTheory.ChernCalc.isMetricFr_smoothUnitAt F σ X ι m k E H' hH' y _ (hA y) τ).1⟩, fun y => ?_⟩
  filter_upwards [_root_.GlobalTheory.ChernCalc.frame_eventually_near F σ X ι m k E y _ (hA y)] with z hz
  have hP := (Fr.mem_iff hz).1 (hA z) τ
  have hT := _root_.GlobalTheory.ChernCalc.holUnitAt_ratVal F σ X (m τ) _ z (fun i j => mem_O_ratOf.1 (hP.1 i j)) hP.2.1 (mem_O_ratOf.1 hP.2.2.1)
  refine ⟨_, _, _, hT, hT, hT, ?_⟩
  filter_upwards [_root_.GlobalTheory.ChernCalc.frame_eventually_near F σ X ι m k E z _ hz, _root_.GlobalTheory.ChernCalc.frame_eventually_near F σ X ι m k E z _ (hA z)] with w h1 h2
  exact ⟨hH.trans w _ h1 _ h2 τ, hH'.trans w _ h1 _ h2 τ⟩

end GlobalTheory.ChernCalc
