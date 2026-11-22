import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeilStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.CovTop
theorem PublishedHodgeBundleTheorems.toClassicalTheorems : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.Hypotheses'' := fun h => h.toClassicalTheoremsOf GlobalTheory.T.toroidalFlagProportionality_of_goodChernWeil
end GlobalTheory.CovTop
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_topology_refinement : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.Hypotheses'' := by
  first | exact @_root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems | exact _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems | (intros; apply _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems <;> assumption)
end
