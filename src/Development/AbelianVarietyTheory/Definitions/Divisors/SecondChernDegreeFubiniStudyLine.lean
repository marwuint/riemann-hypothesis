import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalInnerProductLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSurjectiveLine
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricIsometricOfIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame

namespace GlobalTheory.ChTwoModel

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem quot_eq_map {S : ShortComplex X.Modules} (h : Met p σ S.X₂ (0 + 1)) (hS : S.ShortExact)
    (h₁ : IsVB S.X₁ 0) (h₃ : IsVB S.X₃ 1) [IsIso S.g] :
    h.quot hS h₁ h₃ = h.map (asIso S.g) := Met.ext_of_exists fun y => by
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  refine ⟨a.quot, ha, ?_⟩
  rw [h.quot_G hS h₁ h₃ a ha]
  ext i j
  refine Eq.trans ?_ (((h.map (asIso S.g)).form_frame a.quot ha i j).symm.trans
    (h.form_map (asIso S.g) (a.t i) (a.t j) ha)).symm
  simp [quotGram, toBlocks₂₂, Met.gram, VBExt.AdaptedChart.frame]

end GlobalTheory.ChTwoModel
