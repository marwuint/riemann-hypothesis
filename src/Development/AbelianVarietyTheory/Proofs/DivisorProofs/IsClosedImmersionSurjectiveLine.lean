import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ArInt

noncomputable section

namespace GlobalTheory.FlagZ.Plane

theorem span_infty {A : Type} [CommRing A] : Ideal.span (Set.range (![0, 1] : Fin 2 → A)) = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨1, rfl⟩)

def infty : Sp ℤ ⟶ PSpace ℤ 1 := pt (RingHom.id ℤ) ![0, 1] span_infty

instance : IsClosedImmersion infty := by
  have : IsClosedImmersion (infty ≫ PSpace.str ℤ 1) := by
    rw [toZ_ext (infty ≫ _) (𝟙 _)]; infer_instance
  exact IsClosedImmersion.of_comp infty (PSpace.str ℤ 1)

end GlobalTheory.FlagZ.Plane
