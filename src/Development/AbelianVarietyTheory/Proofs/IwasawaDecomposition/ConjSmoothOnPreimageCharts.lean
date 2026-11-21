import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open ReciprocityTheory.L2DbarEstimates (V bas wd wdb leviV)
open Filter Topology
open scoped ContDiff

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

def conjV (n : ℕ) : V n ≃ₗᵢ[ℝ] V n := LinearIsometryEquiv.piLpCongrRight 2 fun _ => Complex.conjLIE

theorem conjV_apply (n : ℕ) (v : V n) (a : Fin n) : conjV n v a = starRingEnd ℂ (v a) := rfl

end GlobalTheory.ShFam
