import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerIntAtOfSeriesRat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsTowerCover
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels

namespace GlobalTheory

theorem serInt_outright : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP
  exact ⟨fun u hu c0 hc0 => GlobalTheory.LevelSeries.serIntAt_record D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP u hu c0 hc0, _root_.GlobalTheory.DescIntRoad.descIntAt_of_laws D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP⟩

end GlobalTheory
