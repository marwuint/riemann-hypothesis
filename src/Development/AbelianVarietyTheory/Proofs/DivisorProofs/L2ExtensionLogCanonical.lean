import Mathlib
import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
import ReciprocityTheory.L2DbarEstimates.NormFibrations.LseSmoothRIffReal
import ReciprocityTheory.L2DbarEstimates.NormFibrations.ImportsAlt
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFrameOffFiniteZeroSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionEtaleCoordinatesFiniteZeros

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem l2ExtensionLogCanonical' : GlobalTheory.Published.L2ExtensionLogCanonical := by
  intro n hn Y _ _ _ _ _ _ ι La _ A hH E L s hs hS hjac hle δ hδ hcurv f
  obtain ⟨Λ, τ, z, β, hdata⟩ := _root_.GlobalTheory.exists_etale_frame_of_finite_zeroSet n Y ι La A hn hH E L s hs hS
  exact _root_.GlobalTheory.l2_extension_of_etale_coordinates n Y ι La A hn E L s hs hS hjac hle δ hδ hcurv Λ τ z β hdata f

end GlobalTheory
