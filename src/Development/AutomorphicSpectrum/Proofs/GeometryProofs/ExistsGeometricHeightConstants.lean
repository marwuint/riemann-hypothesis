import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspHeightUpper
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeSum
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDegreeLower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopNine

theorem nineGeoU_of_given (hG : Top.Given) (hW : Out.WeilSt) (hF : Fl.FlatDegree) :
    ∃ Ch Cu : ℝ, NineGeoU Ch Cu := by
  obtain ⟨Ch, hCh⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.TopHt.htU_of_given hG hF
  obtain ⟨Cu, hCu⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.top_mean_cusp_weight hG
  refine ⟨Ch, Cu, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U M S' hII hAdm hU hT
  exact ⟨_root_.GlobalTheory.CompanionTheory.Relay.intersection_degree_lower hG hW E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U M S' hII hAdm hT,
    hCh E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U M S' hII hAdm hU hT,
    hCu E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ U hII hAdm hU⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.TopNine
