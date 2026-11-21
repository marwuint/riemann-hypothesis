import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetSer

theorem exists_index_of_local {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (e : Spec (CommRingCat.of R) ⟶ X) : ∃ j : L.ι, ⊤ ≤ e ⁻¹ᵁ L.U j := by
  have h : e (IsLocalRing.closedPoint R) ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨j, (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of R) e hj).ge⟩

end GlobalTheory.JetSer
