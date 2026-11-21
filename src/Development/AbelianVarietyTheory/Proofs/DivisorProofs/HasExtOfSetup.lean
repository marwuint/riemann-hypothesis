import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentDataChartsCommon
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDescentSeparatedEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocalGroups
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGroupRangeUnionClosedFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem Setup.hasExt (σ : Setup) : HasExt (awayMap σ.f) σ.A := by
  have hc : σ.Common := _root_.GlobalTheory.Desc.setup_common σ
  obtain ⟨E⟩ := _root_.GlobalTheory.Desc.nonempty_emb σ hc
  exact _root_.GlobalTheory.Desc.Emb.hasExt_of_locGrp σ E hc (_root_.GlobalTheory.Desc.UnionLocal.exists_locGrp_range_eq σ E hc)

theorem hasExt_of_setup : ∀ σ : Setup, HasExt (awayMap σ.f) σ.A := Setup.hasExt

end GlobalTheory.Desc
