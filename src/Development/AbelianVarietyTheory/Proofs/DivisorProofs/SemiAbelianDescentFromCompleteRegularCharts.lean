import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocallyNormalNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianExtensionNearPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackCompletionChartToExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem descent_semiAbelian : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : S, Nonempty (Chart j A x)) → ∃ (G : Over S) (_ : GrpObj G) (e : A.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback A G j e ∧ ∀ (x : S) (C : Chart j A x), ∃ π : C.G.left ⟶ G.left, IsGrpPullback C.G G C.ξ π ∧ C.α ≫ e = pullback.fst C.G.hom (jK C.R) ≫ π := by
  intro X S _ hS j _ hj A _ hA L hL hamp hC
  have hloc := _root_.GlobalTheory.Desc.exists_hasExt_near X S hS j hj A hA L hL hamp hC
  obtain ⟨G, iG, e, hsemi, hpb⟩ := _root_.GlobalTheory.ExtGlue.hasExt_of_locally X S hS j hj A hA hloc
  exact ⟨G, iG, e, hsemi, hpb, fun x C => _root_.GlobalTheory.Desc.exists_grpPullback_chart_to_ext X S j hj A G e hsemi hpb x C⟩

end GlobalTheory.Desc
