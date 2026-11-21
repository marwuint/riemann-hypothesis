import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisInvariantNbhdClosedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisQuotientInvariantOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientSmoothBaseChangeIsoClosedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueLocalDescentsNearClosedFibreGalois
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawDescendsGaloisInvariantOpen

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_near_galois_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∃ N : Near (spMap ρ) G', N.Law ∧ ∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ) := by
  intro R _ _ _ hR R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS U' a
  obtain ⟨H, hH, hall, hc, horb⟩ := _root_.GlobalTheory.Mum.exists_invariant_nbhd_closedFibre R hR R' ρ hF hG D D' hD A' G' hS U' a
  obtain ⟨X, π, hX, h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.Mum.exists_galois_quotient R hR R' ρ hF hG D D' hD A' G' hS U' a H hH horb
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.Mum.GlueNear.glue_near R hR R' ρ hF hG D D' hD A' G' hS U' a H hH hall hc X π hX h1 h2 h3 h4 h5
    (_root_.GlobalTheory.Mum.quotient_smooth_and_baseChange_iso R hR R' ρ hF hG D D' hD A' G' hS U' a H hH horb X π hX h1 h2 h3 h4 h5)
  exact ⟨N, _root_.GlobalTheory.Mum.law_of_galAct_invariant R hR R' ρ hF hG D D' hD A' G' hS U' a N hN, hN⟩

end GlobalTheory.Mum
