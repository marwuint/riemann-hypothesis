import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleTrivialNearFibreFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumFrameCocycleUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatUnitCocycleLocallyCoboundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFrameInvariantUnderDescentDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfDescentInvariantFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBDescent

theorem exists_descent : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] (L : LB X), L.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, GlobalTheory.LBDescent.chart f L i j)ˣ), GlobalTheory.LBDescent.DescCompat f L φ → GlobalTheory.LBDescent.DescCocycle f L φ → ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  intro X Y f _ _ _ _ L hL φ hc hcoc
  refine _root_.GlobalTheory.LBDescent.exists_lb_of_invariant_frames f L hL φ fun y => ?_
  obtain ⟨V, hy, t, ht⟩ := _root_.GlobalTheory.LBDescent.exists_trivial_near_fibre f L hL y
  obtain ⟨c, hct, hcc⟩ := GlobalTheory.T.descentDatum_frame_cocycle_unit f L hL φ hc hcoc V t ht
  obtain ⟨V', hle, hy', u, hu⟩ := _root_.GlobalTheory.LBDescent.coboundary_locally_of_cocycle f V c hcc y hy
  exact ⟨V', hy', _root_.GlobalTheory.LBDescent.twist_frame_descent f L φ V t ht c hct V' hle u hu⟩

end GlobalTheory.LBDescent
