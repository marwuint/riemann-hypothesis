import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCptGenResidueFieldGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCptGen_residue_field_generic : ∀ (X : Scheme.{0}), (∀ x : X, IsDomain (X.presheaf.stalk x)) → ∀ x : X, (∀ y : X, y ⤳ x → y = x) → IsCptGen (Ω := X.residueField x) (X.fromSpecResidueField x) := by
  exact @GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal
