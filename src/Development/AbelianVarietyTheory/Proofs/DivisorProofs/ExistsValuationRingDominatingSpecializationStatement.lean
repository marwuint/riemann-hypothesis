import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationRingDominatingSpecialization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationRing_dominating_specialization : ∀ (X : Scheme.{0}) (x' x : X), x' ⤳ x → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : ValuationRing V) (g : Spec (CommRingCat.of V) ⟶ X), g (IsLocalRing.closedPoint V) = x ∧ g (⊥ : PrimeSpectrum V) = x' := by
  exact @GlobalTheory.exists_valuationRing_of_specializes
