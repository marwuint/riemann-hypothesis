import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicAndBlockOneNondegenerate

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.units_cohomology_bijective : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ i : ℤ, Function.Bijective (gmPhi q T i) := GlobalTheory.EtC.GmAicDeg1.main
