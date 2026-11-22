import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceTateTwistStrictlyHenselian
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homotopyInvariance_tateTwist_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := GlobalTheory.homotopyInvariance_strictlyHenselian
