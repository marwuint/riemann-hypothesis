import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingHomWittAlgClosureEqOfCongrModPrime
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_witt_algClosure_eq_of_congr_mod_prime : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W], 0 < n → (∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) → ∀ f g : W →+* Formalism.L2.G.Pend.WW p, (∀ x, (p : Formalism.L2.G.Pend.WW p) ∣ f x - g x) → f = g := by
  exact @GlobalTheory.ringHom_wittKbar_eq_of_modp
