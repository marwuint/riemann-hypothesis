import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFstUniqueSylvester
import Formalism.SatakeDualWeyl.Statement

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSignature_fst_unique_sylvester : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {a b a' b' : ℕ}, Formalism.UG.HasSignature J a b → Formalism.UG.HasSignature J a' b' → a = a' := by
  exact @GlobalTheory.SylvesterInertia.hasSignature_fst_unique
