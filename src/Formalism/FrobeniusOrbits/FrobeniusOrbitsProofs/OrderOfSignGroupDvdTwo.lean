import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow

open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Misc

theorem isSquare_of_hensel (p : ℕ) [Fact p.Prime] (c a : ℤ)
    (h : ‖((a ^ 2 + c : ℤ) : ℤ_[p])‖ < ‖((2 * a : ℤ) : ℤ_[p])‖ ^ 2) :
    IsSquare (-(c : ℤ_[p])) := by
  have h' : ‖Polynomial.aeval (a : ℤ_[p]) (Polynomial.X ^ 2 + Polynomial.C (c : ℤ_[p]))‖ <
      ‖Polynomial.aeval (a : ℤ_[p])
        (Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.C (c : ℤ_[p])))‖ ^ 2 := by
    push_cast at h
    simp [Polynomial.derivative_X_pow, mul_comm] at h ⊢
    convert h using 4
    norm_num
  obtain ⟨z, hz, -⟩ := hensels_lemma h'
  refine ⟨z, ?_⟩
  simp at hz
  linear_combination -hz

end Misc

open Misc Galois

end Formalism.FrobeniusOrbits
