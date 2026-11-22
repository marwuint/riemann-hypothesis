import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenBoundCombinePadicPrimeToP

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.den_bound_combine_padic_primeToP : ∀ (p D K k : ℕ), p.Prime → ∀ q : ℚ, (∃ m : ℕ, m.Coprime p ∧ ∃ a : ℤ, ((p ^ K * m : ℕ) : ℚ) * q = a) → (∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * q = a) → ∃ a : ℤ, ((D * p ^ K : ℕ) : ℚ) * q = a := GlobalTheory.den_comb
