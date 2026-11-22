import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyPowMulEqOne
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_poly_pow_mul_eq_one' : ∀ (n l : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), 0 < l → IsUnit B → ∃ p : ℂ[X], (aeval B p) ^ l * B = 1 := GlobalTheory.exists_poly_pow_mul_eq_one
