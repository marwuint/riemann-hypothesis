import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisMemOfIsLocalRingOfVarietyPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace

open GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trBasis_mem_of_isLocalRingOfVarietyPoint : ∀ {K : Type} [Field K] (c : ℂ →+* K) (R : Subring K) (n : ℕ), IsLocModel c R →
    (∃ x : Fin n → K, TrBasis c x) → ∃ xi : Fin n → R, TrBasis c (fun j => (xi j : K)) := by
  exact @GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel
