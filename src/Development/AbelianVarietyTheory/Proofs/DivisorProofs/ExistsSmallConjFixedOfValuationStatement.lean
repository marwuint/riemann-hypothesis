import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallConjFixedOfValuation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent

open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_conjFixed_of_valuation : ∀ (K : GlobalTheory.UnitLemma.UQ) (k : ℕ), 1 ≤ k → ∃ t : K.O, K.Small t ∧ GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k := by
  exact @GlobalTheory.UnitLemma.exists_small_val
