import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinate
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], ∀ (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (i : σ), evA k x hx (X i) = x i := by
  exact @GlobalTheory.Katz.evA_X
