import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitary
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_finitary : ∀ (q : ℕ) (i : ℤ), Finitary (tw q i) := GlobalTheory.EtC.tw_finitary
