import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepIntegrandBesselPeriodInvariant_proof : ∀ D : D7, GlobalTheory.FinPl.HandInv D := by
  exact @GlobalTheory.FinPl.HandInvPf.handInv
