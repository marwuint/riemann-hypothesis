import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContractionOfVacuumCombinationsProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contractionOfVacuumCombinations_proof : ∀ D : D7, GlobalTheory.FinPl.ContrOp D := by
  exact @GlobalTheory.FinPl.ContrOpProof.contrOp
