import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmallPairPairingAllGluedPlacesProof
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallPairPairingAllGluedPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.SmallAll D := by
  exact @GlobalTheory.FinPl.SmallAllPf.main
