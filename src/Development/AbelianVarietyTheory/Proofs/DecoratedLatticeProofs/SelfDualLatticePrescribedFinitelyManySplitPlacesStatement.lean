import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticePrescribedFinitelyManySplitPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces : ∀ D : D7, GlobalTheory.FinPl.LatAll D := by
  exact @GlobalTheory.LatPresc.latAll
