import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitNormVectors_one_orbit_selfDualLattice_split : ∀ D : D7, GlobalTheory.FinPl.OrbitSplit D := by
  exact @GlobalTheory.FinPl.SplitOrbit.orbitSplit
