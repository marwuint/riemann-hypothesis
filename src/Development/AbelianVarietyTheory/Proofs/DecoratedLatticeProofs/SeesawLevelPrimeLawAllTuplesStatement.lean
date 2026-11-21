import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLevelPrimeLawAllTuples
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_levelPrime_law_all_tuples : ∀ D : D7, GlobalTheory.SeeSaw.TOfShape D := by
  exact @GlobalTheory.LevPrimeAll.lawLevelPrime_all
