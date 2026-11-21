import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHeisenbergRadicalCoordinates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_heisenberg_radical_coordinates : Heis := by
  exact @GlobalTheory.InertZeta.HeisCoord.Heisenberg₂
