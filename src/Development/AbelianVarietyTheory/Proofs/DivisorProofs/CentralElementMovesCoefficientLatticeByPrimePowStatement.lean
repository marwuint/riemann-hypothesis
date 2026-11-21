import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementMovesCoefficientLatticeByPrimePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_element_moves_coefficient_lattice_by_prime_pow : CentLat := by
  exact @GlobalTheory.CentralLattice.centLat
