import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularRowLatticeTriangularBasis
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockTriangular_row_lattice_triangular_basis : SpanEq := by
  exact @GlobalTheory.InertZeta.RowSpan.spanEq_holds
