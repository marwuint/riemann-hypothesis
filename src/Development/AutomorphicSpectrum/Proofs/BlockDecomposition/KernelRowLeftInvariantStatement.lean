import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowLeftInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_row_left_invariant : GlobalTheory.CompanionTheory.KerFc.LtSob → GlobalTheory.CompanionTheory.KerFc.LtComm → GlobalTheory.CompanionTheory.KerFc.RowLeft := by
  exact @GlobalTheory.CompanionTheory.KerFc.rowLeft
