import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_row_exists : GlobalTheory.CompanionTheory.KerFc.FactorRapid → GlobalTheory.CompanionTheory.KerFc.EvAdj → GlobalTheory.CompanionTheory.KerFc.RowExists := by
  exact @GlobalTheory.CompanionTheory.KerFc.rowExists_of_factor
