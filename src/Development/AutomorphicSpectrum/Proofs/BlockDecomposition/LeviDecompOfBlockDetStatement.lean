import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDecompOfBlockDet
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_decomp_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.LeviS := by
  exact @GlobalTheory.CompanionTheory.RgEisLevi.leviS
