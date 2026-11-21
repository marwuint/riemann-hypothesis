import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLawOfBlockDet
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_law_of_block_det : PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.ParLaw := by
  exact @GlobalTheory.CompanionTheory.RgEisPar.parLaw
