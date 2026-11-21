import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionLaw
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_law : PositivityTheory.RgEis.ExtLaw := by
  exact @GlobalTheory.CompanionTheory.RgEisExt.extLaw
