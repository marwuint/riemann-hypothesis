import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolic
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_multiplier_mirabolic : PositivityTheory.RgEis.Dict → PositivityTheory.RgEis.CMGood → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.MirGen → PositivityTheory.RgEis.CMMir := by
  exact @GlobalTheory.CompanionTheory.CMMirror.cmMir
