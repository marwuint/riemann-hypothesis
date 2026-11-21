import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionary
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_dictionary : PositivityTheory.RgEis.Dict := by
  exact @GlobalTheory.CompanionTheory.EisDict.dict
