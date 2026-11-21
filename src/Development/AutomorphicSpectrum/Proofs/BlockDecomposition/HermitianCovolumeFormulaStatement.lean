import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCovolumeFormula
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_covolume_formula : PositivityTheory.SiegelWeilFormula.KWhit.MeasP.HermCovol := by
  exact @GlobalTheory.CompanionTheory.SW.HermCov.hermCovol
