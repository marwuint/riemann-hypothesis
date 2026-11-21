import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealCompression
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MuQMemHarmSet
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_compression : PositivityTheory.RgBcC.RealD.Compress := by
  exact @GlobalTheory.CompanionTheory.LevelCompress.exists_compress
