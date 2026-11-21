import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCountTail
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_count_tail : PositivityTheory.Rg.BcB.F.Tail.PExp.CosetCount := by
  exact @GlobalTheory.CompanionTheory.IwahoriCount.cosetCount
