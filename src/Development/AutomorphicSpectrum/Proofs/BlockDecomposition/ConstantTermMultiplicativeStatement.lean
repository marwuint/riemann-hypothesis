import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicative
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_multiplicative : CtMul := by
  exact @GlobalTheory.CompanionTheory.CtMulSplit.ctMul
