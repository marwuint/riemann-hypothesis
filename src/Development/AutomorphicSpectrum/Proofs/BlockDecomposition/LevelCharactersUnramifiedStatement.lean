import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelCharactersUnramified
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_characters_unramified : PositivityTheory.SiegelWeilFormula.Gunr.LevChars := by
  exact @GlobalTheory.CompanionTheory.GunrLevChars.levChars
