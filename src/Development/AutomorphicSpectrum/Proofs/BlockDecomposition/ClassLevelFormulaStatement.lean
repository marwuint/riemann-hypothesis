import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassLevelFormula
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_level_formula : PositivityTheory.SiegelWeilFormula.Gunr.ClassLev := by
  exact @GlobalTheory.CompanionTheory.GunrClassLev.classLev
