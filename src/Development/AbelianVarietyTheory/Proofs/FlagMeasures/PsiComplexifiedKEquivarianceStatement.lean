import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_complexifiedK_equivariance : PsEquiv := by
  exact @GlobalTheory.Dec.Equivar.psEquiv
