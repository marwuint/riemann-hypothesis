import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kType_extends_holomorphic_complexifiedK : TauExists := by
  exact @GlobalTheory.Dec.TauExt.tauExists
