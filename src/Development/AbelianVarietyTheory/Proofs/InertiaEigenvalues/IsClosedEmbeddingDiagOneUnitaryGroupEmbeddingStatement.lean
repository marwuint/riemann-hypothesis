import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneUnitaryGroupEmbedding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedEmbedding_diagOneUnitaryGroupEmbedding : ∀ (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E], Topology.IsClosedEmbedding (GlobalTheory.JR.Step.uEmb r E) := by
  exact @GlobalTheory.JR.Step.isClosedEmbedding_uEmb
