import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClosedEmbeddingDiagOneGeneralLinearEmbedding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedEmbedding_diagOneGeneralLinearEmbedding : ∀ (F : Type) [NontriviallyNormedField F] (r : ℕ), Topology.IsClosedEmbedding (GlobalTheory.JR.Step.emb r F) := by
  exact @GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb
