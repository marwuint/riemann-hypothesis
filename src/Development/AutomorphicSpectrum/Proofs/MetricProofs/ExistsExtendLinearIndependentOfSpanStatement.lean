import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsExtendLinearIndependentOfSpan
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extend_linearIndependent_of_span : ∀ (g m r : ℕ) (w : Fin r → Fin g → ℂ) (b : Fin m → Fin g → ℂ), LinearIndependent ℂ w → LinearIndependent ℂ b → (∀ a, w a ∈ Submodule.span ℂ (Set.range b)) → ∃ (k : ℕ) (J : Fin k → Fin m), r + k = m ∧ LinearIndependent ℂ (Fin.append w (fun j => b (J j))) := by
  exact @GlobalTheory.CompanionTheory.Ar.Exchange.exists_completion_by_members
