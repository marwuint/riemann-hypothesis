import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIntPreimageOfOrthogonalKernel
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.IsotropicSubmoduleNonzeroFamily
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeEigenProjections

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_preimage_of_orthogonal_kernel : ∀ (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ), Sᵀ = S → ∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, S *ᵥ v = 0 → u ⬝ᵥ v = 0) → ∃ (N : ℤ) (c : Fin g → ℤ), N ≠ 0 ∧ N • u = S *ᵥ c := by
  exact @GlobalTheory.CompanionTheory.Ar.IntegralKernel.exists_smul_eq_mulVec
