import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsKerProj
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
theorem _root_.GlobalTheory.T.exists_isKerProj' : ∀ (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ), ∃ Pr : Matrix (Fin g) (Fin g) ℝ, IsKerProj S Pr := by
  exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.exists_isKerProj
