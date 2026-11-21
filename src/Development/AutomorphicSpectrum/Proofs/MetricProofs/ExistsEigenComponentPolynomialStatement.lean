import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial
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
theorem _root_.GlobalTheory.T.exists_eigenComponent_polynomial : ∀ (E : Type) [Field E] [NumberField E] (s₀ : 𝓞 E →+* ℂ), ∃ c : 𝓞 E →₀ ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V), (∀ x, eigComp ρ s₀ x = ∑ a ∈ c.support, c a • ρ a x) ∧ (∀ x, eigComp ρ s₀ x ∈ eigSp ρ s₀) ∧ ∀ x ∈ eigSp ρ s₀, eigComp ρ s₀ x = x := by
  exact @GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef.eigComp_eq_combination
