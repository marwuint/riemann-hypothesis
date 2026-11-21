import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ChowFormHeightOfArch
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IntegralOfLintegral
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzHeightRVolUpModelMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveClosureIsProjOver
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfKnownTheorem
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfA
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfB
import CompanionTheory.AutomorphicTheory.KrullDimension.TopologicalKrullDimModel
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzHeightRVolUpModelModel
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ValFUnitNeZero
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MulEqOneOfComb
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ValFFromSpecStalk
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerSectionStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IntStable
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ValNeBot
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeilHeightInequality

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
theorem ChowFormHeightComparison₂.chow_form_height_bound (h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : PositivityTheory.UnitarySelfGeneration.ChowFormHeight :=
  ChowFormHeightComparison₂.CF.chowFormHeight_of_arch (ChowFormHeightComparison₂.CF.stArch ChowFormHeightComparison₂.CF.stPts (ChowFormHeightComparison₂.CF.stCharts ChowFormHeightComparison₂.CF.stPts)) _root_.GlobalTheory.CompanionTheory.Ar.Short.mahlerSection h.p4.arExists
theorem ChowFormHeightComparison₂.chow_form_height_comparison : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (t a : ℝ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a → a ≤ (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t)) :=
  fun h => _root_.PositivityTheory.UnitarySelfGeneration.weil_height_inequality (_root_.ChowFormHeightComparison₂.chow_form_height_bound h) h
end
