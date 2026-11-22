import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.DetValuationLeOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsMonicIrreducibleCardGt
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Formalism.MonomialMeanResidues.FilteredDegree
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GoodOver
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YReadArch
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformLawsRootModelBound
import Development.WeilBound.CoreStatements.RationalSupMetrics.MhbNeg
import Development.WeilBound.CoreStatements.RationalSupMetrics.AevalCoordProd
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginRootWeightBound
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspSquareIntegrableIffUnfolded
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagQuotientIntegralEqUniversalConstMul
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.OS

section Vals

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] {𝕜 : Type} [Field 𝕜]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → 𝕜}

theorem hasVal_add {a : K → ℤ} {s s' : Ω} {w w' : 𝕜} (h : Small.HasVal y a s z w)
    (h' : Small.HasVal y a s' z w') : Small.HasVal y a (s + s') z (w + w') := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  obtain ⟨dg', dh', g', f', hg', hf', hd', e', hz0', ez'⟩ := h'
  have hdeg : dg' + dh = dg + dh' := funext fun k => by
    have h1 := hd k
    have h2 := hd' k
    simp only [Pi.add_apply]
    omega
  refine ⟨dg + dh', dh + dh', g * f' + g' * f, f * f',
    FinRd.ValSub.mh_add (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hg hf') ?_,
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hf hf', fun k => ?_, ?_, ?_, ?_⟩
  · rw [← hdeg]
    exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hg' hf
  · have h1 := hd k
    simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_add, map_mul, e, e']
    ring
  · rw [map_mul]
    exact mul_ne_zero hz0 hz0'
  · simp only [map_add, map_mul, ez, ez']
    ring

theorem hasVal_zsmul {a : K → ℤ} {s : Ω} {w : 𝕜} (n : ℤ) (h : Small.HasVal y a s z w) :
    Small.HasVal y a (n • s) z (n • w) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  refine ⟨dg, dh, MvPolynomial.C n * g, f, ?_, hf, hd, ?_, hz0, ?_⟩
  · intro m hm k
    rw [MvPolynomial.C_mul'] at hm
    exact hg m (MvPolynomial.support_smul hm) k
  · rw [map_mul, e, MvPolynomial.aeval_C, ← mul_assoc]
    simp [zsmul_eq_mul]
  · rw [map_mul, ez, MvPolynomial.aeval_C, ← mul_assoc]
    simp [zsmul_eq_mul]

theorem hasVal_zero_of {a : K → ℤ} {s : Ω} {w : 𝕜} (h : Small.HasVal y a s z w) :
    Small.HasVal y a (0 : Ω) z (0 : 𝕜) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  exact ⟨dg, dh, 0, f, FinRd.ValSub.mh_zero dg, hf, hd, by simp, hz0, by simp⟩

end Vals

end GlobalTheory.CompanionTheory.Ar.Rec.OS

namespace GlobalTheory.CompanionTheory.Ar.Rec

end GlobalTheory.CompanionTheory.Ar.Rec
