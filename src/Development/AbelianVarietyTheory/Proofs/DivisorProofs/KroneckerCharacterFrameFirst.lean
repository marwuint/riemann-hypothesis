import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLowerBoundPrincipalLevel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumPositive
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWeightSpreadLeExponentNormAdd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SupNormDefiniteOnCuspFormsGoodEmbedding

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LamPet

open scoped ENNReal

theorem log_le_of_sq_le {A B : ℝ≥0∞} {K L : ℝ} (hL : 0 < L) (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hA0 : A ≠ 0)
    (h : A ^ 2 ≤ ENNReal.ofReal K * B ^ 2) :
    0 < L * B.toReal ∧ Real.log (L * A.toReal) ≤ 1 / 2 * Real.log K + Real.log (L * B.toReal) := by
  have hApos : 0 < A.toReal := ENNReal.toReal_pos hA0 hA
  have hK0 : 0 ≤ K := by
    by_contra hK
    rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hK)), zero_mul] at h
    exact hA0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h zero_le))
  have h2 : A.toReal ^ 2 ≤ K * B.toReal ^ 2 := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hB)) h
    rwa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0, ENNReal.toReal_pow] at this
  have hB0 : 0 < B.toReal := by
    rcases (ENNReal.toReal_nonneg (a := B)).lt_or_eq with hb | hb
    · exact hb
    · rw [← hb] at h2; nlinarith
  have hKpos : 0 < K := by
    by_contra hK
    have : K * B.toReal ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hK) (sq_nonneg _)
    nlinarith
  refine ⟨mul_pos hL hB0, ?_⟩
  rw [Real.log_mul hL.ne' hApos.ne', Real.log_mul hL.ne' hB0.ne']
  have h3 : Real.log (A.toReal ^ 2) ≤ Real.log (K * B.toReal ^ 2) := Real.log_le_log (by positivity) h2
  rw [Real.log_pow, Real.log_mul hKpos.ne' (by positivity), Real.log_pow] at h3
  push_cast at h3
  linarith

end GlobalTheory.LamPet
