import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeDimAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureNeTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLowestKTypeWeylDimensionLeOfSizeBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealUnitaryCovolumeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianGramDiagonalSignatureUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HatKMConjImp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryWithDeterminant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvertibleUnitaryAdelicMatrixOfRationalUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaTermTsumLeTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupMeasureDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRepresentativesInjectiveDoubleCoset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.OneMeasureRatio

theorem log_r_add_three_le (D : D7) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) :
    Real.log ((D.R.r : ℝ) + 3) ≤ L := by
  have hr : 6 ≤ D.R.r := by
    unfold Ranks.r; have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hf : 2 ≤ D.R.f := by
    unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hn : D.R.r ≤ D.R.nV := by unfold Ranks.nV; omega
  have hr' : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hf' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hn' : (D.R.r : ℝ) ≤ D.R.nV := by exact_mod_cast hn
  have h1 := hL.1
  rw [← Real.log_exp L]
  refine Real.log_le_log (by positivity) ?_
  have a1 : 2 * (D.R.r : ℝ) ≤ (D.R.f : ℝ) * D.R.r := mul_le_mul_of_nonneg_right hf' (by positivity)
  have a2 : 2 * (D.R.r : ℝ) * D.R.r ≤ (D.R.f : ℝ) * D.R.r * D.R.nV :=
    mul_le_mul a1 hn' (by positivity) (by positivity)
  have : (D.R.r : ℝ) + 3 ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := by nlinarith
  linarith

end GlobalTheory.OneMeasureRatio
