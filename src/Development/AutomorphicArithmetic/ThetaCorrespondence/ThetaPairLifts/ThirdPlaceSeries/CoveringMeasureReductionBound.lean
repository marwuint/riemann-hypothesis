import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAtOfOneMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeDimAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureNeTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactRatioOfFundamentalDomain
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetIsTA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaTermTsumLeTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMeasureRatioLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRatioUpperBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRatioLowerBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.NormalizedCovolumeEqOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatAtUpperStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CovolumeLowerBoundOfCover
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExactAtOfRowsStatement

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
namespace GlobalTheory.CovTop.MeasRd
theorem covering_measure_reduction_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.MeasureCondition := by
  intro h
  have h2 := _root_.GlobalTheory.T.normalized_covolume_eq_one h
  refine Closed.imp (Closed.and (_root_.GlobalTheory.T.exists_log_ratAt_le_mul_unitE h2) (_root_.GlobalTheory.T.exists_neg_unitE_le_log_ratAt h)) ?_
  intro _ Fm _ _ hh
  obtain ⟨⟨K1, hK1, a, ha⟩, ⟨K2, hK2, b, hb⟩⟩ := hh
  refine ⟨(K1 + K2) / 2, by positivity, max a b, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨hr, hu⟩ := ha x hx ((le_max_left _ _).trans hle) ι p hp i
  have hl := hb x hx ((le_max_right _ _).trans hle) ι p hp i
  exact measAt_of p i (_root_.GlobalTheory.T.exactAt_of_oneMeasure p hp.1 (h2 _) i) hr hK1 hK2 hu hl
end GlobalTheory.CovTop.MeasRd
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_meas_of_prints : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.MeasureCondition := by
  first | exact @_root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction_alt | exact _root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction_alt | (intros; apply _root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction_alt <;> assumption)
end
end
