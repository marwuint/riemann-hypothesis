import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.Poulsen
import Formalism.PeriodIntegrals.DSInfCharCap
import Formalism.PeriodIntegrals.LowCyc
import Formalism.PeriodIntegrals.UpqRep
import Formalism.HermitianCurvature.StatementTBB
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreserving
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaInfEqIntegralOfIntegrableCoefficient
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqConstMulArchPairing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayThresholdsOfSpectralGapCondition
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSqStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AemeasurableBesselNormIntegrandBigCell
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqIntegralInnerWeightLeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DstInvContinuousOn
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormSqHermTranslatesOrthonormal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilFormulaIntegrableComplex
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGrowthStabilizerUnipotent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameWConjMatrixUnitsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLieUnitaryElementSimpleRoot
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProductMomentBoundDensityMassOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyProductBoundConstantLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionLocalityInvariantFactorFiniteSumStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FactorisationOfConjHomogeneousAndHomogeneous
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRegularRepBesselBigCellVectorEqBessel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BaseRepCapelliEigenDual
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionSmulStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellExpansionOfBesselFunctionZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CkOnInCCCongrOnGroup
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatrixCoefficientSmoothDerivatives
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalProperties
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSides
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsCoordLeOfLOneNormLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrepDiscreteSeriesSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriTensorDecomposition
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepExteriorPowerStandardRep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FixesWedgeAndForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.HpkRowEsI
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermCmpWedgeEqDet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsometricBesselCompare
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevZeroOfKHighest
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLowestKFiniteVectorDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionExpandMatrixUnitsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumDeterminantEigenvalue
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexifiedDerivedActionLieHomGramAdjointStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModule
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlProjectionLevelSumSqLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProjectorEntryValueUnderLinearFunctional
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExpMemUnipotentAndHasDerivAtCharacter
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAtStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyCompatible
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenvalueOnDualTensorSummand
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LoweringBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevEAddTwo
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelSumNormSqLe
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorAbsoluteOfExplicit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopNum

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.WaveGrid.Ball

section sup

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

structure Sup0 (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (q0 : ℕ)
    (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq)
    (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ)
    (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) : Prop where
  fam : IsFam lam q0 R
  left : haveI := FiniteDimensional.complete ℂ Wp
    SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg
  right : haveI := FiniteDimensional.complete ℂ Wq
    SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg
  coef : ∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) →
    IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν
  zero : ∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0
  tau_zero : ∀ ν I, J ν = 0 ∨ J (ν + eZ I) = 0 → tau ν I = 0
  tau_eq : ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 →
    ∃ io pr ep, TensH (cmp (P.r + 1)) (cmp (P.r + 1) (Formalism.QuantumDeterminants.Hpk P.k P.r)) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep ∧
      ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), J ν ≠ 0 → J (ν + eZ I.1) ≠ 0 → ∃ κ κ' : ℂ,
        (∀ v ∈ (R ν).sm, l (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) v c)) = κ • l ν v) ∧
        (∀ v ∈ (R ν).sm, l' (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) v c)) = κ' • l' ν v) ∧
        tau ν I.1 = (ep I : ℂ) * κ' * star κ * s ν / s (ν + eZ I.1)

end sup

end CompanionTheory.WaveGrid.Ball
