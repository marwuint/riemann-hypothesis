import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfInducedOfInduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsDualBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverNormsPullbackPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsLiftPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCovers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetResidueLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationConstantOfPowerEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobalFunctionsDvrOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfRegularAtCodimOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedSpecialFibreGlobalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCobOneOfIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosureOfValuationRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianCubeFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationTorsionTower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupSche
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiInjectiveCriterion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwich
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTorusLeLieSpan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulEqZeroOfToCompletion
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentGeometricallyIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionStatementHolds
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetCondTensorDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CorrespondenceDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothBaseAndNormalCoordinateRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CocycleTrivialOnProjectiveCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentCombinationEigenAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellsGlueLocallyClosedPluckerProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageIUnionOpensEqRangeFlagCells
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfPluckerProportional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAdaptedOfIntStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedNextStepType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedSubstepClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClosureOfEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLocalRingPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineModelTrueOfFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringDedekindOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionMonoBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateDifferenceSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateGluedSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropertyOfCodimOneLocalUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSectionCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthArchSectionEqSmulOfSameWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightRuleReadsNonvanishingDetSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrOverHeightOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointModelOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistenceOfComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDvrExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingUnitScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluckerMinorsProportional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BLieLieComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointOnModelPullbackCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnectedOfProper
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPointThrough
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsMaximalTensorProductOfIsLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteType
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegralCoeffZeroMulOfAevalInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointFactorsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLawsOfSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToOverSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColengthDvdOfNeZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPrimitiveIdempotentMapEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagPointTangentDualNumber
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordinateSectionsOfWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSmoothOnPreimageCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedComplexPointOfEigenFrameOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointExtensionSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointTorsionSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFrameCoverTangentCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramePrimeTangentCompat

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm

namespace GlobalTheory.NefHodgeTateAt

section Curves

variable {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem topSelf_of_cls_eq_add (hp : IsProjOver p) {N A B : LB X} (hN : N.IsLB) (hA : A.IsLB) (hB : B.IsLB)
    (h : cls N hN = cls A hA + cls B hB) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ] [Finite κ]
    [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ (N.pull i) 1 = topSelfIntersection κ (A.pull i) 1 + topSelfIntersection κ (B.pull i) 1 := by
  obtain ⟨hpr, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have e2 (L : LB X) : topSelfIntersection κ (L.pull i) 1 = interNum κ (structureModule Z) ![L.pull i] := by
    rw [topSelf_def]
    congr 1
    funext j
    fin_cases j
    rfl
  rw [e2, e2, e2]
  refine interNum_one_of_cls_eq_add (hH.pull_of_isClosedImmersion i) hd (LB.isLB_pull hN i) (LB.isLB_pull hA i)
    (LB.isLB_pull hB i) ?_
  rw [cls_pull hN, cls_pull hA, cls_pull hB, h, map_add]

theorem topSelf_pow (hp : IsProjOver p) (L : HermLB p) (m : ℕ) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i]
    (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1 := by
  have c (n : ℕ) : cls (L.pow n).B (L.pow n).isLB = n • cls L.B L.isLB := cls_lbPow L.isLB n _
  induction m with
  | zero =>
    have := topSelf_of_cls_eq_add hp (L.pow 0).isLB (L.pow 0).isLB (L.pow 0).isLB (by rw [c]; simp) Z i κ hd
    simp only [Nat.cast_zero, zero_mul]
    linarith
  | succ n ih =>
    rw [topSelf_of_cls_eq_add hp (L.pow (n + 1)).isLB (L.pow n).isLB L.isLB (by rw [c, c, succ_nsmul]) Z i κ hd, ih]
    push_cast
    ring

end Curves

open Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4
open scoped ENNReal Classical

end GlobalTheory.NefHodgeTateAt
