import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLineGenOn
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfD
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumPf
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SectionInputData
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SchurLatticeConjugates
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Duality
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameLinearAlgebraFirst
import Formalism.MeanHeightDescent.MuMaxMinkowski
import Formalism.MeanHeightDescent.BadRowsNumeric
import Formalism.MeanHeightDescent.CombinedAverageDegreeBound
import Formalism.QuotientMetricDivisors.StatementK
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
import Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin
import Formalism.MeanHeightDescent.AverageDegreeBounds.MuMaxMinkowski
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.HodgeTateCharacterSystems
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Formalism.CorankShare.CorankShareProofs.LayerCakeFormula
import Formalism.MeanHeightDescent.AverageDegreeBounds.SumComponents
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsLiftAddOfIsReducedEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalRingCardinality.DataCoeff
import Formalism.LocalRingCardinality.DataArith
import Formalism.LocalRingCardinality.DataKernels
import Formalism.LocalRingCardinality.DataRows
import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
import Formalism.SharpRestriction.GrowthBounds.DataG
import Formalism.LocalRingCardinality.DataCD
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RingHomFlatCodescendsAlongFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinitePresentationOfInjective
import ReciprocityTheory.SemistableReduction.SJCore
import ReciprocityTheory.SemistableReduction.SjHolds
import ReciprocityTheory.SemistableReduction.HeightLowerBound
import ReciprocityTheory.SemistableReduction.IntCores
import ReciprocityTheory.SemistableReduction.TorusMean
import ReciprocityTheory.SemistableReduction.TorusLex
import ReciprocityTheory.SemistableReduction.GramOfLinearOrder
import Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic
import Formalism.FrobeniusOrbits.HostDiffSupport
import Formalism.FrobeniusOrbits.HostThickExists
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.AlgChart
import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GroupLikeIntegralOfFiniteFree
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsHomDivMulRefine
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.AwayToSectionFromZero
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IrreducibleDetOfIsRelPrime
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PushComparisonBijectiveOfIsClosedEmbedding
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
import ReciprocityTheory.SemistableReduction.SphereTorusC
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.DualLattices.ColengthSqMulLeProd
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Theta1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.HasGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoToInterAppPushforwardInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankLin
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpecHomCompCoaction
import Formalism.LocalRingCardinality.DataLevel
import Formalism.FormalDegreeBessel.StatementG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoveringRadiusStatement
import ReciprocityTheory.DualLattices.InvolutionPermApplyZero
import ReciprocityTheory.DualLattices.BasechangeProjectorIdempotentAction
import ReciprocityTheory.DualLattices.KilledGen
import ReciprocityTheory.DualLattices.IdemGen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.TameInertiaTowers.CentralOrderTwo.OrderOfThreeUnitsTwoPow
import Formalism.TameInertiaTowers.CentralOrderTwo.MemDecompositionSubgroupIff
import Formalism.TameInertiaTowers.CentralOrderTwo.NegOneNeOneUnitsZmodFour
import Formalism.TameInertiaTowers.CentralOrderTwo.Groups
import Formalism.TameInertiaTowers.CentralOrderTwo.NormalOrderTwoCentral
import Formalism.TameInertiaTowers.CentralOrderTwo.Galois
import Formalism.TameInertiaTowers.CentralOrderTwo.ConjEqInvOfPowEqOne
import ReciprocityTheory.DualLattices.EigenQuotientSmithStatement
import ReciprocityTheory.DualLattices.SumValCoord
import ReciprocityTheory.DualLattices.MemAugIdeal
import ReciprocityTheory.DualLattices.StdJForm4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import Formalism.GaussIdealIdentity.GaussIdealPrimality.GaussLocalizationLengthHolds
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinTypeQE
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FromSpecResidueFieldAppTopIso
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAppTopEqOfEffectiveEpi
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasAlgebraicChartsOfIsStandardSmooth
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Formalism.FormalDegreeBessel.StatementBF
import Formalism.FormalDegreeBessel.StatementWR
import ReciprocityTheory.DualLattices.ColengthCotangentBoundStatementOfClaim
import ReciprocityTheory.DualLattices.PrimeHopfOrderOfAddEquiv
import ReciprocityTheory.DualLattices.ImportsBis
import ReciprocityTheory.DualLattices.SqIdeal
import ReciprocityTheory.DualLattices.MapTensorSpan
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RangeRestrictCompSubtypeOfOrthogonalOfNe
import ReciprocityTheory.DualLattices.SubgroupQuotientStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitAlgebraMapEqOfValuationEqOne
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolySeq
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SumOfSquaresIdentityHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasKHW
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HWDiag
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge

namespace Bl.KappaIntegralBound

private lemma kappaIntBound {K : Type} [Field K] [NumberField K] (p : Nat.Primes)
    (κ : K →+* PadicComplex p.val) (r : NumberField.RingOfIntegers K) :
    ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ ≤ 1 := by
  let w : Valuation K NNReal := (NormedField.valuation (K := PadicComplex p.val)).comap κ
  have hi : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K r) :=
    NumberField.RingOfIntegers.isIntegral_coe r
  have hO : IsIntegral w.integer (algebraMap (NumberField.RingOfIntegers K) K r) := hi.tower_top
  have hm : algebraMap (NumberField.RingOfIntegers K) K r ∈ w.integer :=
    (Valuation.integer.integers w).mem_of_integral hO
  rw [Valuation.mem_integer_iff] at hm
  have h2 : ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖₊ ≤ 1 := hm
  exact_mod_cast h2

theorem goal1 :
  ∀ {K : Type} [inst : Field.{0} K] [inst_1 : NumberField.{0} K] (p : Nat.Primes)
  (κ : RingHom.{0, 0} K (PadicComplex (Subtype.val.{1} p))),
  Exists.{1} fun (la : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K)) ↦
    ∀ (a : K),
      Iff (LE.le.{0} (DFunLike.coe.{1, 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{0, 0} K la) a) 1)
        (LE.le.{0} (Norm.norm.{0} (DFunLike.coe.{1, 1, 1} κ a)) 1) := by
  intro K _ _ p κ
  have hle : ∀ r : NumberField.RingOfIntegers K,
      ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ ≤ 1 := fun r => kappaIntBound p κ r
  let I : Ideal (NumberField.RingOfIntegers K) :=
    { carrier := {r | ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
        calc ‖κ (algebraMap _ K c)‖ * ‖κ (algebraMap _ K a)‖
            ≤ 1 * ‖κ (algebraMap _ K a)‖ := mul_le_mul_of_nonneg_right (hle c) (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact ha }
  have hmem : ∀ r, r ∈ I ↔ ‖κ (algebraMap (NumberField.RingOfIntegers K) K r)‖ < 1 :=
    fun r => Iff.rfl
  have hIprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmem]
      simp
    · intro a b hab
      rw [hmem, map_mul, map_mul, norm_mul] at hab
      rw [hmem, hmem]
      by_contra h
      rw [not_or, not_lt, not_lt] at h
      have ha := le_antisymm (hle a) h.1
      have hb := le_antisymm (hle b) h.2
      rw [ha, hb, mul_one] at hab
      exact lt_irrefl _ hab
  have hpI : ((p.val : ℕ) : NumberField.RingOfIntegers K) ∈ I := by
    rw [hmem, map_natCast, map_natCast]
    rw [show ((p.val : ℕ) : PadicComplex p.val) = (((p.val : ℕ) : Padic p.val) : PadicComplex p.val)
      from by simp]
    rw [PadicComplex.norm_extends', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
  have hne : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpI
    have h2 := congrArg (algebraMap (NumberField.RingOfIntegers K) K) hpI
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h2
    exact p.2.ne_zero h2
  let la : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) := ⟨I, hIprime, hne⟩
  refine ⟨la, fun a => ?_⟩
  obtain ⟨n, d, h | h⟩ := la.exists_primeCompl_mul_eq_or_mul_eq a
  · have hd : (d : NumberField.RingOfIntegers K) ∉ la.asIdeal := d.2
    have hvd := (la.valuation_eq_one_iff_notMem (K := K)).mpr hd
    have hNd : ‖κ (algebraMap _ K (d : NumberField.RingOfIntegers K))‖ = 1 :=
      le_antisymm (hle _) (not_lt.mp hd)
    have hv : la.valuation K a = la.valuation K (algebraMap _ K n) := by
      rw [← h, map_mul, hvd, mul_one]
    have hN : ‖κ a‖ = ‖κ (algebraMap _ K n)‖ := by
      rw [← h, map_mul, norm_mul, hNd, mul_one]
    rw [hv, hN]
    exact iff_of_true (la.valuation_le_one (K := K) n) (hle n)
  · have hd : (d : NumberField.RingOfIntegers K) ∉ la.asIdeal := d.2
    have hvd := (la.valuation_eq_one_iff_notMem (K := K)).mpr hd
    have hNd : ‖κ (algebraMap _ K (d : NumberField.RingOfIntegers K))‖ = 1 :=
      le_antisymm (hle _) (not_lt.mp hd)
    have hv2 : la.valuation K a * la.valuation K (algebraMap _ K n) = 1 := by
      rw [← map_mul, h, hvd]
    have hN2 : ‖κ a‖ * ‖κ (algebraMap _ K n)‖ = 1 := by
      rw [← norm_mul, ← map_mul, h, hNd]
    have key1 : la.valuation K a ≤ 1 ↔ n ∉ la.asIdeal := by
      constructor
      · intro ha
        have h1 : 1 ≤ la.valuation K (algebraMap _ K n) := hv2 ▸ mul_le_of_le_one_left' ha
        exact (la.valuation_eq_one_iff_notMem (K := K)).mp
          (le_antisymm (la.valuation_le_one (K := K) n) h1)
      · intro hn
        have h1 := (la.valuation_eq_one_iff_notMem (K := K)).mpr hn
        rw [h1, mul_one] at hv2
        exact hv2.le
    have key2 : ‖κ a‖ ≤ 1 ↔ n ∉ la.asIdeal := by
      constructor
      · intro ha hn
        have h1 : 1 ≤ ‖κ (algebraMap _ K n)‖ := by
          rw [← hN2]; exact mul_le_of_le_one_left (norm_nonneg _) ha
        exact absurd ((hmem n).mp hn) (not_lt.mpr h1)
      · intro hn
        have h1 : ‖κ (algebraMap _ K n)‖ = 1 := le_antisymm (hle n) (not_lt.mp hn)
        rw [h1, mul_one] at hN2
        exact hN2.le
    rw [key1, key2]

end Bl.KappaIntegralBound
