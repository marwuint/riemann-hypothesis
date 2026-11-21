import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFrameWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalOnWeightParameters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelComponentShortBasisBound
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBound
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinomialFlagDimensionDegreeBound
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFinrankCuspFormsLe
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLastAddGaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnectedStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadWeightLineNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFlagUnitWeightBundlesNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivLeSubMulDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelMapBirationalOfCuspFormsGenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModifResidueFieldMapSurjective
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulLeSqrtBergmanMulComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefAndIsBig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRatiosGenerateAtFlagSpaceGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerIsoFlagTangent
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeBotOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedStr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOnOpenCuspIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsExtendVanishCompactifiedFlagSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalIntegralWeightSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemOfMemSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCmPtFrPolyNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolyDivDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.ChartWD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCoverComponentExtendsToRankOneCuspData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFrameReadingNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldFrameValueNeZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortFamilyOfSpanning
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLarge

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.HSShortRun

open GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe {g : ℤ} (hg : 0 ≤ g) {la : AllWt.Weight Dw} (h : GapGe g la) (τ : Psi H) : Antitone (la τ) := by
  intro a i hai
  have h0 : ∀ k, 0 ≤ gap (la τ) k := fun k => by
    by_cases hk : k + 1 < Dw.p + Dw.q
    · exact hg.trans (h τ k hk)
    · rw [gap, dif_neg hk]
  have e := ofGaps_gap (la τ) a i
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := gap (la τ)) (Finset.range_mono (show (a : ℕ) ≤ i from hai))
    fun k _ _ => h0 k
  rw [ofGaps] at e
  linarith

theorem gapGe_wt_of_wtBig {P : WtPar Dw} (h : WtBig P) : ∀ i, GapGe (FlagTan.dimFlag Dw + 1) (P.wt i) := by
  have h₁ : GapGe (FlagTan.dimFlag Dw + 3) P.u₁ := h.gaps.mono (by
    push_cast
    exact le_mul_of_one_le_right (by positivity) (by omega))
  intro i τ k hk
  have a := h₁ τ k hk
  have b := (P.gap_rem τ k).1
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by rw [gap_kap τ hk]; split_ifs <;> omega
  have d : 0 ≤ gap (P.u₁ τ) k := le_trans (by positivity) a
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, gap_add, gap_nsmul]
  nlinarith [mul_nonneg (Int.natCast_nonneg i) d, mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) d]

end Weights

variable {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j}

end GlobalTheory.HSShortRun
