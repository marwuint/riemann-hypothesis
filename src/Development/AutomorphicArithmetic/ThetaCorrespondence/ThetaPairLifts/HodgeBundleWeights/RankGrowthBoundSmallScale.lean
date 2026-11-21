import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthBoundSmallScale
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMultiplicityWeight
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsNonzeroSectionWeightBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentredPointPhiPositiveWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsExtendVanishCompactifiedFlagSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberQuotientBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberUpperWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRulesExistAndCusp
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisedChartScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionDvrFlagLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTruncatedFrameChartResidueCharZerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReflectionSumJetNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAntitoneBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormStalkIntegralFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfThRuleLeNuLocOf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateEqUnitMulNormaliserThetaVa
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointStatementsOnCopiesHold
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlope
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrime
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalk
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralFramePointStalkCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameStalkCompatibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CentredPointPhiPositive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToroidalFlagNonempty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GloballyGeneratedOnOpenOfWeightGapGe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightPrincipalisationBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityPrincipleCompactification
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CompactificationTopChernEqVolume
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwistedFlatBundleRanks
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.JetRankComplexLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.UnramifiedPointsAtDeepLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.HodgeSteps
theorem covering_goodAt_shift (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (Y : Deep T.toCore j) (e : ℕ)
    (o : ℝ) (hY : Y.Good e o) (hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W j) Y.dict) (hl : ∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q)
    (hF : GlobalTheory.FlatLine.FlatExists Y.U (xiR D)) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (s : ℤ) (hn : Even n)
    (h : Y.GoodAt (wtOf _ (uWt (T.Q.Dw j) a n kc + s • hodgeWt (T.Q.Dw j)) 0)) : Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  obtain ⟨m, rfl⟩ := hn
  have h1 := (((_root_.GlobalTheory.FlatRootTwist.flat_root_twist hP.p5 D T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U _ Y.dict hC hY.geo hpq hl hF
    (_root_.GlobalTheory.T.unramified_points_of_deep_cover hP D T j Y e o hL hj hY) (anchor (T.Q.Dw j) a (m + m) kc) m).2 _ 0).2 h).1
  have e1 : uWt (T.Q.Dw j) a (m + m) kc + s • hodgeWt (T.Q.Dw j) +
      GlobalTheory.FlatLine.parWt (T.Q.Dw j) (anchor (T.Q.Dw j) a (m + m) kc) =
      laOf (T.Q.Dw j) a (m + m) + s • hodgeWt (T.Q.Dw j) := by
    rw [add_right_comm, uWt_add_anchor]
  rw [e1, add_comm (0 : ℤ), AllWt.wtOf_add] at h1
  have e2 : exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (m + m)) m + wtOf (T.Q.Dw j) (s • hodgeWt (T.Q.Dw j)) 0) =
      exZ (T.Q.Dw j) (shiftG (T.Q.Dw j) a (m + m) s) := by
    rw [shiftG, FlatTw.exZ_add_eq, FlatTw.exZ_add_eq]
    congr 1
    have := AllWt.exOf_weightOf (Dw := T.Q.Dw j) (fun x => (a x : ℤ)) m
    rw [AllWt.exOf] at this
    rw [laOf, show (m + m) / 2 = m by omega, this, wtZ]
    push_cast
    rw [two_mul]
  have e3 : cuspW Y.d.Xo₂ Y.d.c₂ Y.U
      (wtOf (T.Q.Dw j) (laOf (T.Q.Dw j) a (m + m)) m + wtOf (T.Q.Dw j) (s • hodgeWt (T.Q.Dw j)) 0) =
      cuspW Y.d.Xo₂ Y.d.c₂ Y.U (shiftG (T.Q.Dw j) a (m + m) s) := by
    ext f
    rw [AllWt.mem_cuspW, AllWt.mem_cuspW, e2]
    exact and_congr_right fun _ => forall₂_congr fun σ hσ => by
      rw [AllWt.modelWt_congr (Y.U σ) hσ (hY.unf σ hσ) e2]
  have key : ∀ C C' : Submodule Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂), C = C' →
      ((AllWt.supLat C).FG ∧ Submodule.span Y.d.c₂.F (AllWt.supLat C : Set C) = ⊤) →
      (AllWt.supLat C').FG ∧ Submodule.span Y.d.c₂.F (AllWt.supLat C' : Set C') = ⊤ := by
    rintro C _ rfl h
    exact h
  exact ⟨hasGram_nrm_of_good D _ j Y e o hY _, key _ _ e3 h1.2⟩
end GlobalTheory.CovTop.HodgeSteps
end
end

