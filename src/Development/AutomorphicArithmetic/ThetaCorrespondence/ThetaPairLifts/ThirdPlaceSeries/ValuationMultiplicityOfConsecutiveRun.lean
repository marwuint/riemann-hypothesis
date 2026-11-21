import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMultiplicityWeight
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
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
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNonzeroSectionWeightBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSectionOrderBoundHilbertSamuel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentredPointPhiPositive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtBigRun

set_option synthInstance.maxHeartbeats 200000

section
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
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ValMultRun
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic GlobalTheory.Vanishing in
set_option maxHeartbeats 1000000 in
theorem valuation_multiplicity_of_consecutive_run_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ValMult Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) (wtOf (dat p i) (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) 0) := by
  intro hP hGD hQ hS hT hL h2 h3 h4
  refine ((((_root_.GlobalTheory.T.exists_nonzero_section_weight_bound_alt_alt hP h2 h3 h4).and (_root_.GlobalTheory.T.exists_section_order_bound_hilbertSamuel_alt hP h2 h3 h4)).and (_root_.GlobalTheory.T.exists_phi_pos_of_centred_off_U0 hP h2 h3 h4)).and _root_.GlobalTheory.HSApp.wtBig_run_alt).imp
    fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨C, hC, x0, hx⟩, ⟨C', hC', x1, hx1⟩⟩, ⟨C'', hC'', x2, hx2⟩⟩, ⟨C₃, hC₃, x3, hx3⟩⟩ := h
  refine ⟨C, hC, max (max x0 x1) (max x2 x3), fun x hx' hle ι p hp i hi Y hY Z => ?_⟩
  simp only [max_le_iff] at hle
  have hB := hx3 x hx' hle.2.2 ι p hp i hi
  have hP' := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨TF⟩ := @_root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt hP' _ _ _ _ _ _ _ Y.d.Xo₂ Y.d.c₂ hB.one_le
  obtain ⟨θ, hθ, -, hst⟩ := hx x hx' hle.1.1 ι p hp i hi Y hY Z TF
  have hJ := hx1 x hx' hle.1.2 ι p hp i hi Y hY Z TF _ (Or.inl rfl)
  have hD := hx2 x hx' hle.2.1 ι p hp i hi Y hY Z TF
  have hf : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by
    have h3 : Module.finrank ℚ (Fm.D x ι).host.E = 4 * (Fm.D x ι).R.ord :=
      (Fm.D x ι).host.finrank_cmField
    have h : 4 ≤ (Fm.D x ι).R.ord := (Fm.D x ι).host.four_le_n'
    omega
  have hCI : ∀ la, CuspIso TF.X Z Y.U la := fun la =>
    ⟨_root_.GlobalTheory.CompHS.cusp_extends_comp _ _ _ Y _ _ hY.1 hf Z TF _, vanBd_le_space _ _ _ Y _ _ hY.1 hf Z TF _⟩
  have hfree := _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP' hGD hQ hP.q15 hP.q16 hS hT.toroidalChartsForFan hL _ _ _ _ _ _ TF Z _ Y.U hY.1.geo
    hB.one_le _ (gaps_of_wtBig _ _ _ _ hB _ List.mem_cons_self).2 (hCI _)
  refine valMult_of_section TF.X Z Y.U (GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.1.geo) hCI ?_ hfree θ hθ
    fun y hy ν hν => ?_
  · rw [CompHt.uPrime]
    module
  obtain ⟨φ, hφ, hPh⟩ := hD y hy ν hν
  obtain ⟨w, hw, hwb⟩ := hJ y hy ν hν φ hPh
  refine ⟨w, hw, fun j hj j' hj' => ?_⟩
  obtain ⟨hw0, hwm⟩ := hwb j' hj'
  obtain ⟨zw, hzw⟩ := WithZero.ne_zero_iff_exists.1 hw0
  have ew : ν (H0.germ j' y (memTop y) hj' w) =
      ((Multiplicative.ofAdd (-(-Multiplicative.toAdd zw)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [neg_neg, ofAdd_toAdd]; exact hzw.symm
  have bw := hwm _ ew
  by_cases h0 : ν (H0.germ j y (memTop y) hj θ) = 0
  · rw [h0, zero_pow three_ne_zero]
    exact zero_le
  · obtain ⟨zt, hzt⟩ := WithZero.ne_zero_iff_exists.1 h0
    have et : ν (H0.germ j y (memTop y) hj θ) =
        ((Multiplicative.ofAdd (-(-Multiplicative.toAdd zt)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      rw [neg_neg, ofAdd_toAdd]; exact hzt.symm
    have bt := hst y hy ν hν φ hPh j hj _ et
    have hle' : (3 * Multiplicative.toAdd zt : ℝ) ≤ (8 * Multiplicative.toAdd zw : ℝ) := by
      push_cast at bw bt ⊢
      linarith
    have hle'' : 3 * Multiplicative.toAdd zt ≤ 8 * Multiplicative.toAdd zw := by exact_mod_cast hle'
    rw [← hzt, ← hzw, ← WithZero.coe_pow, ← WithZero.coe_pow, WithZero.coe_le_coe, ← Multiplicative.toAdd_le,
      toAdd_pow, toAdd_pow]
    simpa using hle''
end GlobalTheory.ValMultRun
end
end
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_multiplicity_run_estimate_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, ValMult Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) (wtOf (dat p i) (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) 0) := by
  exact @_root_.GlobalTheory.ValMultRun.valuation_multiplicity_of_consecutive_run_alt
end
end
