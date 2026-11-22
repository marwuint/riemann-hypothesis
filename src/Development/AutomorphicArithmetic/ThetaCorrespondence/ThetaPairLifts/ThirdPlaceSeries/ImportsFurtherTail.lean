import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialBoundSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalCongruenceCountOfRootDifferenceUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalStepObjectsOfCyclotomicGeneratorInerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalSlotDataOffExceptionalPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfLargeResidueChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoTopOfLocalTateDualityEulerChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachFunctorComparisonOfBhattScholze
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostRamificationIdxEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersOfLargeScale
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BigImageThirdCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoCharacterOffsetUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceBoundExtendedOfRationalBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundZeroAtLargePrimesOfCongruenceBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExcludedPrimesFewAndSmallAlongFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LongOrbitsRowColengthInertLocalisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowsCDRowConditionLocalBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamifiedCoefficientChainsPrvTwentyFive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBOfBlochKatoTateDualityEulerC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2TwistSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG5Setup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftColumnRowSetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmH0Setup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientSubContinuitySetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolySpanAndHomRelationsOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxLengthLocalInvariantsTwistedFractionModIntege
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitInvariantsTwistedLatticeLeOfKillingExponeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonPlacePartLocalBoundLeMiddleRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarInequalityRowsADOfGlobalTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCaseBoundAtPointOfAdmittedItems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SizeConditionsMonotoneInConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPointMultiplicityLeRankProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableFromDataBandCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableRowsCDAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousComplementFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistAnnihilatesSelmerGroups
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialPrimesSmallAlongFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarBoundOfMultiplicity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremECorollaryAClosingAllDataStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoEALe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerMore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolyValLeSumMulPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamJointBCD
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNeTypePrime
import Development.AutomorphicArithmetic.ResidueCharacters.RowDef
import Development.AutomorphicArithmetic.ResidueCharacters.ConclusionSplitOfHub
import Development.AutomorphicArithmetic.ResidueCharacters.PlaceTypeConj
import Development.AutomorphicArithmetic.ResidueCharacters.LenUnitInvariantsLe
import Development.AutomorphicArithmetic.ResidueCharacters.LocAll
import Development.AutomorphicArithmetic.ResidueCharacters.NumRow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PolynomialBoundSetup
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NStarS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSetupLargeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleParameterEventuallyStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamJointBCDClosed
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsADInSettingStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EtaLocLeRhsStatement

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLinkClose
theorem main_alt_alt : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C : ℝ) (CT : ℕ), 0 ≤ C → TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT →
    _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm → ConclF Fm := by
  intro hP eps Fm C CT hC0 hTw hF h23
  obtain ⟨C₀, h03⟩ := GlobalTheory.T.theoremE_corollaryA_closing_all_data hP.bk hP.tate hP.euler
  obtain ⟨constantFirstHub, Q, h67⟩ := _root_.GlobalTheory.T.embedding_jumps_aux2_of_setup
  obtain ⟨C1, xpar, hC1, hpar⟩ := _root_.GlobalTheory.NLink.admissible_parameters_design_family Fm
  obtain ⟨Ca, xa, ha⟩ := h23
  obtain ⟨Cb, xb, hb'⟩ := _root_.UpperTheory.N.starSF_of_prints hP Fm
  set ComplexParameterFamilyContinuity : ℝ := max 0 (max Ca Cb) with hC23def
  set x23 : ℝ := max 1 (max xa xb) with hx23def
  set C₂ : ℝ := max C₀ 1 with hC₂def
  set Cs : ℝ := max (3 * C₂ + 1) (max 22365 (max (FamilyRepresentationConstants.CG constantFirstHub Q) (max (2000 * (C + 1) + 5 * C1)
    (max C1 (max ComplexParameterFamilyContinuity (CT : ℝ)))))) with hCsdef
  have hA : 3 * C₂ + 1 ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hK : (22365 : ℝ) ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hG : FamilyRepresentationConstants.CG constantFirstHub Q ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hT : 2000 * (C + 1) + 5 * C1 ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hP1 : C1 ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have h23C : ComplexParameterFamilyContinuity ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hCT : (CT : ℝ) ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hCs1 : (1 : ℝ) ≤ Cs := by linarith
  have hCs0 : (0 : ℝ) ≤ Cs := by linarith
  have hC₂1 : (1 : ℝ) ≤ C₂ := le_max_right _ _
  have hC₂0 : C₀ ≤ C₂ := le_max_left _ _
  have hRle : (rowC C₂).Le Cs := by
    simp only [KillingConditions.RowK.Le, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃, rowC]
    refine ⟨hC₂1, ?_, ?_, ?_, hCs1, hA, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  obtain ⟨xset, hset⟩ := _root_.GlobalTheory.T.exists_hubData_admJ_setup hP Fm C C₂ CT hTw hF
  obtain ⟨xexc, hexc⟩ := _root_.GlobalTheory.NLink.excOK_family Fm
  obtain ⟨xsm, hsm⟩ := _root_.GlobalTheory.SpecialSmall.special_primes_small Fm Cs hCs1
  obtain ⟨xE, hE⟩ := _root_.GlobalTheory.T.eventually_congBound_of_facts hP Fm
  obtain ⟨xbcd, hbcd⟩ := _root_.GlobalTheory.HTW.RecS.fam_jointBCD_closed_alt hP.font GlobalTheory.Per.FontaineAll.fontaine_bounds
    GlobalTheory.FontaineAdm.fontaineProperties_all_places _root_.GlobalTheory.JumpStatement.holds_all_alt Fm (rowC C₂)
  refine ⟨Cs, max xset (max xexc (max xsm (max xE (max xbcd (max xpar x23))))), ?_⟩
  intro x hx0 hx i hSha
  simp only [ge_iff_le, max_le_iff] at hx0
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hx0
  obtain ⟨exc, hexcEq, hexcOK⟩ := hexc x h2 hx i
  obtain ⟨HW, F, Cm, X, hXexc, hAdmJ, hS⟩ := hset x h1 hx i hSha exc
  obtain ⟨hFa, hEx⟩ := hF x hx i
  obtain ⟨hSm, -, -, hb⟩ := hsm x h3 hx i
  have hBCD := hbcd x h5 hx i HW X hAdmJ hS.canon.fam
  have hmid := _root_.GlobalTheory.T.star_ad_and_bb_le_of_joint_cond hP (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.ex x hx i).nch HW F Cm X C₂ hS hC₂1
    ((h03 (Fm.D x i) HW F Cm).2 C₂ hC₂0) hBCD
  have hparC1 := hpar x h6 hx i
  have hmult := _root_.GlobalTheory.NLink.multLe_of_rank (Fm.D x i) (Fm.L x i) hFa.Conclusion1.2.2 hFa.Conclusion2.2.2 hFa.toCore.isot hFa.c2
  have hSizeG : SizeG (Fm.L x i) := (Fm.sizes x hx i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCTb : (CT : ℝ) ≤ (Fm.L x i).sc.b := le_trans hCT hb
  have htyp := _root_.GlobalTheory.T.star_bound_of_paired_character_condition hP (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.ex x hx i).nch HW F Cm X C₂ hS C C1 CT
    hC0 hC1 hCTb hEx.2 hmult hparC1 hSizeG
  have hmono := _root_.GlobalTheory.NLinkMono.main (Fm.D x i) (Fm.L x i) (Fm.params x hx i) X
  have hCong := hE x h4 hx i hFa
  have hlarge := _root_.GlobalTheory.NLink.RowE.main (Fm.D x i) (Fm.L x i) X.r X.ρ X.exc hCong hFa.toCore.weight hS.canon.fam hS.kill hSha
    hSm.1 (by rw [hXexc]; exact hexcEq)
  have hxa : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h7
  have hxb : xb ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h7
  have hmid23 : ∀ C', C' ≤ ComplexParameterFamilyContinuity → midF (Fm.L x i) C' ≤ midF (Fm.L x i) ComplexParameterFamilyContinuity := fun C' hC' =>
    midF_mono _ hC' (le_max_left _ _)
  have htwo : StarF (Fm.L x i) X.ρ ComplexParameterFamilyContinuity := by
    refine starF_of _ _ _ (fun k hk hl π hπ => ?_) (fun k hk hl h5 π hπ => ?_)
    · have h := ha x hxa hx i HW F Cm X C₂ hS k hk hl π hπ
      have h' := hmid23 Ca (le_trans (le_max_left _ _) (le_max_right _ _))
      unfold Bd at h ⊢; linarith
    · have h := hb' x hxb hx i HW F Cm X C₂ hS k hk hl h5 π hπ
      have h' := hmid23 Cb (le_trans (le_max_right _ _) (le_max_right _ _))
      unfold Bd at h ⊢; linarith
  refine ⟨X, ?_⟩
  exact
    { pos := hCs0
      pass := GlobalTheory.EtaPassage.main _ hEx.1
      mult := hmult
      rank := hFa.toCore.a3 _
      kill := hS.kill
      num := ⟨GlobalTheory.NLink.RowA.main _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle,
        GlobalTheory.NLink.localBoundTableFromData_rowB_rowEntries _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle,
        (_root_.GlobalTheory.NLink.localBoundTable_rowsCD_admissible _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle).1,
        (_root_.GlobalTheory.NLink.localBoundTable_rowsCD_admissible _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle).2,
        _root_.GlobalTheory.NBand.bandPlaceWeightApproximation_tabX _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle hS.par67⟩
      mid := hmid.1
      bb := ((hmono 7200 Cs (by linarith) hCs0).2.2.1) hmid.2
      large := hlarge
      exc := by rw [hXexc]; exact hexcOK
      two := ((hmono ComplexParameterFamilyContinuity Cs h23C hCs0).1) htwo
      ram := GlobalTheory.NLink.starG_of_thmB _ _ (Fm.params x hx i) X.ρ constantFirstHub Cs Q hG
        (h67 hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ hS) hS.kill hSha
      typ := ((hmono _ Cs hT hCs0).2.1) htyp
      par := ((hmono C1 Cs hP1 hCs0).2.2.2) hparC1
      small := hSm }
end GlobalTheory.NLinkClose
end
