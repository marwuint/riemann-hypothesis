import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LongOrbitsRowColengthInertLocalisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowsCDRowConditionLocalBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamifiedCoefficientChainsPrvTwentyFive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBOfBlochKatoTateDualityEulerC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SetPointGood

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink.InertStep
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.InertK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admitted i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i) := by
  intro hP D L P nch HW F Cm X C₂ hS hC hconds2 hBCD i htw hg hR hin π hπ
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG5x, hG6, hBK, hCont, hSS, hDec, hEps, hTie, hShape, hFont, hH2, hCFT⟩ :=
    _root_.GlobalTheory.T.set_pt_of_setup_not_twisted hP D L P nch HW F Cm X C₂ hS i hg π hπ
  have hcB : ∀ i', GlobalTheory.HubLoc.cBnum (D.nd.l i') ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i' := by
    intro i'
    rw [hS.canon.cB]
    exact le_rfl
  have hX := _root_.GlobalTheory.closingFamilyX_alt_alt hP.font hP.fin D HW F L X (_root_.GlobalTheory.JumpStatement.holds_all_alt D)
    (hS.facts.admJ L hS.par) hS.par67 hS.facts.Conclusion1.1 hS.facts.large.2.1 hS.canon.fam hcB
  obtain ⟨M0, h0, hJ⟩ := hX.2.1 i hR π
  have hTB : TruncatedSeriesCountingIdentities.admTB i (X.r i) π (X.cB i) :=
    _root_.GlobalTheory.TBLocal.main D HW F i (X.r i) (X.ρ i) π M0 h0 (X.cB i)
      (_root_.GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar hP.bk hP.tate hP.euler D HW F Cm) (_root_.GlobalTheory.NLink.wAll_holds D HW F Cm) (GlobalTheory.crysOnCond_all D HW F) hFont hJ
  have h11 : 11 ≤ D.nd.l i := by
    have := D.nd.lPrime i
    exact GlobalTheory.Survey.InertPlacesGoodSet.eleven_le this.out hin (le_trans (by norm_num) hS.split)
  have hD := hS.canon.data
  have hROW : TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) := by
    by_cases hB : KillingConditions.IsRowB L (D.nd.l i)
    · rw [hD.rowB i hin hB]
      exact _root_.GlobalTheory.RowBLong.main D L P HW C₂ i (X.r i) (X.ρ i) π (X.dc i) hconds2 hC hS.par67 h11
        ((hBCD i htw hin π hπ).1 hB)
    · have hband : X.band i = fun lam => bandOf L HW 320 i (X.r i) (X.ρ i) lam := by
        funext lam
        exact propext (hD.band i lam)
      rw [hD.rowCD i hin hB, hband]
      exact _root_.GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond D L P HW F C₂ i (X.r i) (X.ρ i) π (X.dc i)
        (_root_.GlobalTheory.theoremB_closing hP.bk hP.tate hP.euler D HW F Cm 320 le_rfl)
        (_root_.GlobalTheory.ramifiedCoefficientChains_prv_twenty_five hP.bk hP.tate hP.euler D HW F Cm)
        (_root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hP.bk hP.tate hP.euler D HW F Cm) hS.par67 h11 hπ ((hBCD i htw hin π hπ).2 hB)
  have hLIFT : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i (X.r i) (X.dc i) (X.e' i) := by
    intro w hw hwc
    rw [hD.col i hin] at hwc
    simp at hwc
  exact ⟨hG1, hG2, hG3, hG4, hG5, hG5x, hG6, hBK, hTB, hROW, hLIFT, hCont, hSS, hDec, hEps, hTie, hShape, hFont,
    hH2, hCFT⟩
end GlobalTheory.NLink.InertStep
end
