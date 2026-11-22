import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfLiftingTheory
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictAdm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ElementDenominatorAdm7
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremWachModuleLemmaHypothesesAdmitted
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisRest

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AdmittedPartOne

theorem all_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ElementDenominator.Adm1 D HW F Cm 23 32 32 := by
  intro hBK hTD hEC D HW F Cm
  have hU := (_root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm).1
  have h54 := _root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hBK hTD hEC D HW F Cm
  have hA := (_root_.GlobalTheory.LiftAdmitted.all_admitted D HW F Cm).1
  refine ⟨hU.1, hU.2.2.1, _root_.GlobalTheory.res_cor_H1f D HW F, hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    GlobalTheory.AdmHerrLocal.main D HW F, hU.2.2.2, archimedean_signature_matching_of_liftingTheory D HW F 23 32 32 10 h54,
    lifting_input_five_of_lifting D HW F 10 23 32 32 h54, lifting_input_six_of_lifting D HW F 10 23 32 32 h54,
    _root_.GlobalTheory.elementDenominator_adm7 D, GlobalTheory.Per.FontaineAdm.fontaine_bounds D, GlobalTheory.Per.StrictAdm.strict_adm D, _root_.GlobalTheory.Per.ResFinite.adm12_elementDenominator D⟩

end GlobalTheory.AdmittedPartOne
