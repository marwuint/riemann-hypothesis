import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.HerrClassFieldOfNorms
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.HerrDescriptionH1OfHerr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrPartAEveryRecord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrExtensionClassFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimFormulaAllLocalSituations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratorsAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHold
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaSubOneDivUniformiserAtLetterOfConclusions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedForms
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremCAdm

theorem admissible_ranks_of_CMDatum : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      RamifiedCoefficientChains.admitted D HW F Cm 10 23 32 32 := by
  intro hBK hTD hEC D HW F Cm
  have hU := (_root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm).1
  have h54 := _root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hBK hTD hEC D HW F Cm
  have h6a := GlobalTheory.HerrFull.herr_part_a_every_record D HW F
  exact ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2,
    RamifiedCoefficientChains.sizes_bound_of_log_estimates D HW F h54, RamifiedCoefficientChains.restriction_dimension_of_division D HW F h54, RamifiedCoefficientChains.level_tools_of_admitted D HW F h54, RamifiedCoefficientChains.lemma_M_prime_hypothesis D HW F h54,
    RamifiedCoefficientChains.crystalline_lift_of_theorem_c D HW F h54, RamifiedCoefficientChains.lifting_bounds_of_theorem_c D HW F h54,
    _root_.GlobalTheory.Per.DcrisExact.fontaine_dcris D, _root_.GlobalTheory.blochKatoDim_at_every_local_situation D, _root_.GlobalTheory.h1f_generators_of_record D,
    Formalism.MainNotions.N.herr_description_H1_of_herr D HW F h6a, _root_.GlobalTheory.ExtCrysCrit.blochKato_ext_all D,
    GlobalTheory.HerrExtClass.herr_extension_class_formula D HW F,
    Formalism.MainNotions.HerrComplexNaturality.herr_naturality_theorem_holds D HW F h6a,
    _root_.GlobalTheory.adm18_of_N1used D HW F Cm (_root_.GlobalTheory.NL.wach_used_clauses D HW F Cm),
    _root_.GlobalTheory.GenCountUnram.admGenL_all D⟩

end GlobalTheory.TheoremCAdm
