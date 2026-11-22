import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfLiftingTheory
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneSurjectiveWittTiltStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictAdm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AdmAllRecords

theorem localLifting_admittedHypotheses_all_alt : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ElementDenominator.Adm2 D HW F := by
  intro hBK hTD hEC D HW F _
  exact ⟨_root_.GlobalTheory.res_cor_H1f D HW F, _root_.GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ hBK hTD hEC D, GlobalTheory.Per.FontaineAdm.fontaine_bounds D,
    GlobalTheory.Per.StrictAdm.strict_adm D, _root_.GlobalTheory.Per.ResFinite.adm12_elementDenominator D, GlobalTheory.T.frobenius_sub_one_surjective_witt_tilt⟩

end GlobalTheory.AdmAllRecords
