import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.WachRestrictionOfLiftingPackage
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem archimedean_signature_matching_of_liftingTheory (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA : ℝ) (CB : ℝ) (CK : ℝ) (C : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.ArchimedeanSignatureMatching D HW F CA CB CK := by
  unfold Formalism.MainNotions.ElementDenominator.ArchimedeanSignatureMatching
  exact lift_of_lifting_package D HW F C CA CB CK h54

theorem lifting_input_five_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.adm5 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm5
  exact wach_of_lifting_package D HW F C CA CB CK h54

theorem lifting_input_six_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.adm6 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm6
  exact lifting_local_of_package D HW F C CA CB CK h54

end Formalism.MainNotions.N
