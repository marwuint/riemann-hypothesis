import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem lifting_local_of_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.ConclusionL D HW F := h.1

theorem wach_of_lifting_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.ConclusionW D HW F := h.2.1

theorem lift_of_lifting_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK := h.2.2.2.2.2.2.2

end Formalism.MainNotions.N
