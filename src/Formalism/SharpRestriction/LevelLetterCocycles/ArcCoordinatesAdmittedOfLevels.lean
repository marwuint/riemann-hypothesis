import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfLevelZeroParts

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem arc_coordinates_of_levels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : LevelZeroModPLocal D HW) (h2 : LevelZeroModPRefinedLocal D HW) : ArcCoordinatesTheorem D HW F Cm := Formalism.MainNotions.UnusedSlot80.arc_coordinates_of_level_zero_parts D HW F Cm h1 h2

end Formalism.MainNotions.UnusedSlot80
