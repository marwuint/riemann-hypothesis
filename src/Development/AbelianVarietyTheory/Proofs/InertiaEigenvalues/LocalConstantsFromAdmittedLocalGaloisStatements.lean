import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremWachModuleLemmaHypothesesAdmitted
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem localConstants_from_admitted_local_Galois_statements_alt : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      LiftingTheory.aux₃ D HW F 10 23 32 32 :=
  fun _ _ _ D HW F Cm => Formalism.MainNotions.LiftingTheory.frobenius_lifting D HW F Cm (_root_.GlobalTheory.LiftAdmitted.all_admitted D HW F Cm).1

end GlobalTheory
