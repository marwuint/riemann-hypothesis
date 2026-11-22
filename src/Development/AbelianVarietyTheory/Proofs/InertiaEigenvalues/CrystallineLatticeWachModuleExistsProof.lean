import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachHypothesisCrystallineLattices
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem wAll_holds : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), WAll D HW F :=
  fun D HW F Cm =>
    _root_.GlobalTheory.WachHyp.hypW_crystalline D HW F Cm (_root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm).1 (_root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm).2 (GlobalTheory.crysOnCond_all D HW F)

end GlobalTheory.NLink
