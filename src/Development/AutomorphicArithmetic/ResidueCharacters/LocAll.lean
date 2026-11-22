import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProof
import Development.AutomorphicArithmetic.ResidueCharacters.LocAllOf

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem UpperTheory.N.locAll : Hypotheses₂ → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (_ : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime],
    UpperTheory.N.LiftK (D.loc l) ∧ UpperTheory.N.InvariantsKilledOverCyclotomic (D.loc l) ∧ UpperTheory.N.TBK (D.loc l) :=
  fun hP D HW F Cm l _ => UpperTheory.N.locAll_of hP.bk hP.tate hP.euler D HW F Cm l
    (_root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hP.bk hP.tate hP.euler D HW F Cm).2.2.2.2.2.2.2 (_root_.GlobalTheory.NLink.wAll_holds D HW F Cm l)
