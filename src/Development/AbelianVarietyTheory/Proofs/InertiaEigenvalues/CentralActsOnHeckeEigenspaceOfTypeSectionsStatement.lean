import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralActsOnHeckeEigenspaceOfTypeSections
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralActsOnHeckeEigenspace_of_typeSections : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), (∀ i, Nonempty (Sec D i)) → OnMtPreservesTypeV D → EigSpan P := by
  exact @GlobalTheory.PendOf.EigSpanProof.main
