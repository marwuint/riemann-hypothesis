import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundAtPointAllLocalisationsOfObjectConditionsAl

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.InertiaEigenvalues.LengthBoundClosing

theorem stmt_closed : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.Stmt D := by
  intro hA hB hT hE D h51
  exact ⟨_root_.GlobalTheory.LocalisationBoundAtPoint.boundAtPoint_all_localisations_of_objectConditions hA hB hT hE D h51, Formalism.MainNotions.TruncatedSeriesCountingIdentities.second_statement D⟩

end GlobalTheory.InertiaEigenvalues.LengthBoundClosing
