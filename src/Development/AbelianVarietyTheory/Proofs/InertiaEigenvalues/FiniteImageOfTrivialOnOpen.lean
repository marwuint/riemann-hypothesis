import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIndexOfIsOpenAbsGaloisFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageFiniteOfTrivialOnInfFiniteIndex
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory

theorem GK.finite_image_of_trivial_on_open :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (Q : Type) [Group Q] (ρ : ↥(GK K) →* Q)
      (J H : Subgroup ↥(GK K)), IsOpen (H : Set ↥(GK K)) → (∀ g ∈ J, g ∈ H → ρ g = 1) →
      (ρ '' (J : Set ↥(GK K))).Finite := by
  intro l _ K Q _ ρ J H hH hρ
  haveI := _root_.GlobalTheory.OpenFiniteIndex.finiteIndex_of_isOpen l K H hH
  exact _root_.GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex _ Q ρ J H inferInstance hρ

end GlobalTheory
