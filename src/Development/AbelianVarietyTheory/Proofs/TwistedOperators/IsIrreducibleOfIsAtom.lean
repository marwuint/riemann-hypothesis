import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvAtParabNeZero

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses GlobalTheory.TypeDim ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.MaschkeForms

open Representation

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_of_isAtom {π : Representation ℂ G V} {U : Subrepresentation π}
    (hU : IsAtom U) : U.toRepresentation.IsIrreducible := by
  have hne : U.toSubmodule ≠ ⊥ := fun h => hU.1 (Subrepresentation.toSubmodule_injective h)
  have hnt : Nontrivial (Subrepresentation U.toRepresentation) := by
    refine ⟨⊥, ⊤, fun h => hne ?_⟩
    have h' : (⊥ : Submodule ℂ U.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [← U.toSubmodule.map_subtype_top, ← h', Submodule.map_bot]
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation π := ⟨S.toSubmodule.map U.toSubmodule.subtype, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨_, S.apply_mem_toSubmodule g hx, rfl⟩⟩
  have hT : T ≤ U := U.toSubmodule.map_subtype_le S.toSubmodule
  have hinj := Submodule.map_injective_of_injective U.toSubmodule.injective_subtype
  rcases hU.le_iff.mp hT with h | h
  · left
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans (Submodule.map_bot _).symm
  · right
    refine Subrepresentation.toSubmodule_injective (hinj ?_)
    exact (congrArg Subrepresentation.toSubmodule h).trans U.toSubmodule.map_subtype_top.symm

end GlobalTheory.MaschkeForms
