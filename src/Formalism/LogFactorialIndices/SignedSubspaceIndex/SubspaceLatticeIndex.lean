import Formalism.LogFactorialIndices.StatementIdx
import Mathlib

open scoped Pointwise

noncomputable section

namespace Formalism.LatticeIndexTer.subgroupData

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

theorem length_le_of_le {S T A B : Submodule O X} (hST : S ≤ T) (hBA : B ≤ A)
    (hSA : S ⊓ A ≤ B) :
    Module.length O (S ⧸ B.comap S.subtype) ≤ Module.length O (T ⧸ A.comap T.subtype) := by
  let f : (S ⧸ B.comap S.subtype) →ₗ[O] (T ⧸ A.comap T.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hST) (fun x hx => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_inclusion] at hx ⊢
      exact hBA hx)
  apply Module.length_le_of_injective f
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [f, Submodule.mapQ_apply] at hxy
  rw [Submodule.Quotient.eq] at hxy ⊢
  simp only [Submodule.mem_comap, Submodule.coe_subtype, map_sub, Submodule.coe_inclusion]
    at hxy ⊢
  exact hSA (Submodule.mem_inf.mpr ⟨S.sub_mem x.2 y.2, hxy⟩)

theorem qlen_eq_zero {A B : Submodule O X} (h : A ≤ B) : qlen O X A B = 0 := by
  unfold qlen
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Submodule.Quotient.eq]
  exact h (a - b).2

end Formalism.LatticeIndexTer.subgroupData

namespace Formalism.LatticeIndexTer

end Formalism.LatticeIndexTer
