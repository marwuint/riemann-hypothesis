import Mathlib

noncomputable section

namespace GroundTheory.Automorphic

open Module Submodule
open scoped RealInnerProductSpace

universe u

section Dual

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

def latticeDual (L : AddSubgroup X) : AddSubgroup X where
  carrier := {y | ∀ x ∈ L, ∃ n : ℤ, ⟪y, x⟫ = n}
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  add_mem' := fun {a b} ha hb x hx => by
    obtain ⟨m, hm⟩ := ha x hx
    obtain ⟨n, hn⟩ := hb x hx
    exact ⟨m + n, by rw [inner_add_left, hm, hn]; push_cast; ring⟩
  neg_mem' := fun {a} ha x hx => by
    obtain ⟨m, hm⟩ := ha x hx
    exact ⟨-m, by rw [inner_neg_left, hm]; push_cast; ring⟩

end Dual

end GroundTheory.Automorphic
