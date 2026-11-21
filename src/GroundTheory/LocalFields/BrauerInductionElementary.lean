import Mathlib

noncomputable section

namespace GroundTheory.LocalField

variable {G : Type*} [Group G]

def IsElementaryAt (p : ℕ) (H : Subgroup G) : Prop :=
  ∃ C P : Subgroup G, C ≤ H ∧ P ≤ H ∧ IsCyclic C ∧ (Nat.card C).Coprime p ∧ IsPGroup p P ∧
    (∀ c ∈ C, ∀ y ∈ P, c * y = y * c) ∧ ∀ h ∈ H, ∃ c ∈ C, ∃ y ∈ P, h = c * y

variable [Finite G] {p : ℕ}

end GroundTheory.LocalField
