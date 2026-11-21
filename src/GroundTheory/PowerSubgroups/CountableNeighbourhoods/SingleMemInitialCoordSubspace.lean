import Mathlib

namespace GroundTheory.Variant₂.N1

def initialCoordSubspace {K : Type*} [Field K] {n : ℕ} (k : ℕ) : Submodule K (Fin n → K) where
  carrier := {v | ∀ i : Fin n, k ≤ (i : ℕ) → v i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c a ha i hi
    simp [ha i hi]

theorem mem_initialCoordSubspace {K : Type*} [Field K] {n k : ℕ} (v : Fin n → K) :
    v ∈ (initialCoordSubspace k : Submodule K (Fin n → K)) ↔ ∀ i : Fin n, k ≤ (i : ℕ) → v i = 0 :=
  Iff.rfl

end GroundTheory.Variant₂.N1
