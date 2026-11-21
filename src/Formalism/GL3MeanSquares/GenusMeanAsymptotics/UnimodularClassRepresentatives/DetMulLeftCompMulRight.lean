import Mathlib

open Matrix TensorProduct

namespace Formalism.HermitianLattices.Ext.L3.LITr

section Herm

variable {K F : Type*} [Field K] [CharZero K] [StarRing K] [Field F] [Algebra F K] {m : ℕ}

def hermSub (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (m : ℕ) :
    Submodule F (Matrix (Fin m) (Fin m) K) where
  carrier := {B | Bᴴ = B}
  add_mem' := by
    intro a b ha hb
    change (a + b)ᴴ = a + b
    rw [Matrix.conjTranspose_add, show aᴴ = a from ha, show bᴴ = b from hb]
  zero_mem' := Matrix.conjTranspose_zero
  smul_mem' := by
    intro c B hB
    change (c • B)ᴴ = c • B
    rw [← algebraMap_smul K c B, Matrix.conjTranspose_smul, show Bᴴ = B from hB, (hF _).2 ⟨c, rfl⟩]

variable (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K))

theorem mem_hermSub (B : Matrix (Fin m) (Fin m) K) : B ∈ hermSub hF m ↔ Bᴴ = B := Iff.rfl

end Herm

end Formalism.HermitianLattices.Ext.L3.LITr
