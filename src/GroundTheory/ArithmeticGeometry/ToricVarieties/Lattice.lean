import Mathlib

namespace GroundTheory.Arith.Toric

open Module PointedCone TensorProduct

section Integral

variable {L E : Type*} [AddCommGroup L] [AddCommGroup E] [Module ℝ E]

def latticePoints (ι : L →ₗ[ℤ] E) (τ : PointedCone ℝ E) : AddSubmonoid L :=
  τ.toAddSubmonoid.comap ι.toAddMonoidHom

@[simp]
theorem mem_latticePoints {ι : L →ₗ[ℤ] E} {τ : PointedCone ℝ E} {m : L} :
    m ∈ latticePoints ι τ ↔ ι m ∈ τ := Iff.rfl

end Integral

section Lattice

variable (N : Type*) [AddCommGroup N]

def toRealSpan : N →ₗ[ℤ] ℝ ⊗[ℤ] N := TensorProduct.mk ℤ ℝ N 1

def toRealDual : Dual ℤ N →ₗ[ℤ] Dual ℝ (ℝ ⊗[ℤ] N) := Module.Dual.baseChange ℝ

variable {N}

theorem toRealSpan_apply (n : N) : toRealSpan N n = (1 : ℝ) ⊗ₜ n := rfl

@[simp]
theorem toRealDual_apply_toRealSpan (m : Dual ℤ N) (n : N) :
    toRealDual N m (toRealSpan N n) = (m n : ℝ) := by
  simp [toRealDual, toRealSpan_apply, Module.Dual.baseChange_apply_tmul]

variable [Module.Free ℤ N] [Module.Finite ℤ N]

end Lattice

section Gordan

variable {N : Type*} [AddCommGroup N]

def dualMonoid (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) : AddSubmonoid (Dual ℤ N) :=
  latticePoints (toRealDual N) (dual (Dual.eval ℝ (ℝ ⊗[ℤ] N)) (σ : Set (ℝ ⊗[ℤ] N)))

variable [Module.Free ℤ N] [Module.Finite ℤ N]

end Gordan

end GroundTheory.Arith.Toric
