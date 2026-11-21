import Mathlib

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeCosetUniformizer

open Matrix IsLocalRing

section Objects

variable (O F : Type) [CommRing O] [Field F] [Algebra O F] (n : ℕ)

def integralGL : Subgroup (GL (Fin n) F) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap O F)).range

def inclVec : (Fin n → O) →ₗ[O] (Fin n → F) :=
  (Algebra.linearMap O F).compLeft (Fin n)

def stdLattice : Submodule O (Fin n → F) := LinearMap.range (inclVec O F n)

variable {F n}

def latticeOf (g : GL (Fin n) F) : Submodule O (Fin n → F) :=
  (stdLattice O F n).map
    ((Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) F)).restrictScalars O)

theorem mem_latticeOf (g : GL (Fin n) F) (x : Fin n → F) :
    x ∈ latticeOf O g ↔
      ∃ v : Fin n → O, (g : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => algebraMap O F (v i)) = x := by
  constructor
  · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨_, ⟨v, rfl⟩, rfl⟩

theorem latticeOf_mul_le (g k : GL (Fin n) F) (hk : k ∈ integralGL O F n) :
    latticeOf O (g * k) ≤ latticeOf O g := by
  obtain ⟨k₀, rfl⟩ := hk
  intro x hx
  rw [mem_latticeOf] at hx ⊢
  obtain ⟨v, rfl⟩ := hx
  refine ⟨(k₀ : Matrix (Fin n) (Fin n) O) *ᵥ v, ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem latticeOf_mul (g k : GL (Fin n) F) (hk : k ∈ integralGL O F n) :
    latticeOf O (g * k) = latticeOf O g := by
  refine le_antisymm (latticeOf_mul_le O g k hk) ?_
  have h := latticeOf_mul_le O (g * k) k⁻¹ (inv_mem hk)
  rwa [mul_inv_cancel_right] at h

def latticeOfCoset (c : GL (Fin n) F ⧸ integralGL O F n) : Submodule O (Fin n → F) :=
  Quotient.liftOn' c (latticeOf O) (by
    intro a b hab
    have h := latticeOf_mul O a (a⁻¹ * b) (QuotientGroup.leftRel_apply.mp hab)
    rw [mul_inv_cancel_left] at h
    exact h.symm)

@[simp] theorem latticeOfCoset_mk (g : GL (Fin n) F) :
    latticeOfCoset O (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL O F n) = latticeOf O g := rfl

def scaleBy (a : O) (L : Submodule O (Fin n → F)) : Submodule O (Fin n → F) :=
  L.map (a • LinearMap.id)

end Objects

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeCosetUniformizer
