import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult GlobalTheory.TensorHW GlobalTheory.BlockReps
open Matrix
open scoped Kronecker

namespace GlobalTheory.UnitaryTrick

variable {R S : ℕ}

def HasModel (Λ : Ix R S → ℚ) : Prop :=
  ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (ρ : Mat R S →ₗ[ℂ] Matrix X X ℂ) (u : X → ℂ),
    (∀ Y Z, IsKC Y → IsKC Z → ρ (Y * Z - Z * Y) = ρ Y * ρ Z - ρ Z * ρ Y) ∧
    (∀ a b, (ρ (Eab a b))ᴴ = ρ (Eab b a)) ∧ u ≠ 0 ∧
    (∀ a, ρ (Eab a a) *ᵥ u = ((Λ a : ℚ) : ℂ) • u) ∧ ∀ a b, posC a b → ρ (Eab a b) *ᵥ u = 0

lemma kron_mulVec {X Y : Type} [Fintype X] [Fintype Y] (A : Matrix X X ℂ) (B : Matrix Y Y ℂ) (u : X → ℂ) (w : Y → ℂ) :
    (A ⊗ₖ B) *ᵥ (fun x => u x.1 * w x.2) = fun x => (A *ᵥ u) x.1 * (B *ᵥ w) x.2 := by
  ext ⟨i, j⟩
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum, kroneckerMap_apply]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma HasModel.add {Λ M : Ix R S → ℚ} (h : HasModel Λ) (h' : HasModel M) : HasModel (Λ + M) := by
  obtain ⟨X, _, _, ρ, u, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨Y, _, _, σ, w, k1, k2, k3, k4, k5⟩ := h'
  let τ : Mat R S →ₗ[ℂ] Matrix (X × Y) (X × Y) ℂ :=
    { toFun := fun Z => ρ Z ⊗ₖ 1 + 1 ⊗ₖ σ Z
      map_add' := fun Z Z' => by simp only [map_add, add_kronecker, kronecker_add]; abel
      map_smul' := fun c Z => by simp only [map_smul, smul_kronecker, kronecker_smul, RingHom.id_apply, smul_add] }
  have hτ : ∀ Z, τ Z = ρ Z ⊗ₖ 1 + 1 ⊗ₖ σ Z := fun _ => rfl
  refine ⟨X × Y, inferInstance, inferInstance, τ, fun x => u x.1 * w x.2, fun A B hA hB => ?_, fun a b => ?_,
    fun h0 => ?_, fun a => ?_, fun a b hab => ?_⟩
  · rw [hτ, hτ, hτ, h1 A B hA hB, k1 A B hA hB]
    have e1 : ∀ P Q : Matrix X X ℂ, (P - Q) ⊗ₖ (1 : Matrix Y Y ℂ) = P ⊗ₖ 1 - Q ⊗ₖ 1 := fun P Q => by
      ext i j; simp [sub_mul]
    have e2 : ∀ P Q : Matrix Y Y ℂ, (1 : Matrix X X ℂ) ⊗ₖ (P - Q) = 1 ⊗ₖ P - 1 ⊗ₖ Q := fun P Q => by
      ext i j; simp [mul_sub]
    simp only [add_mul, mul_add, ← mul_kronecker_mul, mul_one, one_mul, e1, e2]
    abel
  · rw [hτ, hτ, conjTranspose_add, conjTranspose_kronecker, conjTranspose_kronecker, h2, k2, conjTranspose_one,
      conjTranspose_one]
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h3
    obtain ⟨y, hy⟩ := Function.ne_iff.1 k3
    exact mul_ne_zero hx hy (congrFun h0 (x, y))
  · rw [hτ, add_mulVec, kron_mulVec, kron_mulVec, h4, k4, one_mulVec, one_mulVec]
    ext x
    simp
    ring
  · rw [hτ, add_mulVec, kron_mulVec, kron_mulVec, h5 a b hab, k5 a b hab]
    ext x
    simp

end GlobalTheory.UnitaryTrick

end
