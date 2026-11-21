import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgLowZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SmoothCartan

noncomputable section

open scoped Matrix.Norms.L2Operator
open ReciprocityTheory.ChartRestriction.DS Matrix

namespace GlobalTheory.Kg

variable {T : Type} [Fintype T] [DecidableEq T] {n : ℕ}

abbrev MatT (T : Type) (n : ℕ) : Type := T → Matrix (Fin n) (Fin n) ℂ

def UJfam (ε : T → Fin n → Bool) : Subgroup (MatT T n)ˣ where
  carrier := {g | ∀ τ, (g.val τ)ᴴ * Jm (ε τ) * g.val τ = Jm (ε τ)}
  one_mem' τ := by simp
  mul_mem' {g h} hg hh τ := by
    simp only [Units.val_mul, Pi.mul_apply, Matrix.conjTranspose_mul]
    calc (h.val τ)ᴴ * (g.val τ)ᴴ * Jm (ε τ) * (g.val τ * h.val τ)
        = (h.val τ)ᴴ * ((g.val τ)ᴴ * Jm (ε τ) * g.val τ) * h.val τ := by simp only [Matrix.mul_assoc]
      _ = Jm (ε τ) := by rw [hg τ, hh τ]
  inv_mem' {g} hg τ := by
    have h1 : g.val τ * (g⁻¹).val τ = 1 := by
      rw [← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Pi.one_apply]
    calc ((g⁻¹).val τ)ᴴ * Jm (ε τ) * (g⁻¹).val τ
        = ((g⁻¹).val τ)ᴴ * ((g.val τ)ᴴ * Jm (ε τ) * g.val τ) * (g⁻¹).val τ := by rw [hg τ]
      _ = (g.val τ * (g⁻¹).val τ)ᴴ * Jm (ε τ) * (g.val τ * (g⁻¹).val τ) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Jm (ε τ) := by rw [h1]; simp

end GlobalTheory.Kg

end
