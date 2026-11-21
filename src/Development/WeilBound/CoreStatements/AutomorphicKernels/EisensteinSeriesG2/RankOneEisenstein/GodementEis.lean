import Mathlib
import GroundTheory.AutomorphicForms.GL2.GodementSection

open NumberField Matrix
open scoped NumberField.AdeleRing

namespace PositivityTheory.EisRk1

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection

variable (K : Type*) [Field K] [NumberField K]

def borelK : Subgroup (GL (Fin 2) K) where
  carrier := {γ | (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at *
    rw [ha, hb]; ring
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two]
    simp [ha]

abbrev BCoset : Type _ := Quotient (QuotientGroup.rightRel (borelK K))

variable {K}

noncomputable def godementEis (χ₁ χ₂ : HeckeCharacter K) (s : ℂ) (Φ : (Fin 2 → 𝔸[K]) → ℂ)
    (g : GL (Fin 2) 𝔸[K]) : ℂ :=
  ∑' c : BCoset K, godementSection χ₁ χ₂ s Φ (AdelicGLn.diagonal K 2 c.out * g)

structure IsEisCont (χ₁ χ₂ : HeckeCharacter K) (Φ : (Fin 2 → 𝔸[K]) → ℂ)
    (F : ℂ → GL (Fin 2) 𝔸[K] → ℂ) : Prop where
  entire : ∀ g, Differentiable ℂ fun s ↦ F s g
  cont : Continuous fun p : ℂ × GL (Fin 2) 𝔸[K] ↦ F p.1 p.2
  eq_eis : ∀ s : ℂ, 1 < s.re → ∀ g, F s g = s * (s - 1) * godementEis χ₁ χ₂ s Φ g
  strip : ∀ a b : ℝ, ∀ Ω : Set (GL (Fin 2) 𝔸[K]), IsCompact Ω →
    ∃ C N : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ∀ g ∈ Ω, ‖F s g‖ ≤ C * (1 + ‖s‖) ^ N

variable (K)

end PositivityTheory.EisRk1
