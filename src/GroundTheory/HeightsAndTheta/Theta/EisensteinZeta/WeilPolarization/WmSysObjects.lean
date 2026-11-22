import Mathlib

noncomputable section

namespace GroundTheory.Heights₂.Theta

open MeasureTheory Matrix

set_option linter.unusedSectionVars false

section Alg

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

@[ext]
structure Heis (ω : LinearMap.BilinForm R W) where

  w : W

  t : R

namespace Heis

variable {ω : LinearMap.BilinForm R W} [Invertible (2 : R)]

instance : Mul (Heis ω) := ⟨fun h h' => ⟨h.w + h'.w, h.t + h'.t + ⅟2 * ω h.w h'.w⟩⟩

instance : One (Heis ω) := ⟨⟨0, 0⟩⟩

instance : Inv (Heis ω) := ⟨fun h => ⟨-h.w, -h.t + ⅟2 * ω h.w h.w⟩⟩

@[simp] theorem mul_w (h h' : Heis ω) : (h * h').w = h.w + h'.w := rfl
@[simp] theorem product_torus_component (h h' : Heis ω) : (h * h').t = h.t + h'.t + ⅟2 * ω h.w h'.w := rfl
@[simp] theorem one_w : (1 : Heis ω).w = 0 := rfl
@[simp] theorem indicator_eq_one_of_true : (1 : Heis ω).t = 0 := rfl
@[simp] theorem inv_w (h : Heis ω) : h⁻¹.w = -h.w := rfl
@[simp] theorem exists_inverse_fontaineElement_mem_fil_neg_one (h : Heis ω) : h⁻¹.t = -h.t + ⅟2 * ω h.w h.w := rfl

instance : Group (Heis ω) where
  mul_assoc a b c := by
    ext
    · simp [add_assoc]
    · simp only [product_torus_component, mul_w, map_add, LinearMap.add_apply]
      ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by
    ext
    · simp
    · simp only [product_torus_component, exists_inverse_fontaineElement_mem_fil_neg_one, inv_w, indicator_eq_one_of_true, map_neg, LinearMap.neg_apply]
      ring

end Heis

variable {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

structure SympPolarization (ω : LinearMap.BilinForm R W) (X Y : Type*) [AddCommGroup X]
    [Module R X] [AddCommGroup Y] [Module R Y] where

  e : W ≃ₗ[R] X × Y

  isoX : ∀ x x' : X, ω (e.symm (x, 0)) (e.symm (x', 0)) = 0

  isoY : ∀ y y' : Y, ω (e.symm (0, y)) (e.symm (0, y')) = 0

namespace SympPolarization

variable {ω : LinearMap.BilinForm R W}

end SympPolarization

variable {P₁ P₂ Q₁ Q₂ : Type*} [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
  [AddCommGroup Q₁] [Module R Q₁] [AddCommGroup Q₂] [Module R Q₂]

structure FourPieces (ω : LinearMap.BilinForm R W) (P₁ P₂ Q₁ Q₂ : Type*) [AddCommGroup P₁]
    [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup Q₁] [Module R Q₁]
    [AddCommGroup Q₂] [Module R Q₂] where

  e : W ≃ₗ[R] (P₁ × P₂) × (Q₁ × Q₂)

  a₁ : P₁ →ₗ[R] Q₁ →ₗ[R] R

  a₂ : P₂ →ₗ[R] Q₂ →ₗ[R] R

  form : ∀ w w', ω w w' = a₁ (e w).1.1 (e w').2.1 + a₂ (e w).1.2 (e w').2.2
    - a₁ (e w').1.1 (e w).2.1 - a₂ (e w').1.2 (e w).2.2

section Std

variable (R) in

def stdForm {d : ℕ} (M : Matrix (Fin d) (Fin d) R) :
    LinearMap.BilinForm R ((Fin d → R) × (Fin d → R)) :=
  LinearMap.mk₂ R (fun u v => u.1 ⬝ᵥ (M *ᵥ v.2) - v.1 ⬝ᵥ (M *ᵥ u.2))
    (fun u u' v => by
      simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, mulVec_add, dotProduct_add]; ring)
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, mulVec_smul, dotProduct_smul,
        smul_eq_mul]; ring)
    (fun u v v' => by
      simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, mulVec_add, dotProduct_add]; ring)
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, mulVec_smul, dotProduct_smul,
        smul_eq_mul]; ring)

theorem stdForm_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) R) (u v : (Fin d → R) × (Fin d → R)) :
    stdForm R M u v = u.1 ⬝ᵥ (M *ᵥ v.2) - v.1 ⬝ᵥ (M *ᵥ u.2) := rfl

end Std

end Alg

end GroundTheory.Heights₂.Theta
