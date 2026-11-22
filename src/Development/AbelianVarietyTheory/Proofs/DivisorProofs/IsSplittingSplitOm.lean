import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open Matrix
open scoped NNReal Kronecker

namespace GlobalTheory.WeilM

variable {R : Type} [CommRing R]

theorem schr_schr [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (w w' : (κ → R) × (κ → R))
    (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * (mul_invOf_self (2 : R))

variable (R) in

def swapA : R × R →ₐ[R] R × R := { (RingEquiv.prodComm : R × R ≃+* R × R).toRingHom with commutes' := fun _ => rfl }

@[simp] theorem swapA_apply (x : R × R) : swapA R x = (x.2, x.1) := rfl

variable {α β κ : Type}

def flat (σ : κ ≃ α × β) : Matrix α β R ≃ₗ[R] (κ → R) where
  toFun X k := X (σ k).1 (σ k).2
  invFun u := of fun i j => u (σ.symm (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv X := by ext i j; simp
  right_inv u := by ext k; simp

theorem flat_apply (σ : κ ≃ α × β) (X : Matrix α β R) (k : κ) : flat σ X k = X (σ k).1 (σ k).2 := rfl

theorem flat_symm_apply (σ : κ ≃ α × β) (u : κ → R) (i : α) (j : β) : (flat σ).symm u i j = u (σ.symm (i, j)) := rfl

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

theorem IsHerm.snd_eq {J : Matrix α α (R × R)} (h : IsHerm (swapA R) J) (i j : α) : (J i j).2 = (J j i).1 := by
  have hc := congrArg Prod.snd (h.1 i j)
  rw [swapA_apply] at hc
  exact hc.symm

def splitChar (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) (a : ℕ) : Rˣ →* ℂ where
  toFun t := (χ (Units.map (MonoidHom.inl R R) t) : ℂ) * (((m t : ℝ) ^ (-(a : ℝ) / 2) : ℝ) : ℂ)
  map_one' := by simp
  map_mul' s t := by
    simp only [map_mul, Circle.coe_mul, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _),
      Complex.ofReal_mul]
    ring

end GlobalTheory.WeilM

end
