import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemCentIffTwConj

open Matrix

noncomputable section

namespace GlobalTheory.Tw

section Theta
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

def PhiGL (n : ℕ) (R : Type) [CommRing R] : GL (Fin n) R :=
  ⟨Phi n R, (Phi n R)ᵀ, Model.Phi_mul_transpose, Model.transpose_mul_Phi⟩

omit [StarRing R] in
@[simp] theorem PhiGL_val : (PhiGL n R).val = Phi n R := rfl

omit [StarRing R] in
@[simp] theorem PhiGL_inv_val : (PhiGL n R)⁻¹.val = (Phi n R)ᵀ := rfl

omit [StarRing R] in
theorem Phi_inv : (Phi n R)⁻¹ = (Phi n R)ᵀ := Matrix.inv_eq_right_inv Model.Phi_mul_transpose

def thetaGL (g : GL (Fin n) R) : GL (Fin n) R := PhiGL n R * star g⁻¹ * (PhiGL n R)⁻¹

theorem thetaGL_val (g : GL (Fin n) R) : (thetaGL g).val = theta g.val := by
  simp [thetaGL, theta, Matrix.star_eq_conjTranspose, Phi_inv]

theorem thetaGL_thetaGL (g : GL (Fin n) R) : thetaGL (thetaGL g) = g :=
  Units.ext (by rw [thetaGL_val, thetaGL_val, Model.theta_theta g.isUnit])

theorem thetaGL_mul (g h : GL (Fin n) R) : thetaGL (g * h) = thetaGL g * thetaGL h :=
  Units.ext (by simp only [Units.val_mul, thetaGL_val, Model.theta_mul])

end Theta

structure PFlag (n : ℕ) (k : Type) [CommRing k] where

  carrier : Set (Submodule k (Fin n → k))
  chain : IsChain (· ≤ ·) carrier
  bot_mem : ⊥ ∈ carrier
  top_mem : ⊤ ∈ carrier

namespace PFlag

section Ring
variable {n : ℕ} {k : Type} [CommRing k] (F : PFlag n k)

def pred (V : Submodule k (Fin n → k)) : Submodule k (Fin n → k) := sSup {V' | V' ∈ F.carrier ∧ V' < V}

def lieQ : Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := {X | ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ V}
  add_mem' hX hY V hV v hv := by rw [add_mulVec]; exact V.add_mem (hX V hV v hv) (hY V hV v hv)
  zero_mem' V _ v _ := by simp
  smul_mem' c X hX V hV v hv := by rw [smul_mulVec]; exact V.smul_mem c (hX V hV v hv)

def lieN : Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := {X | ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ F.pred V}
  add_mem' hX hY V hV v hv := by rw [add_mulVec]; exact (F.pred V).add_mem (hX V hV v hv) (hY V hV v hv)
  zero_mem' V _ v _ := by simp
  smul_mem' c X hX V hV v hv := by rw [smul_mulVec]; exact (F.pred V).smul_mem c (hX V hV v hv)

variable {F}

theorem mem_lieN {X : Matrix (Fin n) (Fin n) k} : X ∈ F.lieN ↔ ∀ V ∈ F.carrier, ∀ v ∈ V, X *ᵥ v ∈ F.pred V := Iff.rfl

variable (F)

variable {F}

end Ring

end PFlag

end GlobalTheory.Tw
