import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates

noncomputable section

open Matrix Finset
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.RealHermitianForms

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

section Form

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_add_r (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  unfold hJ; rw [mulVec_add, dotProduct_add]

theorem hJ_smul_r (c : ℂ) (x y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  unfold hJ; rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_uj (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) : hJ ε (uMat g *ᵥ x) (uMat g *ᵥ y) = hJ ε x y := by
  have hg : Formalism.REAL.inUJ ε (uMat g) := g.2
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  unfold Formalism.REAL.inUJ at hg
  rw [hg]

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  simp [uMat]

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem hJ_inv_r (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε x (uMat g⁻¹ *ᵥ y) = hJ ε (uMat g *ᵥ x) y := by
  rw [← hJ_uj ε g x (uMat g⁻¹ *ᵥ y), mulVec_mulVec, uMat_mul_inv, one_mulVec]

end Form

section Eich

variable {n : ℕ} (ε : Fin n → Bool)

def eichL (u w : Fin n → ℂ) (κ : ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun x := x + hJ ε w x • u - hJ ε u x • w + (κ * hJ ε u x) • u
  map_add' x y := by
    simp only [hJ_add_r, add_smul, mul_add]
    abel
  map_smul' c x := by
    simp only [hJ_smul_r, RingHom.id_apply]
    module

theorem eichL_apply (u w : Fin n → ℂ) (κ : ℂ) (x : Fin n → ℂ) :
    eichL ε u w κ x = x + hJ ε w x • u - hJ ε u x • w + (κ * hJ ε u x) • u := rfl

end Eich

end Formalism.L2.SG.RealObj.InfCut.RealHermitianForms
