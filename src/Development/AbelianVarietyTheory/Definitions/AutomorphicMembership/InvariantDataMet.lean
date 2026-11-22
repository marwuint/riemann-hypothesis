import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CurvNormNonneg

noncomputable section

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open scoped ComplexOrder ContDiff

namespace GlobalTheory.HodgeDomain

variable {ι : Type} [Fintype ι] {p q : ℕ}

def bergman (z : Pt ι p q) : Pt ι p q →ₗ[ℂ] Pt ι p q →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun ξ η => ∑ τ, ((hP (z τ))⁻¹ * ξ τ * (hQ (z τ))⁻¹ * (η τ)ᴴ).trace)
    (fun _ _ _ => by simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])
    (fun _ _ _ => by simp [Matrix.mul_add, Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])

theorem trace_pos {A : Matrix (Fin p) (Fin p) ℂ} {B : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (ξ : Matrix (Fin p) (Fin q) ℂ) : 0 ≤ (A * ξ * B * ξᴴ).trace ∧ (ξ ≠ 0 → 0 < (A * ξ * B * ξᴴ).trace) := by
  open MatrixOrder in
  obtain ⟨R, hR, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hA.isStrictlyPositive
  open MatrixOrder in
  obtain ⟨S, hS, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self.1 hB.isStrictlyPositive
  have e : (star R * R * ξ * (S * star S) * ξᴴ).trace = ((R * ξ * S) * (R * ξ * S)ᴴ).trace := by
    simp only [star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e]
  have h0 := (posSemidef_self_mul_conjTranspose (R * ξ * S)).trace_nonneg
  refine ⟨h0, fun hξ => lt_of_le_of_ne h0 fun h => hξ ?_⟩
  have h1 := trace_mul_conjTranspose_self_eq_zero_iff.1 h.symm
  have hR' := (isUnit_iff_isUnit_det _).1 hR
  have hS' := (isUnit_iff_isUnit_det _).1 hS
  have : R⁻¹ * (R * ξ * S) * S⁻¹ = ξ := by
    rw [Matrix.mul_assoc R, nonsing_inv_mul_cancel_left _ _ hR', mul_nonsing_inv_cancel_right _ _ hS']
  rw [← this, h1]; simp

end GlobalTheory.HodgeDomain
