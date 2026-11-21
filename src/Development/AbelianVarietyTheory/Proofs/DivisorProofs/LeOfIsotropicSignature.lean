import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilAnisotropic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.ThetaInner
open scoped InnerProductSpace
open Matrix

namespace GlobalTheory.WittSignature

open scoped ComplexOrder in

theorem le_of_isotropic_standard {p q k : ℕ} (N : Matrix (Fin p ⊕ Fin q) (Fin k) ℂ) (L : Matrix (Fin k) (Fin p ⊕ Fin q) ℂ)
    (hL : L * N = 1) (h : Nᴴ * Formalism.UG.Jpq p q * N = 0) : k ≤ p ∧ k ≤ q := by
  have key : ∀ v : Fin k → ℂ, star ((N *ᵥ v) ∘ Sum.inl) ⬝ᵥ ((N *ᵥ v) ∘ Sum.inl) =
      star ((N *ᵥ v) ∘ Sum.inr) ⬝ᵥ ((N *ᵥ v) ∘ Sum.inr) := by
    intro v
    have h1 : star (N *ᵥ v) ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ (N *ᵥ v)) = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
      simp
    generalize N *ᵥ v = x at h1 ⊢
    rw [Formalism.UG.Jpq, Matrix.fromBlocks_mulVec] at h1
    simp only [dotProduct, Fintype.sum_sum_type, Matrix.one_mulVec, Matrix.zero_mulVec, Matrix.neg_mulVec, add_zero, zero_add,
      Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at h1
    simp only [dotProduct]
    exact add_neg_eq_zero.1 h1
  have inj : ∀ v : Fin k → ℂ, (N *ᵥ v) ∘ Sum.inl = 0 → (N *ᵥ v) ∘ Sum.inr = 0 → v = 0 := by
    intro v h1 h2
    have h3 : N *ᵥ v = 0 := by
      funext i
      rcases i with i | i
      · exact congrFun h1 i
      · exact congrFun h2 i
    have : (L * N) *ᵥ v = 0 := by rw [← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]
    simpa [hL] using this
  constructor
  · have hf : Function.Injective ((LinearMap.funLeft ℂ ℂ (Sum.inl : Fin p → Fin p ⊕ Fin q)).comp N.mulVecLin) := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : (N *ᵥ v) ∘ Sum.inl = 0 := hv
      have h2 := key v
      rw [h1, dotProduct_zero] at h2
      exact inj v h1 (dotProduct_star_self_eq_zero.1 h2.symm)
    simpa using LinearMap.finrank_le_finrank_of_injective hf
  · have hf : Function.Injective ((LinearMap.funLeft ℂ ℂ (Sum.inr : Fin q → Fin p ⊕ Fin q)).comp N.mulVecLin) := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : (N *ᵥ v) ∘ Sum.inr = 0 := hv
      have h2 := key v
      rw [h1, dotProduct_zero] at h2
      exact inj v (dotProduct_star_self_eq_zero.1 h2) h1
    simpa using LinearMap.finrank_le_finrank_of_injective hf

theorem le_of_isotropic_signature {n p q k : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (hJ : Formalism.UG.HasSignature J p q)
    (M : Matrix (Fin n) (Fin k) ℂ) (L : Matrix (Fin k) (Fin n) ℂ)
    (hL : L * M = 1) (h : Mᴴ * J * M = 0) : k ≤ p ∧ k ≤ q := by
  obtain ⟨e, P, hP⟩ := hJ
  have hP' : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * J.submatrix e.symm e.symm *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hP
  have hPP : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * (P⁻¹ : GL _ ℂ) = 1 := P.mul_inv
  have hN : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ).val * M.submatrix e.symm id) = M.submatrix e.symm id := by
    rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
  refine le_of_isotropic_standard ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ).val * M.submatrix e.symm id) (L.submatrix id e.symm * P.val) ?_ ?_
  · rw [Matrix.mul_assoc, hN, Matrix.submatrix_mul_equiv, hL, Matrix.submatrix_id_id]
  · rw [← hP']
    generalize ((P⁻¹ : GL _ ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * M.submatrix e.symm id = N at hN ⊢
    calc _ = ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * N)ᴴ * J.submatrix e.symm e.symm *
          ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * N) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by
          rw [hN, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h]
          rfl

end GlobalTheory.WittSignature
