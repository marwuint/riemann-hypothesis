import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.HermFrame.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}

theorem blockSS_eq (K T : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    blockSS K T = T.toBlocks₁₁ + orthCoeff K * T.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks T]
  simp [blockSS, orthProj, incl, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

theorem blockQQ_eq (K T : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    blockQQ K T = T.toBlocks₂₂ - T.toBlocks₂₁ * orthCoeff K := by
  conv_lhs => rw [← fromBlocks_toBlocks T]
  simp [blockQQ, quotMap, orthLift, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  abel

theorem conn_sub (hu : IsUnit (H z).det) (hs : IsUnit (subGram (H z)).det) (ξ : E) :
    conn (fun x => subGram (H x)) z ξ = blockSS (H z) (conn H z ξ) := by
  have h := transpose_mul_conn hu ξ
  rw [← fromBlocks_toBlocks (H z)ᵀ, ← fromBlocks_toBlocks (conn H z ξ), fromBlocks_multiply] at h
  have h1 := congrArg toBlocks₁₁ h
  rw [toBlocks_fromBlocks₁₁] at h1
  have hs' : IsUnit (H z).toBlocks₁₁ᵀ.det := by rwa [det_transpose]
  rw [blockSS_eq, conn,
    show (mdel (fun x => subGram (H x)) z ξ)ᵀ = (mdel H z ξ)ᵀ.toBlocks₁₁ from rfl, ← h1,
    show (H z)ᵀ.toBlocks₁₁ = (H z).toBlocks₁₁ᵀ from rfl,
    show (H z)ᵀ.toBlocks₁₂ = (H z).toBlocks₂₁ᵀ from rfl, subGram, Matrix.mul_add,
    nonsing_inv_mul_cancel_left _ _ hs', orthCoeff, Matrix.mul_assoc]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype l] [DecidableEq l] in

theorem mContDiffAt_orthCoeff {k : WithTop ℕ∞} (h : MContDiffAt k H z)
    (hs : IsUnit (subGram (H z)).det) : MContDiffAt k (fun x => orthCoeff (H x)) z :=
  (h.subGram.transpose.inv (by rwa [det_transpose])).mul (h.submatrix Sum.inr Sum.inl).transpose

theorem conn_quot (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (ξ : E) :
    conn (fun x => quotGram (H x)) z ξ = blockQQ (H z) (conn H z ξ) := by
  refine (eq_conn_of_compatible (H := fun x => quotGram (H x))
    (isUnit_det_quotGram hu hs) ?_).symm
  have hA : MContDiffAt 1 (fun x => (H x).toBlocks₁₁) z := h.subGram
  have hB : MContDiffAt 1 (fun x => (H x).toBlocks₁₂) z := h.submatrix Sum.inl Sum.inr
  have hC : MContDiffAt 1 (fun x => (H x).toBlocks₂₁) z := h.submatrix Sum.inr Sum.inl
  have hD : MContDiffAt 1 (fun x => (H x).toBlocks₂₂) z := h.submatrix Sum.inr Sum.inr
  have hs' : IsUnit (H z).toBlocks₁₁.det := hs
  have e := conn_transpose_mul hu ξ
  rw [← fromBlocks_toBlocks (conn H z ξ)ᵀ, ← fromBlocks_toBlocks (H z), fromBlocks_multiply] at e
  have e11 := congrArg toBlocks₁₁ e
  have e12 := congrArg toBlocks₁₂ e
  have e21 := congrArg toBlocks₂₁ e
  have e22 := congrArg toBlocks₂₂ e
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂] at e11 e12 e21 e22
  simp only [quotGram, sub_eq_add_neg]
  rw [mdel_add hD ((hC.mul (hA.inv hs')).mul hB).neg, mdel_neg, mdel_mul (hC.mul (hA.inv hs')) hB,
    mdel_mul hC (hA.inv hs'), mdel_inv hA hs',
    show mdel (fun x => (H x).toBlocks₁₁) z ξ = (mdel H z ξ).toBlocks₁₁ from rfl,
    show mdel (fun x => (H x).toBlocks₁₂) z ξ = (mdel H z ξ).toBlocks₁₂ from rfl,
    show mdel (fun x => (H x).toBlocks₂₁) z ξ = (mdel H z ξ).toBlocks₂₁ from rfl,
    show mdel (fun x => (H x).toBlocks₂₂) z ξ = (mdel H z ξ).toBlocks₂₂ from rfl,
    ← e11, ← e12, ← e21, ← e22, blockQQ_eq, transpose_sub, transpose_mul, orthCoeff, transpose_mul,
    transpose_transpose, transpose_nonsing_inv, transpose_transpose,
    show (conn H z ξ).toBlocks₂₂ᵀ = (conn H z ξ)ᵀ.toBlocks₂₂ from rfl,
    show (conn H z ξ).toBlocks₂₁ᵀ = (conn H z ξ)ᵀ.toBlocks₁₂ from rfl]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hs']
  abel

end GlobalTheory.HermFrame.Model
