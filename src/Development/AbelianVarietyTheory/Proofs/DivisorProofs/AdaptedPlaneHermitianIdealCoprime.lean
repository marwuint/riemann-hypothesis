import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors Matrix TensorProduct

namespace GlobalTheory.AdaptedPlaneIdeal

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_hasSig {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (φ : E →+* ℂ)
    (h : HasSig (J.map φ) r s) : J.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  intro h0
  have hM : (J.map φ).det = 0 := by
    have := RingHom.map_det φ J
    rw [h0, map_zero] at this
    exact this.symm
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hM
  have hD : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]; simp [Matrix.det_neg]
  have h1 := Matrix.rank_of_isUnit _ hD
  rw [← hA] at h1
  have h2 : (Aᵀ * J.map φ * A.map star).rank ≤ (J.map φ).rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have h3 := LinearMap.finrank_range_add_finrank_ker (J.map φ).mulVecLin
  have h4 : 0 < Module.finrank ℂ (LinearMap.ker (J.map φ).mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun e => hv0 (congrArg Subtype.val e)⟩
  rw [Module.finrank_fin_fun] at h3
  have h5 : (J.map φ).rank = Module.finrank ℂ (LinearMap.range (J.map φ).mulVecLin) := rfl
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
  omega

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

end GlobalTheory.AdaptedPlaneIdeal
