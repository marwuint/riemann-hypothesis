import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.SepModel

theorem tmul_mem_cenOrder {F : Type} [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] {N : ℕ}
    (hN : ¬ ℓ ∣ N) {c : F} (hc : IsIntegral ℤ ((N : F) * c)) :
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c ∈ cenOrder ℓ F := by
  have hu : IsUnit (N : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN
  obtain ⟨u, hu⟩ := hu
  have hmem : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c) ∈ cenOrder ℓ F :=
    Algebra.subset_adjoin ⟨⟨_, hc⟩, rfl⟩
  have heq : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c = (↑u⁻¹ : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c)) := by
    have h1 : (u : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] c) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((N : F) * c) := by
      rw [hu, Nat.cast_smul_eq_nsmul, ← TensorProduct.tmul_smul, nsmul_eq_mul]
    rw [← h1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [heq]
  exact Subalgebra.smul_mem _ hmem _

theorem exists_nat_integral {F : Type} [Field F] [NumberField F] (s : Finset F) :
    ∃ N : ℕ, 0 < N ∧ ∀ c ∈ s, IsIntegral ℤ ((N : F) * c) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := F) s
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun c hc => ?_⟩
  have h := hy c hc
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e] at h; simpa using h
  · rw [e] at h
    have := h.neg
    simpa [neg_mul] using this

end GlobalTheory.SepModel

namespace GlobalTheory.SepModel

end GlobalTheory.SepModel
