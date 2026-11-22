import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

noncomputable section
namespace GlobalTheory.UCls
open scoped TensorProduct
open IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem isKM_mul {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hk' : IsKM c G L M k') :
    IsKM c G L M (k * k') := by
  obtain ⟨⟨hd, hh⟩, h2, h3⟩ := hk
  obtain ⟨⟨hd', hh'⟩, h2', h3'⟩ := hk'
  refine ⟨⟨by rw [det_mul]; exact hd.mul hd', fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hh, hh']
  · obtain ⟨y2, hy2, e2⟩ := h2' x hx
    have hx' : k' *ᵥ x ∈ hat F L := by
      have : k' *ᵥ x = x + M • y2 := by rw [← e2]; abel
      rw [this]; exact add_mem hx (nsmul_mem hy2 _)
    obtain ⟨y1, hy1, e1⟩ := h2 _ hx'
    refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e1, ← e2]; abel
  · obtain ⟨y1, hy1, e1⟩ := h3 x hx
    obtain ⟨y2, hy2, e2⟩ := h3' y1 hy1
    exact ⟨y2, hy2, by rw [← mulVec_mulVec, e2, e1]⟩

theorem isKM_inv {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)} {M : ℕ}
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) :
    IsKM c G L M k⁻¹ := by
  obtain ⟨⟨hd, hh⟩, h2, h3⟩ := hk
  have hkk : k * k⁻¹ = 1 := mul_nonsing_inv k hd
  have hkk' : k⁻¹ * k = 1 := nonsing_inv_mul k hd
  have hmem : ∀ x ∈ hat F L, k *ᵥ x ∈ hat F L := by
    intro x hx
    obtain ⟨y, hy, e⟩ := h2 x hx
    have : k *ᵥ x = x + M • y := by rw [← e]; abel
    rw [this]; exact add_mem hx (nsmul_mem hy _)
  refine ⟨⟨?_, fun x y => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · rw [det_nonsing_inv]; exact hd.ringInverse
  · rw [← hh, mulVec_mulVec, mulVec_mulVec, hkk, one_mulVec, one_mulVec]
  · obtain ⟨y, hy, e⟩ := h3 x hx
    obtain ⟨z, hz, ez⟩ := h2 y hy
    refine ⟨-z, neg_mem hz, ?_⟩
    have : k⁻¹ *ᵥ x = y := by rw [← e, mulVec_mulVec, hkk', one_mulVec]
    rw [this, ← e, smul_neg, ← ez]; abel
  · exact ⟨k *ᵥ x, hmem x hx, by rw [mulVec_mulVec, hkk', one_mulVec]⟩

end GlobalTheory.UCls
end
