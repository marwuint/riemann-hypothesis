import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate

noncomputable section
namespace GlobalTheory.UCls.KGrp
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem isUA_mul (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) {g h : Matrix (Fin n) (Fin n) (RA F E)}
    (hg : IsUA c G g) (hh : IsUA c G h) : IsUA c G (g * h) :=
  ⟨by rw [det_mul]; exact hg.1.mul hh.1, fun x y => by rw [← mulVec_mulVec, ← mulVec_mulVec, hg.2, hh.2]⟩

theorem isUA_inv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) {g : Matrix (Fin n) (Fin n) (RA F E)}
    (hg : IsUA c G g) : IsUA c G g⁻¹ := by
  refine ⟨isUnit_nonsing_inv_det g hg.1, fun x y => ?_⟩
  rw [← hg.2, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv g hg.1, one_mulVec, one_mulVec]

theorem isKM_mul (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hk' : IsKM c G L M k') :
    IsKM c G L M (k * k') := by
  refine ⟨isUA_mul c G hk.1 hk'.1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y', hy', e'⟩ := hk'.2.1 x hx
    have hkx : k' *ᵥ x ∈ hat F L := by
      have : k' *ᵥ x = x + M • y' := by rw [← e']; abel
      rw [this]; exact add_mem hx (nsmul_mem hy' M)
    obtain ⟨y, hy, e⟩ := hk.2.1 _ hkx
    refine ⟨y + y', add_mem hy hy', ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e, ← e']; abel
  · obtain ⟨y, hy, e⟩ := hk.2.2 x hx
    obtain ⟨z, hz, e'⟩ := hk'.2.2 y hy
    exact ⟨z, hz, by rw [← mulVec_mulVec, e', e]⟩

theorem isKM_inv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) : IsKM c G L M k⁻¹ := by
  have h1 : k * k⁻¹ = 1 := mul_nonsing_inv k hk.1.1
  have h2 : k⁻¹ * k = 1 := nonsing_inv_mul k hk.1.1
  refine ⟨isUA_inv c G hk.1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hk.2.2 x hx
    obtain ⟨z, hz, e⟩ := hk.2.1 y hy
    refine ⟨-z, neg_mem hz, ?_⟩
    rw [mulVec_mulVec, h2, one_mulVec, smul_neg, ← e]; abel
  · obtain ⟨z, hz, e⟩ := hk.2.1 x hx
    refine ⟨k *ᵥ x, ?_, by rw [mulVec_mulVec, h2, one_mulVec]⟩
    have : k *ᵥ x = x + M • z := by rw [← e]; abel
    rw [this]; exact add_mem hx (nsmul_mem hz M)

end GlobalTheory.UCls.KGrp
