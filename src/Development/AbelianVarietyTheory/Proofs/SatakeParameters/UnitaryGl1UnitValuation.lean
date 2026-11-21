import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

noncomputable section
namespace GlobalTheory.Hk3.LatModel
open Classical

section Concrete
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_two {ϖ : L} {σ : L →+* L} {q : ℕ} (h : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) : Valued.v (2 : L) = 1 := by
  obtain ⟨-, -, -, -, -, h2, hc⟩ := h
  by_contra hne
  have hle : Valued.v (2 : L) ≤ 1 := by
    have := (Valued.v (R := L)).integer.add_mem (one_mem _) (one_mem _)
    rw [one_add_one_eq_two] at this; exact this
  have hlt := lt_of_le_of_ne hle hne
  set R := (Valued.v (R := L)).valuationSubring
  change Nat.card (R ⧸ IsLocalRing.maximalIdeal R) = q ^ 2 at hc
  have hm : (2 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [Valuation.mem_maximalIdeal_iff]; exact hlt
  have h20 : (2 : R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rwa [map_ofNat] at this
  have hodd : Odd (Nat.card (R ⧸ IsLocalRing.maximalIdeal R)) := by rw [hc]; exact hq.pow
  obtain ⟨k, hk⟩ := hodd
  have h3 : ((Nat.card (R ⧸ IsLocalRing.maximalIdeal R) : ℕ) : R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
    rw [← nsmul_one]; exact card_nsmul_eq_zero'
  rw [hk] at h3
  push_cast at h3
  rw [h20] at h3
  simp at h3

end Concrete

end GlobalTheory.Hk3.LatModel
end
