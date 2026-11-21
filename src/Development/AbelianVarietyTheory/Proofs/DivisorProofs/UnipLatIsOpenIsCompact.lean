import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.StatementE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGUIffAdjJ
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG

namespace GlobalTheory.BorelUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ball_eq_image {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    {x : L | Valued.v x ≤ WithZero.exp (-k)} = (fun x => ϖ ^ k * x) '' {x : L | Valued.v x ≤ 1} := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hk : Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp
  ext x
  constructor
  · intro hx
    refine ⟨(ϖ ^ k)⁻¹ * x, ?_, by field_simp⟩
    show Valued.v ((ϖ ^ k)⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, hk]
    exact (inv_mul_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero)).2 hx
  · rintro ⟨y, hy, rfl⟩
    show Valued.v (ϖ ^ k * y) ≤ WithZero.exp (-k)
    rw [map_mul, hk]
    exact (mul_le_mul' le_rfl hy).trans (by rw [mul_one])

theorem isOpen_vball {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    IsOpen {x : L | Valued.v x ≤ WithZero.exp (-k)} := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  rw [ball_eq_image hϖ]
  exact (Homeomorph.mulLeft₀ (ϖ ^ k) (zpow_ne_zero k h0)).isOpenMap _ (Valued.isOpen_integer L)

theorem isCompact_vball [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (k : ℤ) :
    IsCompact {x : L | Valued.v x ≤ WithZero.exp (-k)} := by
  obtain ⟨-, hv, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := L)).2 ⟨(Valued.isClosed_integer L).completeSpace_coe,
      (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (by
        refine ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  rw [ball_eq_image hϖ]
  exact (isCompact_iff_compactSpace.2 hp).image (continuous_const.mul continuous_id)

end GlobalTheory.BorelUMod
