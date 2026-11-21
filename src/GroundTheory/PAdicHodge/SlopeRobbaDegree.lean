import Mathlib
import GroundTheory.PAdicHodge.SlopeFrobenius
import GroundTheory.PAdicHodge.SlopePhiSub
import GroundTheory.PAdicHodge.SlopeCauchyBinet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent Module

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)]

variable (K) in

def dvUnif : K := ((IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose : K)

theorem irreducible_dvUnif :
    Irreducible (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose :=
  (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose_spec

theorem norm_eq_one_of_isUnit {z : normInteger K} (hz : IsUnit z) : ‖(z : K)‖ = 1 := by
  have := (normInteger_integers (K := K)).isUnit_iff_valuation_eq_one.1 hz
  rw [NormedField.valuation_apply, ← NNReal.coe_eq_one] at this
  exact this

theorem dvUnif_ne_zero : dvUnif K ≠ 0 := by
  intro h
  have := (irreducible_dvUnif (K := K)).ne_zero
  exact this (Subtype.ext h)

theorem norm_dvUnif_pos : 0 < ‖dvUnif K‖ := norm_pos_iff.2 dvUnif_ne_zero

theorem norm_dvUnif_lt_one : ‖dvUnif K‖ < 1 := by
  have h1 : ‖dvUnif K‖ ≤ 1 := mem_normInteger.1
    (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose.2
  refine lt_of_le_of_ne h1 fun h => (irreducible_dvUnif (K := K)).not_isUnit ?_
  rw [(normInteger_integers (K := K)).isUnit_iff_valuation_eq_one, NormedField.valuation_apply,
    ← NNReal.coe_eq_one]
  exact h

theorem exists_norm_eq_zpow {x : K} (hx : x ≠ 0) : ∃ n : ℤ, ‖x‖ = ‖dvUnif K‖ ^ n := by
  have key : ∀ y : K, y ≠ 0 → ‖y‖ ≤ 1 → ∃ n : ℕ, ‖y‖ = ‖dvUnif K‖ ^ n := by
    intro y hy hy1
    let z : normInteger K := ⟨y, mem_normInteger.2 hy1⟩
    have hz : z ≠ 0 := fun h => hy (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz irreducible_dvUnif
    refine ⟨n, ?_⟩
    have h2 := congrArg (fun w : normInteger K => (w : K)) hu
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow] at h2
    rw [show y = (z : K) from rfl, h2, norm_mul, norm_pow, norm_eq_one_of_isUnit u.isUnit, one_mul]
    rfl
  rcases le_total ‖x‖ 1 with h | h
  · obtain ⟨n, hn⟩ := key x hx h
    exact ⟨n, by rw [hn, zpow_natCast]⟩
  · obtain ⟨n, hn⟩ := key x⁻¹ (inv_ne_zero hx) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h)
    refine ⟨-(n : ℤ), ?_⟩
    rw [norm_inv] at hn
    rw [zpow_neg, zpow_natCast, ← hn, inv_inv]

theorem zpow_dvUnif_injective : Function.Injective fun n : ℤ => ‖dvUnif K‖ ^ n :=
  (zpow_right_strictAnti₀ norm_dvUnif_pos norm_dvUnif_lt_one).injective

namespace Robba

def intBounded (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    Subring (Robba K) where
  carrier := {f | f ∈ bounded K ∧ norm1 f ≤ 1}
  mul_mem' {f g} hf hg := ⟨(bounded K).mul_mem hf.1 hg.1, by
    rw [gaussNorm_mul_alt hf.1 hg.1]; nlinarith [gaussNorm_nonneg_alt f, gaussNorm_nonneg_alt g, hf.2, hg.2]⟩
  one_mem' := ⟨(bounded K).one_mem, by
    refine ciSup_le fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]⟩
  add_mem' {f g} hf hg := ⟨(bounded K).add_mem hf.1 hg.1,
    (gaussNorm_add_le_max_alt hf.1 hg.1).trans (max_le hf.2 hg.2)⟩
  zero_mem' := ⟨(bounded K).zero_mem, by simp [norm1]⟩
  neg_mem' {f} hf := ⟨(bounded K).neg_mem hf.1, by simpa [norm1] using hf.2⟩

theorem mem_intBounded {f : Robba K} : f ∈ intBounded K ↔ f ∈ bounded K ∧ norm1 f ≤ 1 := Iff.rfl

theorem unit_mem_bounded (u : (Robba K)ˣ) : (u : Robba K) ∈ bounded K :=
  mem_bounded_of_mul_eq_one u.mul_inv

theorem unit_ne_zero (u : (Robba K)ˣ) : (u : Robba K) ≠ 0 := u.ne_zero

theorem gaussNorm_unit_pos (u : (Robba K)ˣ) : 0 < norm1 (u : Robba K) :=
  lt_of_le_of_ne (gaussNorm_nonneg_alt _) fun h =>
    unit_ne_zero u ((gaussNorm_eq_zero_iff_alt (unit_mem_bounded u)).1 h.symm)

theorem exists_norm1_eq_zpow (u : (Robba K)ˣ) : ∃ n : ℤ, norm1 (u : Robba K) = ‖dvUnif K‖ ^ n := by
  obtain ⟨m, hm⟩ := exists_norm1_eq (unit_mem_bounded u)
  have hne : (u : Robba K).coeff m ≠ 0 := by
    intro h
    rw [h, norm_zero] at hm
    exact (gaussNorm_unit_pos u).ne' hm
  obtain ⟨n, hn⟩ := exists_norm_eq_zpow hne
  exact ⟨n, hm.trans hn⟩

def ord (u : (Robba K)ˣ) : ℤ := (exists_norm1_eq_zpow u).choose

theorem gaussNorm_eq_zpow_ord (u : (Robba K)ˣ) : norm1 (u : Robba K) = ‖dvUnif K‖ ^ ord u :=
  (exists_norm1_eq_zpow u).choose_spec

theorem ord_eq_of_norm1_eq {u : (Robba K)ˣ} {n : ℤ} (h : norm1 (u : Robba K) = ‖dvUnif K‖ ^ n) :
    ord u = n :=
  zpow_dvUnif_injective ((gaussNorm_eq_zpow_ord u).symm.trans h)

theorem ord_mul (u w : (Robba K)ˣ) : ord (u * w) = ord u + ord w := by
  apply ord_eq_of_norm1_eq
  rw [Units.val_mul, gaussNorm_mul_alt (unit_mem_bounded u) (unit_mem_bounded w), gaussNorm_eq_zpow_ord,
    gaussNorm_eq_zpow_ord, zpow_add₀ norm_dvUnif_pos.ne']

def unitOrd (ψ : Robba K →+* Robba K)
    (hψ : ∀ u : (Robba K)ˣ, norm1 (ψ u) = norm1 (u : Robba K)) : PhiModule.UnitOrd (Robba K) ψ where
  ord := ord
  map_mul := ord_mul
  map_phi u := ord_eq_of_norm1_eq (by
    change norm1 (ψ (u : Robba K)) = _
    rw [hψ, gaussNorm_eq_zpow_ord])

end Robba

namespace Robba

end Robba

namespace PhiModule

end PhiModule

end GroundTheory.PAdicHodge
