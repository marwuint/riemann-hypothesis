import Mathlib
import GroundTheory.PAdicHodge.BCrisTensorK
set_option maxSynthPendingDepth 1

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GroundTheory.PAdicHodge

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

local notation "K₀" => maxUnramified p K

section Frob

variable [FiniteDimensional ℚ_[p] K]

instance finiteDimensional_padic_maxUnramified : FiniteDimensional ℚ_[p] K₀ :=
  FiniteDimensional.of_injective
    (IntermediateField.inclusion (inf_le_left : maxUnramified p K ≤ K)).toLinearMap
    (IntermediateField.inclusion (inf_le_left : maxUnramified p K ≤ K)).injective

end Frob

section Valuation

variable {K}

theorem exists_norm_eq_zpow_maxUnramified {x : K₀} (hx : x ≠ 0) :
    ∃ D : ℤ, ‖(x : PadicAlgCl p)‖ = ‖(p : PadicAlgCl p)‖ ^ D :=
  (isACrisFraction_of_mem (mem_maxUnramified.1 x.2).2).exists_norm_eq_zpow
    (by simpa using hx)

theorem norm_p_algCl_pos : 0 < ‖(p : PadicAlgCl p)‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)

theorem zpow_norm_p_injective : Function.Injective fun D : ℤ => ‖(p : PadicAlgCl p)‖ ^ D :=
  zpow_right_injective₀ norm_p_algCl_pos (norm_p_algCl_lt_one (p := p)).ne

open Classical in

def maxUnramifiedValFun (x : K₀) : WithTop ℤ :=
  if hx : x = 0 then ⊤ else ((exists_norm_eq_zpow_maxUnramified hx).choose : ℤ)

theorem maxUnramifiedValFun_zero : maxUnramifiedValFun (0 : K₀) = ⊤ := by
  classical
  rw [maxUnramifiedValFun, dif_pos rfl]

theorem maxUnramifiedValFun_eq {x : K₀} (hx : x ≠ 0) {D : ℤ} (h : ‖(x : PadicAlgCl p)‖ = ‖(p : PadicAlgCl p)‖ ^ D) :
    maxUnramifiedValFun x = D := by
  classical
  rw [maxUnramifiedValFun, dif_neg hx]
  congr 1
  exact zpow_norm_p_injective ((exists_norm_eq_zpow_maxUnramified hx).choose_spec.symm.trans h)

theorem maxUnramifiedValFun_add_le (x y : K₀) : min (maxUnramifiedValFun x) (maxUnramifiedValFun y) ≤ maxUnramifiedValFun (x + y) := by
  by_cases hx : x = 0
  · rw [hx, zero_add, maxUnramifiedValFun_zero]; exact min_le_right _ _
  by_cases hy : y = 0
  · rw [hy, add_zero, maxUnramifiedValFun_zero]; exact min_le_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy, maxUnramifiedValFun_zero]; exact le_top
  obtain ⟨D, hD⟩ := exists_norm_eq_zpow_maxUnramified hx
  obtain ⟨E, hE⟩ := exists_norm_eq_zpow_maxUnramified hy
  obtain ⟨F, hF⟩ := exists_norm_eq_zpow_maxUnramified hxy
  rw [maxUnramifiedValFun_eq hx hD, maxUnramifiedValFun_eq hy hE, maxUnramifiedValFun_eq hxy hF, ← WithTop.coe_min, WithTop.coe_le_coe]
  have h := IsUltrametricDist.norm_add_le_max (x : PadicAlgCl p) (y : PadicAlgCl p)
  rw [← IntermediateField.coe_add, hF, hD, hE] at h
  have hp0 := norm_p_algCl_pos (p := p)
  have hp1 := norm_p_algCl_lt_one (p := p)
  rcases le_total D E with hDE | hDE
  · rw [min_eq_left hDE]
    rw [max_eq_left ((zpow_le_zpow_iff_right_of_lt_one₀ hp0 hp1).2 hDE)] at h
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hp0 hp1).1 h
  · rw [min_eq_right hDE]
    rw [max_eq_right ((zpow_le_zpow_iff_right_of_lt_one₀ hp0 hp1).2 hDE)] at h
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hp0 hp1).1 h

theorem maxUnramifiedValFun_mul (x y : K₀) : maxUnramifiedValFun (x * y) = maxUnramifiedValFun x + maxUnramifiedValFun y := by
  by_cases hx : x = 0
  · rw [hx, zero_mul, maxUnramifiedValFun_zero, WithTop.top_add]
  by_cases hy : y = 0
  · rw [hy, mul_zero, maxUnramifiedValFun_zero, WithTop.add_top]
  obtain ⟨D, hD⟩ := exists_norm_eq_zpow_maxUnramified hx
  obtain ⟨E, hE⟩ := exists_norm_eq_zpow_maxUnramified hy
  rw [maxUnramifiedValFun_eq hx hD, maxUnramifiedValFun_eq hy hE, maxUnramifiedValFun_eq (mul_ne_zero hx hy) (D := D + E), ← WithTop.coe_add]
  rw [IntermediateField.coe_mul, norm_mul, hD, hE, zpow_add₀ norm_p_algCl_pos.ne']

theorem maxUnramifiedValFun_one : maxUnramifiedValFun (1 : K₀) = 0 :=
  maxUnramifiedValFun_eq (one_ne_zero : (1 : K₀) ≠ 0) (D := 0) (by simp)

variable (K) in

def maxUnramifiedValuation : AddValuation K₀ (WithTop ℤ) :=
  AddValuation.of maxUnramifiedValFun maxUnramifiedValFun_zero maxUnramifiedValFun_one maxUnramifiedValFun_add_le maxUnramifiedValFun_mul

end Valuation

end ACris

end GroundTheory.PAdicHodge
