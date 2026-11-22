import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulOfIsPrimitiveIntegralHahnGauss
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaDerivationHahnSeriesLeibnizAddConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLogDerivQExpansionModPrimePowOfTranslation
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue

noncomputable section
namespace GlobalTheory.UlCusp

variable {Ω : Type} [Field Ω]

theorem eOm_spec [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  obtain ⟨ζ, hζ⟩ := Api.exists_root_of_isAlgClosed ε x.den_pos
  have h : ∃ a, ε a = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
    refine ⟨ζ ^ x.num, ?_⟩
    rw [map_zpow₀, hζ, ← Complex.exp_int_mul]
    congr 1
    conv_rhs => rw [← Rat.num_div_den x]
    push_cast; ring
  exact Function.invFun_eq h

theorem eOm_add [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x y : ℚ) : eOm ε (x + y) = eOm ε x * eOm ε y := by
  apply Api.eOm_eq_of
  rw [map_mul, eOm_spec, eOm_spec, ← Complex.exp_add]; congr 1; push_cast; ring

theorem eOm_intCast [IsAlgClosed Ω] (ε : Ω →+* ℂ) (m : ℤ) : eOm ε (m : ℚ) = 1 := by
  apply Api.eOm_eq_of
  rw [map_one]
  have := Complex.exp_int_mul_two_pi_mul_I m
  rw [← this]; congr 1; push_cast; ring

theorem eOm_zero [IsAlgClosed Ω] (ε : Ω →+* ℂ) : eOm ε 0 = 1 := by
  simpa using eOm_intCast ε 0

theorem eOm_nsmul [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) (k : ℕ) : eOm ε (k * x) = eOm ε x ^ k := by
  induction k with
  | zero => simpa using eOm_zero ε
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, eOm_add, ih, pow_succ]

theorem eOm_pow_den [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) : eOm ε x ^ x.den = 1 := by
  rw [← eOm_nsmul]
  have : (x.den : ℚ) * x = (x.num : ℚ) := by
    have := Rat.mul_den_eq_num x; rw [mul_comm]; exact this
  rw [this, eOm_intCast]

theorem eOm_mem [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (x : ℚ) : eOm ε x ∈ A := by
  rcases A.mem_or_inv_mem (eOm ε x) with h | h
  · exact h
  · have hd := eOm_pow_den ε x
    have h0 : eOm ε x ≠ 0 := by rintro h0; rw [h0, zero_pow x.den_pos.ne'] at hd; exact zero_ne_one hd
    have : eOm ε x = (eOm ε x)⁻¹ ^ (x.den - 1) := by
      rw [inv_pow]; exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ', Nat.sub_add_cancel x.den_pos, hd])
    rw [this]; exact pow_mem h _

theorem eOm_inv_mem [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (x : ℚ) : (eOm ε x)⁻¹ ∈ A := by
  have : (eOm ε x)⁻¹ = eOm ε (-x) := by
    exact inv_eq_of_mul_eq_one_right (by rw [← eOm_add, add_neg_cancel, eOm_zero])
  rw [this]; exact eOm_mem ε A _

end GlobalTheory.UlCusp

noncomputable section
namespace GlobalTheory.UlCusp

end GlobalTheory.UlCusp

noncomputable section
namespace GlobalTheory.UlCusp

end GlobalTheory.UlCusp

noncomputable section
namespace GlobalTheory.UlCusp

end GlobalTheory.UlCusp

noncomputable section
namespace GlobalTheory.UlCusp

end GlobalTheory.UlCusp

noncomputable section
namespace GlobalTheory.UlCusp

end GlobalTheory.UlCusp

namespace GlobalTheory.UlCusp

end GlobalTheory.UlCusp

