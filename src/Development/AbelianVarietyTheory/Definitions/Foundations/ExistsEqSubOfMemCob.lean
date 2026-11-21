import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ValuationIntCastLtOneIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.LambdaValuationPowers

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def lamv (l : ℕ) [Fact l.Prime] (m : ℕ) (s : G ℚ Ω) : Qbar l :=
  algebraMap ℚ_[l] (Qbar l) ((((cycZ (F := ℚ) (Ω := Ω) l s : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) - 1) / (l : Qbar l) ^ m

theorem natCast_ne_zero : (l : Qbar l) ≠ 0 := by
  have : CharZero (Qbar l) := charZero_of_injective_algebraMap (algebraMap ℚ_[l] (Qbar l)).injective
  exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

theorem norm_natCast_lt_one : ‖(l : Qbar l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem pow_mul_lamv (m : ℕ) (s : G ℚ Ω) :
    (l : Qbar l) ^ m * lamv l m s = algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
  rw [lamv, mul_div_cancel₀ _ (pow_ne_zero m natCast_ne_zero), map_sub, map_one]

@[simp] theorem lamv_one (m : ℕ) : lamv l m (1 : G ℚ Ω) = 0 := by
  simp [lamv]

theorem lamv_mul (m : ℕ) (s t : G ℚ Ω) :
    lamv l m (s * t) = lamv l m s + lamv l m t + (l : Qbar l) ^ m * lamv l m s * lamv l m t := by
  apply mul_left_cancel₀ (pow_ne_zero m (natCast_ne_zero (l := l)))
  have hs := pow_mul_lamv (l := l) m s
  have ht := pow_mul_lamv (l := l) m t
  rw [pow_mul_lamv, map_mul, Units.val_mul, PadicInt.coe_mul, map_mul]
  linear_combination (-(algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]))) * hs -
    ((l : Qbar l) ^ m * lamv l m s + 1) * ht

theorem exists_lamv_eq {m : ℕ} {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) :
    ∃ a : ℤ_[l], ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ m * a ∧ lamv l m s = algebraMap ℤ_[l] (Qbar l) a := by
  have h1 : PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    simpa [cycMod] using congrArg Units.val hs
  have h2 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)) := by
    rw [RingHom.mem_ker, map_sub, h1, map_one, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨a, ha⟩ := h2
  have h3 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ m * a := by rw [← ha]; ring
  refine ⟨a, h3, mul_left_cancel₀ (pow_ne_zero m (natCast_ne_zero (l := l))) ?_⟩
  rw [pow_mul_lamv, h3, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
  simp

theorem norm_le_one_of_mem {c : Coef l} {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

theorem norm_lamv_le_one {m : ℕ} {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) : ‖lamv l m s‖ ≤ 1 := by
  obtain ⟨a, -, ha⟩ := exists_lamv_eq hs
  rw [ha, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  exact a.2

namespace HTCoIn

end HTCoIn

end GlobalTheory.LambdaValuationPowers
