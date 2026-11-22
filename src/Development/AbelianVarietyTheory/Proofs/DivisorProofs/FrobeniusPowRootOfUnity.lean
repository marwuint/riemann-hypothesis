import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import ReciprocityTheory.ClassFieldTheory.LocalClassField.CycFieldA

noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKRes.ResSplit

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem dvd_mul_div_gcd (f r : ℕ) : r ∣ f * (r / Nat.gcd f r) := by
  refine ⟨f / Nat.gcd f r, ?_⟩
  rw [← Nat.mul_div_assoc f (Nat.gcd_dvd_right f r), ← Nat.mul_div_assoc r (Nat.gcd_dvd_left f r), mul_comm]

theorem Qr_le_Kn {f : ℕ} (hq : qK p K = p ^ f) (r : ℕ) : Qr p r ≤ Kn p K (r / Nat.gcd f r) := by
  apply UnramifiedExtensions.Kn_le (Q0 p) bot_le
  intro ζ hζ
  apply UnramifiedExtensions.mem_Kn_of_pow K
  rw [residue_cardinality_base_field] at hζ
  obtain ⟨t, ht⟩ := dvd_mul_div_gcd f r
  obtain ⟨c, hc⟩ : p ^ r - 1 ∣ (p ^ r) ^ t - 1 := by simpa using Nat.sub_dvd_pow_sub_pow (p ^ r) 1 t
  rw [hq, ← pow_mul, ht, pow_mul, hc, pow_mul, hζ, one_pow]

def incQ {f : ℕ} (hq : qK p K = p ^ f) (r : ℕ) : Qr p r →ₐ[ℚ_[p]] Kn p K (r / Nat.gcd f r) :=
  IntermediateField.inclusion (Qr_le_Kn p K hq r)

def incK (n : ℕ) : K →ₐ[ℚ_[p]] Kn p K n := IntermediateField.inclusion (UnramifiedExtensions.le_Kn K n)

def comp {f : ℕ} (hq : qK p K = p ^ f) (r i : ℕ) : KQ p K r →ₐ[ℚ_[p]] Kn p K (r / Nat.gcd f r) :=
  Algebra.TensorProduct.productMap (incK p K _) ((incQ p K hq r).comp ((frobQ p r) ^ i))

def eMap {f : ℕ} (hq : qK p K = p ^ f) (r : ℕ) :
    KQ p K r →ₐ[ℚ_[p]] (Fin (Nat.gcd f r) → Kn p K (r / Nat.gcd f r)) :=
  Pi.algHom _ _ fun i => comp p K hq r i

end GlobalTheory.LKRes.ResSplit
