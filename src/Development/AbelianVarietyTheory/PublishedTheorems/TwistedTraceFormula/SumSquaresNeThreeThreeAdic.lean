import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HermLocal

namespace GlobalTheory.HermLocal.Model

section Quad
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]

end Quad

instance two_not_sq : Fact (∀ r : ℚ_[2], r ^ 2 ≠ 2 + 0 * r) := ⟨fun r h => by
  rw [zero_mul, add_zero] at h
  have h1 := congrArg Padic.valuation h
  have h2 : (2 : ℚ_[2]).valuation = 1 := by exact_mod_cast Padic.valuation_p (p := 2)
  rw [Padic.valuation_pow, h2] at h1
  omega⟩

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem norm_one_add_sq (t : ℚ_[3]) (ht : ‖t‖ ≤ 1) : ‖1 + t ^ 2‖ = 1 := by
  let s : ℤ_[3] := ⟨t, ht⟩
  have hu : IsUnit (1 + s ^ 2) := by
    by_contra h
    have h1 : 1 + s ^ 2 ∈ RingHom.ker (PadicInt.toZMod (p := 3)) := by
      rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, map_add, map_pow, map_one] at h1
    revert h1
    generalize PadicInt.toZMod s = z
    revert z; decide
  exact PadicInt.isUnit_iff.1 hu

instance neg_one_not_sq : Fact (∀ r : ℚ_[3], r ^ 2 ≠ -1 + 0 * r) := ⟨fun r h => by
  rw [zero_mul, add_zero] at h
  have h1 : ‖r‖ ^ 2 = 1 := by rw [← norm_pow, h]; simp
  have h2 : ‖r‖ ≤ 1 := by nlinarith [norm_nonneg r]
  have := norm_one_add_sq r h2
  rw [h] at this
  simp at this⟩

end GlobalTheory.HermLocal.Model
