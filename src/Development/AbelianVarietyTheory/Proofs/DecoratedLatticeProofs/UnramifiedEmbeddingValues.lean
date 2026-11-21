import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM NumberField

noncomputable section

namespace GlobalTheory.NfKur

variable {M : Type} [Field M] [NumberField M] {l : ℕ} [Fact l.Prime]

theorem norm_int_le (φ : M →+* ℂ_[l]) (a : 𝓞 M) : ‖φ (a : M)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (φ (a : M)) := by
    convert map_isIntegral_int φ a.isIntegral_coe; exact Subsingleton.elim _ _
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[l])).integer (φ (a : M)) := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[l]))).mem_of_integral h1
  have h3 : ‖φ (a : M)‖₊ ≤ 1 := h2
  exact_mod_cast h3

def primeAt (φ : M →+* ℂ_[l]) : Ideal (𝓞 M) where
  carrier := {a | ‖φ (a : M)‖ < 1}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := fun c {a} ha => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le φ c) (norm_nonneg _) ha

theorem mem_primeAt (φ : M →+* ℂ_[l]) (a : 𝓞 M) : a ∈ primeAt φ ↔ ‖φ (a : M)‖ < 1 := Iff.rfl

theorem notMem_primeAt (φ : M →+* ℂ_[l]) (a : 𝓞 M) : a ∉ primeAt φ ↔ ‖φ (a : M)‖ = 1 :=
  ⟨fun h => le_antisymm (norm_int_le φ a) (not_lt.1 h), fun h h' => absurd h (ne_of_lt h')⟩

instance primeAt_isPrime (φ : M →+* ℂ_[l]) : (primeAt φ).IsPrime := by
  refine ⟨(Ideal.ne_top_iff_one _).2 ((notMem_primeAt φ 1).2 (by simp)), fun {a b} hab => ?_⟩
  by_contra hc
  rw [not_or, notMem_primeAt, notMem_primeAt] at hc
  exact (notMem_primeAt φ (a * b)).2 (by simp [hc.1, hc.2]) hab

end GlobalTheory.NfKur
