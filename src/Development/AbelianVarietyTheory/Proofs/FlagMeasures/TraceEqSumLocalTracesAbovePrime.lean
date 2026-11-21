import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.LocalRingCardinality.DataSpaces
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.LocalTraceSum

open Filter Topology TensorProduct

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem isOpen_lt (γ : ValueGroupWithZero K) : IsOpen {x : K | valuation K x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hγ : γ ≠ 0 := (lt_of_le_of_lt zero_le hx).ne'
  refine (IsValuativeTopology.hasBasis_nhds' x).mem_iff.2 ⟨γ, hγ, fun y hy => ?_⟩
  have := (valuation K).map_add_lt (x := y - x) (y := x) hy hx
  simpa using this

theorem tendsto_pow {x : K} (h : valuation K x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

variable {l : ℕ} [Fact l.Prime] [Algebra ℚ_[l] K]

variable {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

end Local

section Place

variable {F : Type} [Field F] [NumberField F] {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω]

theorem norm_int_le (σ : F →+* Ω) (a : 𝓞 F) : ‖σ a‖ ≤ 1 := by
  have h : IsIntegral ℤ (σ a) := a.isIntegral_coe.map σ.toIntAlgHom
  have h2 : IsIntegral (NormedField.valuation (K := Ω)).integer (σ a) := h.tower_top
  have := (Valuation.integer.integers _).mem_of_integral h2
  exact this

def ker (σ : F →+* Ω) : Ideal (𝓞 F) where
  carrier := {a | ‖σ a‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, RingOfIntegers.coe_eq_algebraMap, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul] at *
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le σ c)) ha

theorem mem_ker (σ : F →+* Ω) (a : 𝓞 F) : a ∈ ker σ ↔ ‖σ a‖ < 1 := Iff.rfl

end Place

end GlobalTheory.LocalTraceSum
