import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableIffOfLeOfLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientMaximalIdealPowSmulTop

open IsDiscreteValuationRing Pointwise

namespace GlobalTheory

section Span

variable {R : Type*} (K : Type*) {V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

theorem exists_ne_zero_smul_mem_of_mem_span_fractionField {M : Submodule R V} {x : V}
    (hx : x ∈ Submodule.span K (M : Set V)) : ∃ a : R, a ≠ 0 ∧ a • x ∈ M := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩

theorem span_inf_restrictScalars_eq {M : Submodule R V} {W : Submodule K V}
    (h : W ≤ Submodule.span K (M : Set V)) :
    Submodule.span K ((M ⊓ W.restrictScalars R : Submodule R V) : Set V) = W := by
  refine le_antisymm (Submodule.span_le.mpr fun x hx => hx.2) fun x hx => ?_
  obtain ⟨a, ha, hax⟩ := exists_ne_zero_smul_mem_of_mem_span_fractionField K (h hx)
  have ha' : algebraMap R K a ≠ 0 := by simpa using ha
  rw [← Submodule.smul_mem_iff _ ha', algebraMap_smul]
  exact Submodule.subset_span ⟨hax, W.smul_of_tower_mem a hx⟩

variable {K}

variable [IsPrincipalIdealRing R]

end Span

end GlobalTheory
