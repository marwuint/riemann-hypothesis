import Mathlib
import GroundTheory.PAdicHodge.FieldOfNorms
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField IsLocalRing

section FieldOfNorms

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
  {L : IntermediateField K Ω} [IsGalois K L]
  [hsapf : Fact (IsStrictlyAPF K Ω L)] [hinf : Fact (¬ FiniteDimensional K L)]

namespace FieldOfNorms

instance isLocalRing_integer_L : IsLocalRing 𝒪[L] :=
  inferInstanceAs (IsLocalRing (valuation L).valuationSubring)

theorem mem_integer_iff (x : FieldOfNorms K Ω L) : x ∈ 𝒪[FieldOfNorms K Ω L] ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation _), ← (valuation _).vle_iff_le,
    vle_iff_norm_le, norm_one]

abbrev E₀ : FinSub K Ω L := (isTowerFor (L := L)).finSub 0

def toL (x : FieldOfNorms K Ω L) : L := ⟨x.1 E₀, E₀.2.1 (x.2.1 E₀)⟩

end FieldOfNorms

end FieldOfNorms

end GroundTheory.PAdicHodge
