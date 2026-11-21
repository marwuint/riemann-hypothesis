import Mathlib
import GroundTheory.PAdicHodge.FieldOfNorms
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField IsLocalRing

namespace NormTower

end NormTower

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

theorem nrm_toL (x : FieldOfNorms K Ω L) : nrm K ((toL x : L) : Ω) = ‖x‖ := rfl

def toPlus (x : 𝒪[FieldOfNorms K Ω L]) : (tower K Ω L).Plus :=
  ⟨(equivFam K Ω L x).1, NormTower.Fam.isIntFam_of_nrm_le (by
    have := (mem_integer_iff _).mp x.2
    rw [norm_def, NormTower.Fam.norm_def] at this
    exact this)⟩

theorem equivFam_eq_toPlus (x : 𝒪[FieldOfNorms K Ω L]) :
    equivFam K Ω L (x : FieldOfNorms K Ω L) = (toPlus x).toFam := rfl

end FieldOfNorms

end FieldOfNorms

end GroundTheory.PAdicHodge
