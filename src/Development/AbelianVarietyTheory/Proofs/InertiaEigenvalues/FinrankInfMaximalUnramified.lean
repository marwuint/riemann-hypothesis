import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries
import GroundTheory.LocalFields.LubinTateLimitGalois
import GroundTheory.LocalFields.LubinTateUnramified
import GroundTheory.LocalFields.KroneckerWeber

noncomputable section

open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup IntermediateField

namespace GlobalTheory.PZ.LTExists

open Formalism.BasicNotions Formalism.BasicNotions.Loc

variable (l : ℕ) [Fact l.Prime]

@[instance_reducible]
def omRel : ValuativeRel (Om l) := ValuativeRel.ofValuation (NormedField.valuation (K := Om l))

attribute [local instance] omRel

theorem om_vle_iff (x y : Om l) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := Iff.rfl

theorem omTop : IsValuativeTopology (Om l) := by
  have hc : (NormedField.valuation (K := Om l)).Compatible := Valuation.Compatible.ofValuation _
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := Om l))
    (fun {s} ↦ (NormedField.toValued (K := Om l)).is_topological_valuation s)

theorem padic_vle_iff (a b : ℚ_[l]) : a ≤ᵥ b ↔ ‖a‖ ≤ ‖b‖ := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [(valuation ℚ_[l]).vle_iff_le]
    simp
  · rw [(valuation ℚ_[l]).vle_iff_le, ← div_le_one (norm_pos_iff.mpr hb), ← norm_div,
      ← PadicRank.mem_integer_padic_iff, Valuation.mem_integer_iff, map_div₀,
      div_le_one₀ (zero_lt_iff.mpr ((valuation ℚ_[l]).ne_zero_iff.mpr hb))]

theorem omExt : ValuativeExtension ℚ_[l] (Om l) :=
  ⟨fun a b => by rw [om_vle_iff, padic_vle_iff, norm_algebraMap', norm_algebraMap']⟩

attribute [local instance] omTop omExt

variable {l}

end GlobalTheory.PZ.LTExists

namespace GlobalTheory.PZ

end GlobalTheory.PZ

end
