import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceEmb
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.LocalFields.LubinTateLimitGalois
import GroundTheory.LocalFields.MaximalUnramified

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup

namespace GlobalTheory.PZ.LTExist

section Padic

variable (l : ℕ) [Fact l.Prime]

@[instance_reducible]
def omRel : ValuativeRel (Om l) := .ofValuation (PadicAlgCl.valued l).v

attribute [local instance] omRel

theorem om_compatible : (PadicAlgCl.valued l).v.Compatible := Valuation.Compatible.ofValuation _

theorem om_isValuativeTopology : IsValuativeTopology (Om l) :=
  haveI := om_compatible l
  isValuativeTopology_of_valued

attribute [local instance] om_isValuativeTopology

theorem om_vle_iff (x y : Om l) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := Iff.rfl

theorem om_valuativeExtension : ValuativeExtension ℚ_[l] (Om l) := ⟨fun a b => by
  rw [om_vle_iff, PadicAlgCl.norm_extends, PadicAlgCl.norm_extends,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation) a b,
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le]⟩

attribute [local instance] om_valuativeExtension

variable {l}

theorem finExt_finiteDimensional (K : FinExt l) : FiniteDimensional ℚ_[l] ↥K.1 := K.2

attribute [local instance] finExt_finiteDimensional

end Padic

end GlobalTheory.PZ.LTExist

end
