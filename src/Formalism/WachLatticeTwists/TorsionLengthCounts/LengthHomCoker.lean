import Formalism.WachLatticeTwists.StatementDual
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SingleEqSmul

open Module IsDiscreteValuationRing Formalism.NG

noncomputable section

namespace Formalism.RepresentationBoundsCohomology

namespace FlowLoadBounds

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

lemma mem_annKO {H : Type*} [AddCommGroup H] [Module O H] (S : Submodule O H)
    (φ : H →ₗ[O] KO O) : φ ∈ annKO O S ↔ ∀ x ∈ S, φ x = 0 := Iff.rfl

end FlowLoadBounds

end Formalism.RepresentationBoundsCohomology
