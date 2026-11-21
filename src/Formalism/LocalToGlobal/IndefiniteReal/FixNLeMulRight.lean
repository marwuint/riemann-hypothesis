import Formalism.LocalToGlobal.IndefiniteReal.CongNormal

noncomputable section

open NumberField

namespace Formalism.IndefR.principalLevelFrame

section SSP

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]
variable {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ}

def Intw (π π' : Formalism.L2.NG.FinTyp L n) (T : π.S →ₗ[ℂ] π'.S) : Prop :=
  ∀ (h : Formalism.AUTREP.GAf L n) (f : π.S), T ⟨Formalism.L2.NG.rt L n h f, π.stable h f f.2⟩ =
    ⟨Formalism.L2.NG.rt L n h (T f), π'.stable h _ (T f).2⟩

end SSP

end Formalism.IndefR.principalLevelFrame
