import Mathlib
import Formalism.HermitianLattices.StatementMass

open NumberField Module

noncomputable section

namespace CMDeg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def sigma (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) : E ≃ₐ[F] E :=
  AlgEquiv.ofRingEquiv (f := starRingAut) (fun x => by simpa using hfix x)

theorem sigma_apply (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (a : E) :
    sigma hfix a = star a := rfl

end CMDeg

