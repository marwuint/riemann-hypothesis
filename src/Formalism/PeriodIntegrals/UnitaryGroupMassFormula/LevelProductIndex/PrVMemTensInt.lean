import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.Development

open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

noncomputable section

namespace PI.LPI

theorem prV_tmul' {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) (a : FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (e ⊗ₜ[F] a) = e ⊗ₜ[F] (a v) := rfl

end PI.LPI
