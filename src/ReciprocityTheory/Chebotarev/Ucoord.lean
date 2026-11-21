import Mathlib
import ReciprocityTheory.Chebotarev.NZIdeal

open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem

namespace ReciprocityTheory.Cheb

noncomputable section

open scoped Classical

variable {E : Type} [Field E] [NumberField E]

def embZ : 𝓞 E →ₗ[ℤ] mixedSpace E :=
  ((mixedEmbedding E).comp (algebraMap (𝓞 E) E)).toIntAlgHom.toLinearMap

def latOf (I : Ideal (𝓞 E)) : Submodule ℤ (mixedSpace E) :=
  Submodule.map (embZ (E := E)) (I.restrictScalars ℤ)

end

end ReciprocityTheory.Cheb
