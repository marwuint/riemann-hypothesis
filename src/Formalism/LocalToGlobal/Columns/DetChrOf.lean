import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct

namespace Formalism.L2.Col

namespace DetChrOf

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance liesOver (P : HeightOneSpectrum (𝓞 E)) : P.asIdeal.LiesOver (P.under (𝓞 F)).asIdeal := ⟨rfl⟩

end Loc

section Tens

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev algFAE : Algebra F (FiniteAdeleRing (𝓞 E) E) :=
  ((algebraMap E (FiniteAdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra

attribute [local instance] algFAE

end Tens

end DetChrOf

end Formalism.L2.Col
