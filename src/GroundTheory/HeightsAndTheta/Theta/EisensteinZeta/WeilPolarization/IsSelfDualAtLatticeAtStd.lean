import Mathlib
import GroundTheory.AutomorphicForms.HermitianExistence
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open Module Matrix NumberField IsDedekindDomain TensorProduct GroundTheory.Automorphic

section Objects

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable {F E}

variable (v : HeightOneSpectrum (𝓞 F))

end Objects

section Inhabitants

set_option linter.unusedSectionVars false

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

variable (v : HeightOneSpectrum (𝓞 F))

end Inhabitants

end GroundTheory.Heights₂.Theta
