import Mathlib
import GroundTheory.AutomorphicForms.UnitaryGroupScheme
import GroundTheory.HeightsAndTheta.Theta.CMDatum
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.MemRangeIffIsIntegral
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace UnitaryReduction

open NumberField GroundTheory.Automorphic Module TensorProduct Matrix FunctionalEquationAlt

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

section Rational

variable (B : HermitianForm F E V)

def perp (W : Submodule E V) : Submodule E V := W.orthogonalBilin B.toSesq

end Rational

section Example

variable (F E)

end Example

end UnitaryReduction

end GroundTheory.Heights₂.Theta
