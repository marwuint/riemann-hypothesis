import Mathlib
import GroundTheory.AutomorphicForms.HermitianClassification
import GroundTheory.AutomorphicForms.HermitianNormLocal

noncomputable section

namespace GroundTheory.Automorphic

open GroundTheory.LocalField ValuativeRel

section Field

variable {F : Type*} [Field F]

def SqNorm (s u : F) : Prop := ∃ x y : F, x ^ 2 - s * y ^ 2 = u

variable (h2 : (2 : F) ≠ 0)
include h2

end Field

end GroundTheory.Automorphic
