import Mathlib
import Formalism.HermitianLattices.StatementLat

open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Defs

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def invIdeal (P : Ideal R) : Submodule R K :=
  ⨅ p ∈ P, (1 : Submodule R K).comap ((LinearMap.mulLeft R (algebraMap R K p)))

end Defs

end Formalism.HermitianLatticesTheory
