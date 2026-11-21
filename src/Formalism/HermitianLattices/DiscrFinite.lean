import Mathlib
import Formalism.AlphaUniqueness.Statement
import Formalism.LatticeTheta.Statement
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.GenusCovolBound

open Module Formalism.K

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Defs

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V]

abbrev discr (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) : Type _ :=
  (tdualSub h L) ⧸ (L.comap (tdualSub h L).subtype)

variable [IsScalarTower (NumberField.RingOfIntegers K) K V]

end Defs

end Formalism.HermitianLatticesTheory
