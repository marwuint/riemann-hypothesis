import Mathlib
import Formalism.LocalToGlobal.Columns.BrzColLatOneLattice

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality

section Defs

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

@[reducible] def latK (M : Submodule (𝓞 K) (Fin n → K)) : HLat K :=
  ofFormB (Pi.basisFun K (Fin n)) M (formAt (Pi.basisFun K (Fin n)) (hStd K n))

end Defs

end Formalism.L2.Col
