import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound

open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder

namespace Formalism.HermitianLatticeCounting.P

def IsW (t : ℤ) : Prop := t = 0 ∨ ∃ k : ℕ, t = 4 ^ k ∨ t = -(4 ^ k)

end Formalism.HermitianLatticeCounting.P
