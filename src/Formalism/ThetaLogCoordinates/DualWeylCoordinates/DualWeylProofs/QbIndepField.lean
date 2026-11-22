import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

variable [NeZero n]

instance qb_fintypeStd (mu : Fin n → ℤ) : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _

end Formalism.InvariantFactorPaths.ColumnFamilies
