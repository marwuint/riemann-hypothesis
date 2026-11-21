import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def qb_sU (w : Fin n → ℤ) : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ :=
  Units.map (AddMonoidAlgebra.of ℤ (Fin n → ℤ)) (toUnits (Multiplicative.ofAdd w))

lemma qb_sU_val (w : Fin n → ℤ) : ((qb_sU w : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ) : AddMonoidAlgebra ℤ (Fin n → ℤ)) =
    AddMonoidAlgebra.single w 1 := rfl

variable [NeZero n]

end Formalism.InvariantFactorPaths.ColumnFamilies
