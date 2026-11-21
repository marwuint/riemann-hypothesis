import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qc_detU_coe (n : ℕ) : ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = algebraMap _ _ (genMat ℤ n).det := rfl

end Formalism.InvariantFactorPaths.ColumnFamilies
