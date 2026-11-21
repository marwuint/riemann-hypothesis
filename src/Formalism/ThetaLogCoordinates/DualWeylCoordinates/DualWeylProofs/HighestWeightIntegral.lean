import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcEvGLGenPtInt

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qr_lastIdx (m : ℕ) : lastIdx (m + 1) = Fin.last m := rfl

end Formalism.InvariantFactorPaths.ColumnFamilies
