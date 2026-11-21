import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcEvGLDetUZpow

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def qc_genPt (F : Type) [CommRing F] (n : ℕ) : GL (Fin n) (GLCoord F n) :=
  Matrix.nonsingInvUnit ((algebraMap _ (GLCoord F n)).mapMatrix (genMat F n))
    (by rw [← RingHom.map_det]; exact IsLocalization.Away.algebraMap_isUnit _)

lemma qc_genPt_val (F : Type) [CommRing F] (n : ℕ) (a b : Fin n) :
    (qc_genPt F n).val a b = algebraMap (MvPolynomial (Fin n × Fin n) F) (GLCoord F n) (X (a, b)) := rfl

end Formalism.InvariantFactorPaths.ColumnFamilies
