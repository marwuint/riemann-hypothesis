import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.BCoreT

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def qs_SM {A : Type*} [CommRing A] (G : Matrix (Fin n) (Fin n) A) (b : ℕ) : Matrix (SymIdx n b) (SymIdx n b) A :=
  fun α β => MvPolynomial.coeff (symMono α) (∏ m : Fin n, (∑ a : Fin n, MvPolynomial.C (G a m) * X a) ^ (β.1 m : ℕ))

def qs_gC (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord ℤ n) :=
  Matrix.of fun a b => algebraMap _ (GLCoord ℤ n) (genMat ℤ n a b)

def qs_gI (n : ℕ) : Matrix (Fin n) (Fin n) (GLCoord ℤ n) := Matrix.of fun a b => ginvC n a b

lemma qs_SymMat_eq (n b : ℕ) : SymMat n b = qs_SM (qs_gC n) b := rfl

lemma qs_SymDMat_eq (n b : ℕ) : SymDMat n b = qs_SM (qs_gI n).transpose b := rfl

end Formalism.InvariantFactorPaths.ColumnFamilies
