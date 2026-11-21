import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.CharPair

variable (P Q R S : ℕ)

def detR (h : P ≤ R) : Pol P Q R 0 :=
  (Matrix.of fun a c : Fin P => (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)).det

variable {P Q}

variable (P Q)

end GlobalTheory.CharPair

end
