import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
import ReciprocityTheory.SemistableReduction.AlgebraicIndependentOfDerivations

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

noncomputable section

namespace GlobalTheory.CharPair.Down

variable {P Q R : ℕ}

def blockR (h : P ≤ R) : Matrix (Fin P) (Fin P) (Pol P Q R 0) :=
  Matrix.of fun a c : Fin P => (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)

theorem detR_eq (h : P ≤ R) : detR P Q R h = (blockR (Q := Q) h).det := rfl

end GlobalTheory.CharPair.Down

namespace GlobalTheory.CharPair

end GlobalTheory.CharPair
