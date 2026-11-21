import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.DetLetters

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def sharpHom {k₁ ι ζ : Type*} [CommRing k₁] {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (g gi : Matrix (Fin n) (Fin n) k₁) :
    MvPolynomial (LVar ι ζ n) k₁ →ₐ[k₁] MvPolynomial (LVar ι ζ n) k₁ :=
  aeval fun x =>
    match x with
    | Sum.inl (i, a) =>
      if i ∈ S then
        (if isVec i then Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C) a
        else Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C).transpose a)
      else X (Sum.inl (i, a))
    | Sum.inr z => X (Sum.inr z)

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
