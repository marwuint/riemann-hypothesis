import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.DefsCol

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

variable {ι : Type*}

def minorF {R : Type*} [CommRing R] {n : ℕ} (m : Matrix (Fin n) (Fin n) R) (I J : Finset (Fin n)) : R :=
  if h : J.card = I.card then
    (m.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h)).det
  else 0

def actF {R : Type*} [CommRing R] {n : ℕ} (K : Form R n) (m : Matrix (Fin n) (Fin n) R) : Form R n :=
  fun J => ∑ I : Finset (Fin n), K I * minorF m I J

def heavy (r K : ℕ) (isVec : ι → Bool) (x : ι × Fin (r + K)) : Prop := isVec x.1 = true ↔ r ≤ x.2.val

instance (r K : ℕ) (isVec : ι → Bool) (x : ι × Fin (r + K)) : Decidable (heavy r K isVec x) := by
  unfold heavy; infer_instance

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
