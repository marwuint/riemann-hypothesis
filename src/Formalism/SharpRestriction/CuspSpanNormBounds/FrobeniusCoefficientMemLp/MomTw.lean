import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def twD (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then (-Complex.I) ^ (r - i.val)
  else if r + k < i.val then (-Complex.I) ^ (r - (2 * r + k - i.val))
  else 1

def twT (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.diagonal (twD k r)

def twTi (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.diagonal (fun i => star (twD k r i))

end Formalism.MainNotions.S.Pv.Mom
