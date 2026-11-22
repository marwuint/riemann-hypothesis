import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbIndepField

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ}

variable {M M' : GLMod n}

end Formalism.InvariantFactorPaths.ColumnFamilies
