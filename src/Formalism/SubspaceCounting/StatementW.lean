import Mathlib

noncomputable section

open scoped BigOperators

namespace Formalism.G0

open Polynomial in

def msDualMat {L : Type} [Field L] {r : ℕ} (g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L[X] :=
  ((g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C)).transpose

end Formalism.G0
