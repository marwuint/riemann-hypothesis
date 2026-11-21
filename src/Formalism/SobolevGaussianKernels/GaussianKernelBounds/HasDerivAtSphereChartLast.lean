import Mathlib

namespace Formalism.SL.P

open MeasureTheory
open scoped ContDiff

namespace SphereChartDerivatives

variable {n : ℕ}

def sn (t : ℝ) (y : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) y t

@[simp] lemma sn_last (t : ℝ) (y : Fin n → ℝ) : sn t y (Fin.last n) = t := by simp [sn]
@[simp] lemma sn_cast (t : ℝ) (y : Fin n → ℝ) (k : Fin n) : sn t y (Fin.castSucc k) = y k := by
  simp [sn]

end SphereChartDerivatives

end Formalism.SL.P
