import Mathlib

noncomputable section

namespace PositivityTheory.KB.ChainCochainPairing

variable {Y : Type}

def cob {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : (Fin (m + 2) → Y) → ℝ :=
  fun y => ∑ i : Fin (m + 2), (-1 : ℝ) ^ (i : ℕ) * F fun j => y (i.succAbove j)

end PositivityTheory.KB.ChainCochainPairing
