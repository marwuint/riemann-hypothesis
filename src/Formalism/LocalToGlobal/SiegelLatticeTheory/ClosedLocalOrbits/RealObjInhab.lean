import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

noncomputable section

open Matrix

namespace Formalism.L2.SG.RealObj

theorem Dl_diagonal {r : ℕ} (c : Fin (r + 1) → ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    Dl (Matrix.diagonal c) l = ∏ i : Fin l, c (Fin.castLE hl i) := by
  unfold Dl
  rw [dif_pos hl, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hl), Matrix.det_diagonal]
  rfl

end Formalism.L2.SG.RealObj
