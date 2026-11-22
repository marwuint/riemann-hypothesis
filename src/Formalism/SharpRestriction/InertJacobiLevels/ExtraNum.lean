import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Finset

def massH {R : Ranks} (H : Host R) (M : ℕ) : ℝ :=
  letI := H.cmStar
  Formalism.HermitianLatticesTheory.mass (stdForm H.E M) (stdLat H.E M)

end Formalism.MainNotions.Inhab

end
