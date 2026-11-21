import Formalism.LocalToGlobal.GlobalTheory.GL4.ColumnLatticeExactSlope
import Formalism.LocalToGlobal.GlobalTheory.GL4.MapIntRatComplex
import Formalism.LocalToGlobal.GlobalTheory.GL4.PLemTLat
import Formalism.LocalToGlobal.GlobalTheory.GL4.PCoordH

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

theorem column_exact_slope_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : fam0 Fm ColSlopeEq :=
  ⟨0, fun _ _ _ _ => column_lattice_exact_slope _⟩

theorem lower_slope_inequality_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilySlopeLowerOpenPart Fm :=
  familySlopeLowerOpen_of_std standard_slope_lower hook_length_bound Fm (column_exact_slope_family Fm)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
