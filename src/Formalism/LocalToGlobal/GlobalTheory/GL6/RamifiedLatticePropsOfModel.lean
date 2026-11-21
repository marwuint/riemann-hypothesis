import Formalism.LocalToGlobal.GlobalTheory.GL6.EqOneOfCoprimeTorsionTwoPrimes
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedRankEqFinrank
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClearDenominatorsLattice

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Classical NumberField

section Parts

variable (D : D7) (u : D.what₂.Word)

def RamifiedSlopeFormula : Prop :=
  (D.fm u).ramLat.mu = ((D.fm u).lat 0).mu -
    (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2)

end Parts

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
