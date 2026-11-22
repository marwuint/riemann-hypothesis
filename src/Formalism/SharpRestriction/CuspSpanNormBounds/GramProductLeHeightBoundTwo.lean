import Formalism.HermitianLattices.StatementMass
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DifferentIdealMapNeBot
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsCnt

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Bound

variable (D : D7) (u u' : D.what₂.Word)

def Pt (b C : ℝ) (Z : GramM D) (τ : D.what₂.Tau) : ℝ :=
  ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (Cnt.absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))

end Bound

end Formalism.MainNotions.GramProductBounds

end
