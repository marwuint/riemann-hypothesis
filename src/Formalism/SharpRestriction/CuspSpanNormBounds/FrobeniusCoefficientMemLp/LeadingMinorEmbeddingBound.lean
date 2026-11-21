import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.ProdLeProdSubOneLe
import Formalism.SharpRestriction.CuspSpanNormBounds.GramProductLeHeightBoundTwo
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

set_option linter.unusedVariables false

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def rhoIJ {j : ℕ} (I J : Fin j ↪o Fin (D.R.rS + 1)) : ℝ := ∏ a, (rhoF D (I a) * rhoF D (J a))

theorem absMinor_eq {j : ℕ} (Z : GramM D) (I J : Fin j ↪o Fin (D.R.rS + 1)) (τ : D.what₂.Tau) :
    Formalism.MainNotions.S.UnitaryVolumeMass.absMinor D Z I J τ = ‖embS D τ (Z.submatrix I J).det‖ * rhoIJ D I J := rfl

end Formalism.MainNotions.S.Pv.HH

end
