import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhNormOfUnits
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeOfTwoIdentities
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.CoeffPowMulPowEqZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.CoeffPowMulPowEqZeroOfLt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormUnits
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormLimit

namespace Formalism.MainNotions.Ext.CutA

theorem phNormOfUnits_holds : PhNormOfUnits := by
  intro p _ g S hok
  exact phase_norm_units p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

theorem phNormClosed_holds : PhNormClosed := by
  intro p _ g S hok
  exact phase_norm_limit_target p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

end Formalism.MainNotions.Ext.CutA
