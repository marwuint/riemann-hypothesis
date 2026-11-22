import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SigmaStarUniq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat
import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarUniq
import Formalism.PeriodIntegrals.DiscrNe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NonzeroDiscriminants.DiscMain
import Formalism.PeriodIntegrals.SigmaStarEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesExistence.SigmaStarEx

namespace Formalism.MainNotions.Ext

theorem discrNe_holds : DiscrNe := DiscrNeWork.discrNe_all

theorem sigmaStarEx_holds : SigmaStarEx := PI.SSE.sigmaStarEx

end Formalism.MainNotions.Ext
