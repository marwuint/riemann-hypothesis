import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Mathlib
import Formalism.PeriodIntegrals.IsoDualPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDualPair.SymmetricMeasureL2NormEqResolutionL2
import Formalism.PeriodIntegrals.IsoFunV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryFunctionSpace.InstFintypeOE
import Formalism.PeriodIntegrals.IsoInvMetric
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.ColChoiceFintype
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.DetSubmatrixFun
import Formalism.PeriodIntegrals.ScalDeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarDegree.ScalDegMain
import Formalism.PeriodIntegrals.IsoDerivB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.IsoDerivB
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwCauchyBinet
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwMain
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwInjective

namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

theorem wwCB_holds (D : D7) : wwCB D := fun k _ N nu y => cauchy_binet_minors (Bool × HH D) k N nu y

theorem ww_holds (D : D7) : ww D :=
  fun l _ N0 N1 nu Th ph Q hQ y' => minor_identity (Bool × HH D) l N0 N1 nu Th ph Q hQ y'

theorem wwInj_holds (D : D7) : wwInj D :=
  fun l _ N nu ph hy J => wwInjective_of cauchy_binet_minors (Bool × HH D) l N nu ph hy J

end Formalism.MainNotions.GL3Columns
