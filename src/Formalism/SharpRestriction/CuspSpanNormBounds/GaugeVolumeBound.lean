import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGenB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.NatSmulMulEq
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative

noncomputable section

namespace Formalism.MainNotions.FundamentalDomainUnfolding

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates
open scoped ENNReal

def muInf (I : AutInst) : Measure I.Ginf := Measure.pi fun v => Formalism.REAL.muG (I.ε v)

end Formalism.MainNotions.FundamentalDomainUnfolding

end
