import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassMeanPeriods

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors

def classMeanValue (D : D7) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt (D.host.d : ℝ)) - logDerivativeAtOne D

end GlobalTheory.IndefiniteRowSideFullHecke.ClassMeanPeriods
