import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

instance LocalizeSubvar.exLoc (k : Type) [Field k] : IsLocalization.AtPrime k (⊥ : Ideal k) :=
  IsLocalization.of_le_isUnit fun a ha =>
    (IsUnit.mem_submonoid_iff a).mpr (isUnit_iff_ne_zero.mpr fun h => ha (h ▸ Ideal.zero_mem _))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
