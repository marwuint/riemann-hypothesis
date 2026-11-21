import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfFreeParAlgIndep
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFreeParAlgIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

theorem FreeParAlgIndep.full : FreeParAlgIndep.Statement := FreeParAlgIndep.proof

theorem GenSecSeparable.full : GenSecSeparable.Statement :=
  GenSecSeparable.of_freeParAlgIndep FreeParAlgIndep.full

theorem ChowFormSectionVertical.full : ChowFormSectionVertical.Statement :=
  ChowFormSectionVertical.of_freeParAlgIndep FreeParAlgIndep.full

end GroundTheory.Heights₂.Heights.Vertical
