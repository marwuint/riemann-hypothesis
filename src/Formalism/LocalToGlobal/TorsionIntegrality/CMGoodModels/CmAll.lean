import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorStatus
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgStatus
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedStatus
import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFixJ
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModInertKur

namespace Formalism.L2.Th1.CM

theorem cm1 : JInvariantIntegrality := ReciprocityTheory.ChartRestriction.L1.cm1
theorem cm4 : CM4 := ReciprocityTheory.ChartRestriction.L1.cm4
theorem cm3 : CM3 := ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree
theorem cm2 [h : Fact CM2] : CM2 := h.out

end Formalism.L2.Th1.CM
