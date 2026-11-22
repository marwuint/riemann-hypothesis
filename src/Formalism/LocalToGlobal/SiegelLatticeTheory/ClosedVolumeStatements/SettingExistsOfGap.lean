import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFromLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NUnimodLoc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas

namespace Formalism.L2.SG.Closed

theorem NUnimodLoc_holds : Formalism.L2.SG.Pf.WFL.NUnimodLoc := by
  have h := n_unimodular_local
  intro k r ε e f wf z0 z c hF hc hz
  exact h k r ε e f wf z0 z c ⟨hF.ee, hF.ff, hF.ef, hF.ez, hF.fz, hF.zz, hF.ww, hF.ew, hF.fw, hF.zw⟩ hc hz

theorem QuotProdK_holds : Formalism.L2.SG.Pf.WFL.QuotProdK := quotient_product_compact

end Formalism.L2.SG.Closed
