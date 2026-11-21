import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EndIntWOf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TransInvOf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RetLat

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

theorem delta_ne' (HI : IdealLattice) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 :=
  delta_ne HI discrNe_holds D cc hc δ hδ

end Formalism.MainNotions.Ext
