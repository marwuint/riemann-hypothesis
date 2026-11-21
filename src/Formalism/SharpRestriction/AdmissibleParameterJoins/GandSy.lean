import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

theorem servedModel_of_params (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (h3 : 3 ≤ L.sc.x ^ (L.sc.ez / 5)) :
    Formalism.MainNotions.WeightDegreeSizes.ServedHasModel X K := by
  unfold Formalism.MainNotions.WeightDegreeSizes.ServedHasModel
  intro u w hw hV
  refine Formalism.BasicNotions.gIdx_of_cand P K h3 u _ ?_ hw
  unfold VV at hV
  by_contra hc
  exact hV (if_neg (fun h => hc h.1))

end Formalism.MainNotions.J
