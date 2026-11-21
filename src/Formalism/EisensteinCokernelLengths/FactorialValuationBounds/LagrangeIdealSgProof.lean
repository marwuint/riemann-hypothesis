import Formalism.EisensteinCokernelLengths.StatementLIFTV
import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt
import Formalism.WindowSums.PowerSeriesRelationList

namespace Formalism.ZetaNonvanishing.LIFTV

theorem lagrangeIdealSg_proof : LagrangeIdealSg := by
  intro ℓ _ R _ _ sg S₁ S₂ c hd hc
  exact Formalism.LIFT.lift_LagrangeIdeal R (ℓ : R) ℤ S₁ S₂ c (fun a b => sg + padicValInt ℓ (a - b)) hd hc

end Formalism.ZetaNonvanishing.LIFTV
