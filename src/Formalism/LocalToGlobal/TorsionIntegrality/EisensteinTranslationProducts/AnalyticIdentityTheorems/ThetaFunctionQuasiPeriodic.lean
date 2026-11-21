import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroTranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassPSecondDerivative

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace SemicharacterPairingLemmas

end SemicharacterPairingLemmas

open SemicharacterPairingLemmas OperatorUThetaLemmas

theorem operator_u_theta : OpUTh0 := by
  intro L t x z
  rw [← opUMul L x t (sgStar L) z]
  simp only [th0, opU]
  ring

end Formalism.L2.Th1.F
