import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.ConstantCoeffVecConsPairEqZero
import Formalism.GL3MeanSquares.HookFormulaTorsion.SquareEqDiagOfQuadraticEven
import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.CharacterExistsAllEmbeddings
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.IntegralThirdInvariantDerivative

namespace Formalism.L2.Th1.C

theorem simeqIffCong : SimeqIffCong := simeq_iff_congruence
theorem unitBallClosed : UnitBallClosed := unit_ball_closed
theorem phOIsPh : PhOIsPh := odd_phi_is_phi
theorem first_level_from_universal_law : FirstLevelFromUniversal := first_level_from_universal_holds

theorem logDerivInt : LogDerivInt := log_derivative_integral'
theorem derivation_cube_integral_jet : ThirdJetIntegral := third_jet_integral
theorem jetsUnramified : JetsUnramified := jets_unramified
theorem jetsShape : JetsShape := jets_shape

end Formalism.L2.Th1.C
