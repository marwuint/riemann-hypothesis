import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.FinalOfNRDense
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementG
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.NRCMOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique

namespace Formalism.L2.Th1.D

theorem nrDense : NRDense := NRDense_of sqrtKur

theorem nrcmOfCM4 : Formalism.L2.Th1.CM.CM4 → NRCM := NRCM_of sqrtKur denseOK homothetic_lattice_integral_s2 nrDense

end Formalism.L2.Th1.D
