import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PMaxOscillation
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PMollifierLowerBound
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartComparison
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PCutoffs
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PGlueRegularised
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ChartFun
import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsCompactImageClosureMid
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PExpExtension
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PKernelPositive
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PImTauBounds
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PHodgeDerivative
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PAnalyticDerivBound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryBound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PMatrixDetDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PGramEntryDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramDeriv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

theorem GlueRegularised.full : GlueRegularised.Statement := GroundTheory.Heights₂.Heights.Regular.GlueRegularised.proof

theorem KernelPositive.full : KernelPositive.Statement :=
  kernelPositive_statement

theorem Tau0Holomorphic.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    Tau0Holomorphic.Statement :=
  Tau0Holomorphic.proof (ExpQuadMonomial.proof hE hO hD)

theorem ImTauBounds.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    ImTauBounds.Statement :=
  ImTauBounds.proof (Tau0Holomorphic.cond hE hO hD) KernelPositive.full

theorem HodgeDerivative.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    HodgeDerivative.Statement :=
  have hInv : InvEntryDeriv.Statement := InvEntryDeriv.proof InvEntryBound.proof
  HodgeDerivative.proof (ImTauBounds.cond hE hO hD) (Tau0Holomorphic.cond hE hO hD)
    AnalyticDerivBound.proof hInv
    (LogDetGramDeriv.proof InvEntryBound.proof hInv MatrixDetDeriv.proof GramEntryDeriv.proof)

end GroundTheory.Heights₂.Heights.Regular
