import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementS
import Formalism.GaussJetBounds.StatementP

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)

section DefsK

variable {K : Type} [Field K]

def betaPair (H : Type) [Fintype H] (N0 N1 : ℕ) (u : H → K) :
    MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K :=
  ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
    MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2)

end DefsK

end Formalism.L2.Th1.G
