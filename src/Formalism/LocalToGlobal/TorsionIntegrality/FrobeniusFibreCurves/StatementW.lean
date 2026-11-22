import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementJ
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp

noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.L2.Th1.A (fgl iSer logSer wpReg g₂ g₃ IntModel)

section Defs

variable {K : Type} [Field K] [CharZero K]

def sgW (W : WeierstrassCurve K) (s2 : K) : PowerSeries K := sgStar s2 (wpReg W)

def phW (W : WeierstrassCurve K) (s2 : K) : PowerSeries K := phO s2 (wpReg W) (logSer W)

def beW (W : WeierstrassCurve K) (s2 : K) : MvPowerSeries (Fin 2) K := cob (fgl W) (phW W s2)

def e1W (W : WeierstrassCurve K) (xT : K) : K := xT + W.b₂ / 12

def kapW (W : WeierstrassCurve K) (xT : K) : K := 3 * e1W W xT ^ 2 - g₂ W / 4

def evenSigmaLogAtTwoTorsion (W : WeierstrassCurve K) (s2 xT : K) : PowerSeries K :=
  phE s2 (e1W W xT) (kapW W xT) (wOf (e1W W xT) (wpReg W)) (logSer W)

end Defs

def CurveSigma : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    PowerSeries.constantCoeff (phW W s2) = 0 ∧
    PowerSeries.subst (logSer W) (sgW W s2) = PowerSeries.X * fExp (-phW W s2) ∧
    MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * (atS (sgW W s2) * atD (sgW W s2)) =
      at1 0 (sgW W s2) ^ 2 * at1 1 (sgW W s2) ^ 2 * wpDiff (wpReg W)

def WeierstrassBiadditiveModEquiv : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K) (s2 : K),
    IntModel W → ‖(2 : K)‖ = 1 →
    DivAB (beW W s2) ∧ swap2 (beW W s2) = beW W s2 ∧
      Simeq (d1 (fgl W) (beW W s2)) 0 ∧ Simeq (d1 (fgl W) (swap2 (beW W s2))) 0

end Formalism.L2.Th1.B
