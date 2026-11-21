import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementJ

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

def ThetaLogIsSubst : Prop :=
  ∀ (K : Type) [Field K] (ν r0 r1 : ℕ) [NeZero ν] (om oms : Fin ν → ZMod (2 * ν) → K) (ϖ : K)
    (μ : PowerSeries K) (Tht : MvPowerSeries (Bool × EV ν r0 r1) K),
    PowerSeries.constantCoeff μ = 0 →
    thetaLog om oms ϖ μ Tht = MvPowerSeries.subst (fun x => MvPowerSeries.subst
        (fun y => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
        (MvPowerSeries.C ϖ * sSub om oms μ x)) Tht

end Formalism.InvariantFactorPaths.G7
