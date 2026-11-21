import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

def CoefWfRing : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]), CoefWf f → CoefWf g →
    CoefWf (f + g) ∧ CoefWf (f - g) ∧ CoefWf (f * g) ∧ ∀ c : ℂ_[p], InWf c → CoefWf (MvPowerSeries.C c * f)

def SubstWf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
    CoefWf f → IntegralW a → MvPowerSeries.constantCoeff a = 0 → CoefWf (PowerSeries.subst a f)

def EndIntWG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → ModelOverW g.lam g.abelian₂ g.C → ∀ α ∈ W2pair p,
    IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) →
    IntegralW (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])

end Formalism.MainNotions.Ext
