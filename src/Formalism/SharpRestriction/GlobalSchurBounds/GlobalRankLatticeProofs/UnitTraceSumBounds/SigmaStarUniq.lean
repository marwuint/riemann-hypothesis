import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

open Formalism.MainNotions.TaylorLogMetric Classical

namespace Formalism.MainNotions.Ext

def lat2 (w₁ w₂ : ℂ) : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂}

def SigmaStarEx : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 →
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
      ∀ ω ∈ lat2 w₁ w₂, ∀ z, U1 (lat2 w₁ w₂) ω G z = (if ω / 2 ∈ lat2 w₁ w₂ then 1 else -1) * G z

def DiscrNe : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → discr (lat2 w₁ w₂) ≠ 0

end Formalism.MainNotions.Ext
