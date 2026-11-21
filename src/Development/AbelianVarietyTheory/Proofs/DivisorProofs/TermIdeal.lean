import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal

noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.ConeMono

variable {X : Type} [AddCommGroup X]

def ev (a b : X) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := LinearMap.applyₗ b ∘ₗ LinearMap.applyₗ a

@[simp] theorem ev_apply (a b : X) (β : LinearMap.BilinForm ℤ X) : ev a b β = β a b := rfl

end GlobalTheory.ConeMono
