import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.LocalRingCardinality.SpanPowerMembership.GatSetting
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

section CC

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

def ccL (σ : Type) : MvPolynomial σ K →ₗ[K] K := lcoeff K 0

theorem ccL_apply {σ : Type} (F : MvPolynomial σ K) : ccL K σ F = constantCoeff F := rfl

def ccInt (σ : Type) : Submodule R (MvPolynomial σ K) :=
  (LinearMap.range (Algebra.linearMap R K)).comap ((ccL K σ).restrictScalars R)

theorem mem_ccInt {σ : Type} (F : MvPolynomial σ K) : F ∈ ccInt R K σ ↔ ∃ a : R, algebraMap R K a = constantCoeff F :=
  Iff.rfl

end CC

end Formalism.MainNotions.G.Inhab

end
