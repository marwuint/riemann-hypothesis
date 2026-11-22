import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.LocalRingCardinality.SpanPowerMembership.GatSetting
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

noncomputable section

namespace Formalism.MainNotions.G.Inhab

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

section CC

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

def ccL (σ : Type) : MvPolynomial σ K →ₗ[K] K := lcoeff K 0

end CC

end Formalism.MainNotions.G.Inhab

end
