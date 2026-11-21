import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.PerfCard

namespace KStar.Selmer

open Matrix Module

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R]

def IsFrobeniusForm (θ : R →ₗ[S] S) : Prop :=
  Function.Bijective ((LinearMap.mul S R).compr₂ θ)

end KStar.Selmer
