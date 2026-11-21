import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.DVR

variable {𝕜 W : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup W] [Module 𝕜 W]

def qf (B : LinearMap.BilinForm 𝕜 W) (w : W) : 𝕜 := B w w / 2

variable {B : LinearMap.BilinForm 𝕜 W}

end ReciprocityTheory.ChartRestriction.G.DVR
