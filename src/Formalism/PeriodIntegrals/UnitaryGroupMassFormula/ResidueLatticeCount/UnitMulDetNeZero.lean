import Mathlib

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped ENNReal Classical Pointwise

noncomputable section

namespace PI.Residue

variable (K : Type) [Field K] [NumberField K]

def unitMul (u : (𝓞 K)ˣ) : mixedSpace K →ₗ[ℝ] mixedSpace K :=
  LinearMap.mulLeft ℝ (mixedEmbedding K (u : K))

theorem unitMul_apply (u : (𝓞 K)ˣ) (y : mixedSpace K) : unitMul K u y = u • y := rfl

end PI.Residue
