import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.SobolevMollifier

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Translation

variable (F) in

def translate (h : E) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.compSubConstCLM ℂ (-h))

theorem translate_apply_apply (h : E) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    translate F h u φ = u (SchwartzMap.compSubConstCLM ℂ (-h) φ) := rfl

end Translation

namespace SobolevSpace

end SobolevSpace

end

end GroundTheory.Automorphic.Sobolev
