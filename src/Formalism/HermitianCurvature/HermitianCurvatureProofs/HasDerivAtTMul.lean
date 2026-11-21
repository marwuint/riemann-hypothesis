import Mathlib

open Set Filter Topology MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}

def prim (ω : ℂ → ℂ →L[ℝ] ℝ) (w₀ w : ℂ) : ℝ := ∫ t in (0 : ℝ)..1, ω (w₀ + (t : ℂ) * (w - w₀)) (w - w₀)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
