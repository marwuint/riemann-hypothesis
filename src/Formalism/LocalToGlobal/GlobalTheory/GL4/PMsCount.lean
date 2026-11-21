import Formalism.LocalToGlobal.GlobalTheory.GL4.PMsFrame

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Count

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def msLat (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (2 * D.R.f * Real.log (C₀ * (C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2))) +
    4 * D.R.f * n * ((n : ℝ) + 1) * (Real.log (C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2) / 2)

theorem msBound_eq (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (n : ℕ) :
    msBound D u C₀ n = msLat D u C₀ n +
      2 * D.R.f * (n : ℝ) ^ 2 * (Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) := rfl

end Count

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
