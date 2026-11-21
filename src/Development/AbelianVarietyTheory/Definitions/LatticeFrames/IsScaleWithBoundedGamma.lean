import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.Core.Rk

def BigGap (D : D7) : Prop := D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6)

def IsScaleWithBoundedGamma (D : D7) (L C' : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ 8 * large₂.CGam ≤ C' ∧ 1 ≤ large₂.CGam

theorem Row.mono {E E' : D7 → ℝ → ℝ → Prop} (hE : ∀ D L C', E' D L C' → E D L C') {Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop}
    (h : Row E Q) : Row E' Q := fun Cg cb Cu cT CT h1 h2 =>
  let ⟨C, a, b, hC, h⟩ := h Cg cb Cu cT CT h1 h2
  ⟨C, a, b, hC, fun C' Cl ha hb D L u hD he hH => h C' Cl ha hb D L u hD (hE _ _ _ he) hH⟩

end GlobalTheory.Core.Rk

end
