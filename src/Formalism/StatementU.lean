import Formalism.StatementOC

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def Gzbar (x : ℝ) : ℝ := ∫ u in (1 : ℝ)..2, u * Gz (x / u)

def GzLipschitz : Prop :=
  ∃ K : ℝ, ∀ t t' : ℝ, 1 / 2 ≤ t → 1 / 2 ≤ t' → |Gz t| ≤ K * t ∧ |Gz t - Gz t'| ≤ K * |t - t'|

end Formalism
