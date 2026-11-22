import Formalism.StatementOC

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def GzLipschitz : Prop :=
  ∃ K : ℝ, ∀ t t' : ℝ, 1 / 2 ≤ t → 1 / 2 ≤ t' → |Gz t| ≤ K * t ∧ |Gz t - Gz t'| ≤ K * |t - t'|

end Formalism
