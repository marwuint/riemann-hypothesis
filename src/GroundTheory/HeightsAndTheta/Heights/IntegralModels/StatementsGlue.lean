import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

section Inhabitants

lemma mem_invOpen_id (m : ℤ) (x : SpecZ) : x ∈ invOpen (𝟙 SpecZ) m ↔ m ∉ x.asIdeal := Iff.rfl

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Model
