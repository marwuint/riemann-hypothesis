import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

@[simp]
lemma pullbackIsoAlong_refl {T Y Z : Scheme.{0}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}
    (e : g ≫ h = k) (F : Z.Modules) :
    pullbackIsoAlong e (Iso.refl ((Scheme.Modules.pullback h).obj F)) = Iso.refl _ := by
  ext1
  simp [pullbackIsoAlong]

end

end GroundTheory.Heights₂.Heights.Model
