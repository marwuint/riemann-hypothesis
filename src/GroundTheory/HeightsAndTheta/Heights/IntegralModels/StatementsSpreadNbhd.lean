import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

def toOpen (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens)
    (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) : baseChange f R ⟶ (W : Scheme.{0}) :=
  IsOpenImmersion.lift W.ι (baseChangeMap f R) hW

@[reassoc (attr := simp)]
lemma toOpen_ι (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens)
    (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) :
    toOpen f R W hW ≫ W.ι = baseChangeMap f R :=
  IsOpenImmersion.lift_fac _ _ _

end

end GroundTheory.Heights₂.Heights.Model
