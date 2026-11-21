import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

namespace FreeSheafBasis

variable (Y : Scheme.{u}) (n : ℕ)

variable {Y} in

def evalHom {M N : Y.Modules} (V : Y.Opens) (x : Γ(M, V)) : (M ⟶ N) →+ Γ(N, V) where
  toFun φ := (φ.app V).hom x
  map_zero' := rfl
  map_add' _ _ := rfl

variable {Y} in
lemma evalHom_apply {M N : Y.Modules} (V : Y.Opens) (x : Γ(M, V)) (φ : M ⟶ N) :
    evalHom V x φ = (φ.app V).hom x := rfl

variable {Y n}

end FreeSheafBasis

end

end GroundTheory.Heights₂.Heights.Model
