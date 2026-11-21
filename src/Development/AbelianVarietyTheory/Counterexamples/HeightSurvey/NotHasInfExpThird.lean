import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.VolHeckeCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isVolMeasG_const (D : D7) (W : HSp D) (P Q : ℕ) (μ : Measure (GA D W)) :
    IsVolMeasG D W (fun _ => P) (fun _ => Q) μ ↔ IsVolMeas D W P Q μ := Iff.rfl

theorem gq_smul (D : D7) (W : HSp D) (γ : GQ W) (g : GA D W) : γ • g = (γ : GA D W) * g := rfl

theorem top_AE (D : D7) : (inferInstance : TopologicalSpace (AE D)) = moduleTopology (AF D.host.F) (AE D) := rfl

theorem isWittLower_self (D : D7) (V : HSp D) : IsWittLower V V 0 := by
  refine ⟨rfl, LinearMap.id, fun _ _ => rfl, 0, ⟨linearIndependent_empty_type, ?_⟩, ?_⟩
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

end GlobalTheory.VolHeckeCheck

end
