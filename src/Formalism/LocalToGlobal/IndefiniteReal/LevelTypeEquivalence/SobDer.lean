import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSympl
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IterEqOfRange

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

def Gf (ψ : AddChar (AF D.host.F) ℂ) (L : (Fin k → ℝ) →+ WO S T) (f : WO S T → ℂ) (x : WO S T) :
    (Fin k → ℝ) → ℂ := fun t => heisO ψ S T (L t) f x

def ellAdd (Λ : Ainf D.host.F →+ ℂ) (L : (Fin k → ℝ) →+ WO S T) (x : WO S T) : (Fin k → ℝ) →+ ℂ :=
  AddMonoidHom.mk' (fun t => Λ (symplOH S T x (L t)).1) (fun t t' => by
    simp only [map_add, symplOH_add_right]
    exact Λ.map_add _ _)

end Formalism.IndefR.Eqv

end
