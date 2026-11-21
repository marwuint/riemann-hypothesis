import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSympl
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable
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

theorem continuous_ellAdd (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T)
    (hL : Continuous L) (x : WO S T) : Continuous (ellAdd Λ L x) := by
  have hs : Continuous fun t => symplOH S T x (L t) := (continuous_symplOH_right x).comp hL
  have h1 : Continuous fun t => Λ (symplOH S T x (L t)).1 := hΛ.comp (continuous_fst.comp hs)
  exact h1

def ellx (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T) (hL : Continuous L)
    (x : WO S T) : (Fin k → ℝ) →L[ℝ] ℂ :=
  AddMonoidHom.toRealLinearMap (ellAdd Λ L x) (continuous_ellAdd Λ hΛ L hL x)

theorem ellx_apply (Λ : Ainf D.host.F →+ ℂ) (hΛ : Continuous Λ) (L : (Fin k → ℝ) →+ WO S T) (hL : Continuous L)
    (x : WO S T) (t : Fin k → ℝ) : ellx Λ hΛ L hL x t = Λ (symplOH S T x (L t)).1 := rfl

end Formalism.IndefR.Eqv

end
