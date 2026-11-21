import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.UnfDefs
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.BesPerSt
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def bEll (Z : HSp D) (ρ : ℕ) : Mx D ρ Z.rank :=
  fun i k => if i.1 + 1 = ρ then incA D (∑ j, Z.gram j k) else 0

def SUp (D : D7) (ρ : ℕ) : AddSubgroup (Mx D ρ ρ) where
  carrier := {N | ∀ i j, j ≤ i → N i j = 0}
  zero_mem' := by intro i j _; rfl
  add_mem' := by
    intro a b ha hb i j h
    simp [Matrix.add_apply, ha i j h, hb i j h]
  neg_mem' := by
    intro a ha i j h
    simp [Matrix.neg_apply, ha i j h]

def ratSU (D : D7) (ρ : ℕ) : AddSubgroup (SUp D ρ) := (ratMx D ρ ρ).addSubgroupOf (SUp D ρ)

end Formalism.IndefR.Mi

end
