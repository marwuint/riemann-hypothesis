import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedLem
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def PhiM (m n : ℕ) (x : Mx D m n) : Fin m → Fin n → Fin (nE D) → AF D.host.F :=
  fun i j => cE D.host.F D.host.E (x i j)

theorem cont_PhiM (m n : ℕ) (i j k) : Continuous fun x : Mx D m n => PhiM m n x i j k :=
  (continuous_apply k).comp ((cE D.host.F D.host.E).continuous.comp (continuous_id.matrix_elem i j))

instance lcMx (m n : ℕ) : LocallyCompactSpace (Mx D m n) :=
  inferInstanceAs (LocallyCompactSpace (Fin m → Fin n → AE D))

end Formalism.IndefR.Eqv

end
