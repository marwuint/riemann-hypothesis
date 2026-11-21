import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobDer

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ} {ψ : AddChar (AF D.host.F) ℂ}

instance instTAGWO : IsTopologicalAddGroup (WO S T) := PHeisFC.tagWA T S

end Formalism.IndefR.Eqv

end
