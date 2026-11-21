import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def invDiff (F : Type) [Field F] [NumberField F] : Set F :=
  {d | ∀ y : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F (d * (y : F)) = z}

end Formalism.IndefR.Fin

end
