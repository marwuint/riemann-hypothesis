import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitCentral

theorem hfin {D : D7} {V : HSp D} (g : GA D V) :
    finMat D.sp.cm.sig V.gram g = (Formalism.L2.Theta.mt V g).map (finPart D) := rfl

end GlobalTheory.SplitCentral
