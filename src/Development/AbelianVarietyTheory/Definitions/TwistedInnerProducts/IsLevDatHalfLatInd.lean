import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField

set_option autoImplicit false

noncomputable section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.NX
open scoped TensorProduct
open Classical

namespace GlobalTheory.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

export GlobalTheory.TowerCov (IsLevN LevN modN)

end GlobalTheory.Tow

end

end
