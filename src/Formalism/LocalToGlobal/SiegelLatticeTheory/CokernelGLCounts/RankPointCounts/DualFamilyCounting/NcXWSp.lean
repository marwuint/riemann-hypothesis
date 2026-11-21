import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.NcX.LT

namespace WSp

section Lin

variable {K : Type*} [Field K] {n : ℕ}

def dl (u : Fin n → K) : Module.Dual K (Fin n → K) where
  toFun w := u ⬝ᵥ w
  map_add' x y := dotProduct_add u x y
  map_smul' c x := by simp [dotProduct_smul]

theorem dl_apply (u w : Fin n → K) : dl u w = u ⬝ᵥ w := rfl

end Lin

end WSp

end Formalism.L2.SG.Pf.NcX.LT
