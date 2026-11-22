import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.IrreducibleSpan

open NumberField Matrix CongruenceSubgroup ModularForm Complex
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

local notation "𝕢₁" => Function.Periodic.qParam 1

variable {N : ℕ} [NeZero N] {k : ℤ}

end GL2Classical

end

end GroundTheory.Automorphic
