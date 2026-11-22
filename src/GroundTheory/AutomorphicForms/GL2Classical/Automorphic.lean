import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.ZFinite
import GroundTheory.AutomorphicForms.GL2Classical.CuspConverse
import GroundTheory.AutomorphicForms.GL2Classical.GrowthReduction

open NumberField Matrix CongruenceSubgroup ModularForm
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

variable {N : ℕ} [NeZero N] {k : ℤ}

end GL2Classical

end

end GroundTheory.Automorphic
