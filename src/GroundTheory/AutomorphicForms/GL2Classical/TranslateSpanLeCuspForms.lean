import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.HeckeCosets
import GroundTheory.AutomorphicForms.GL2Classical.HeckeOperator
import GroundTheory.AutomorphicForms.GL2Classical.HeckeCommute
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Unimodular
import GroundTheory.AutomorphicForms.GL2Classical.HeckeSatake
import GroundTheory.AutomorphicForms.GL2Classical.HeckeSatakeRep

open NumberField IsDedekindDomain Matrix MeasureTheory CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm Spherical

variable {N : ℕ} [NeZero N] {k : ℤ}

end GL2Classical

end

end GroundTheory.Automorphic
