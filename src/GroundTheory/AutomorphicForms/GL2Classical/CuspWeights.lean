import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.EigenformTranslates
import GroundTheory.AutomorphicForms.GL2Classical.WeightOperators

open NumberField Matrix CongruenceSubgroup ModularForm Complex
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

attribute [local instance 100] LieRing.ofAssociativeRing

def raiseMat : Matrix (Fin 2) (Fin 2) ℂ := !![-I, 1; 1, I]

def lowerMat : Matrix (Fin 2) (Fin 2) ℂ := !![I, 1; 1, -I]

def rotMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

def cuspOp (B : Matrix (Fin 2) (Fin 2) ℂ) : Module.End ℂ (cuspForms ℚ 2) :=
  (gkModuleCusp ℚ 2).ρ (lieOfRealMat (reMat B)) + I • (gkModuleCusp ℚ 2).ρ (lieOfRealMat (imMat B))

variable {N : ℕ} [NeZero N] {k : ℤ}

abbrev kMat (x : archCompact ℚ 2) : GL (Fin 2) ℝ := archToReal (x : archGroup ℚ 2)

abbrev epsC : Matrix (Fin 2) (Fin 2) ℂ := (toReal epsilon : Matrix (Fin 2) (Fin 2) ℝ).map (↑)

end GL2Classical

end

end GroundTheory.Automorphic
