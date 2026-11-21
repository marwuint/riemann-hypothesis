import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.HeckeSatake
import GroundTheory.AutomorphicForms.HeckeIrreducible

open NumberField IsDedekindDomain Matrix MeasureTheory CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm ValuativeRel Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm Spherical Iwasawa GLnLocal HeckeAlgebra

variable (p : ℕ) [hp : Fact p.Prime]

def translateSpan (φ : AdelicGL ℚ 2 → ℂ) : Submodule ℂ (AdelicGL ℚ 2 → ℂ) :=
  Submodule.span ℂ (Set.range fun g : FiniteAdelicGL ℚ 2 => finRightRep g φ)

variable {N : ℕ} [NeZero N] [MeasurableSpace (GL (Fin 2) (Qp p))] [BorelSpace (GL (Fin 2) (Qp p))]
  (μ : Measure (GL (Fin 2) (Qp p))) [μ.IsHaarMeasure]

end GL2Classical

end

end GroundTheory.Automorphic
