import Mathlib
import GroundTheory.AutomorphicForms.DefiniteClassNumber.Reduction

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix Submodule
open scoped RealInnerProductSpace

variable {J : Type*} [Fintype J]

def GramSpace (_G : Matrix J J ℝ) : Type _ := J → ℝ

instance (G : Matrix J J ℝ) : AddCommGroup (GramSpace G) := inferInstanceAs (AddCommGroup (J → ℝ))

instance (G : Matrix J J ℝ) : Module ℝ (GramSpace G) := inferInstanceAs (Module ℝ (J → ℝ))

instance (G : Matrix J J ℝ) : FiniteDimensional ℝ (GramSpace G) :=
  inferInstanceAs (FiniteDimensional ℝ (J → ℝ))

end GroundTheory.Automorphic
