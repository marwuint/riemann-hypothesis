import Mathlib
import GroundTheory.AutomorphicForms.AnisotropicRestrict
import GroundTheory.AutomorphicForms.AnisotropicHeight
set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable {K : Type*} [Field K] {κ : Type*} [Fintype κ] [DecidableEq κ]

section General

variable {A : Type*} [Ring A] [Algebra K A] (b : Basis κ K A)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']

variable {R}

variable (R)

variable {R}

end General

section Division

variable [NumberField K] {D : Type*} [DivisionRing D] [Algebra K D] {d : ℕ} (b : Basis (Fin d) K D)

end Division

end Anisotropic

end

end GroundTheory.Automorphic
